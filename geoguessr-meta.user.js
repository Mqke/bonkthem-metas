// ==UserScript==
// @name         BetterMetas
// @namespace    http://tampermonkey.net/
// @version      0.13
// @description  Displays crowdsourced metas and hints for Geoguessr locations.
// @author       Lukas Hzb
// @match        https://www.geoguessr.com/*
// @icon         https://www.google.com/s2/favicons?sz=64&domain=geoguessr.com
// @run-at       document-start
// @grant        GM_xmlhttpRequest
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        unsafeWindow
// @connect      localhost
// @connect      *
// ==/UserScript==

(function() {
    'use strict';


    const SHOW_LOCATION_HUD = false;
    const DEBUG_LOGGING = false;

    // Data Sources
    const USER_LOCATIONS_FILE = 'data/user_locations.json';
    const USER_METAS_FILE = 'data/user_metas.json';

    const getRawFileUrl = (file) => `http://localhost:3000/${file}`;

    function debugLog(...args) {
        if (DEBUG_LOGGING) console.log(...args);
    }

    const win = (typeof unsafeWindow !== 'undefined') ? unsafeWindow : window;
    const HUD_SIZE_STORAGE_KEY = 'gg_hud_size';
    const HUD_POSITION_STORAGE_KEY = 'gg_hud_position';
    const PENDING_LOCAL_CHANGES_STORAGE_KEY = 'gg_pending_local_changes';
    const DATA_CACHE_STORAGE_KEY = 'gg_data_cache';
    const DATA_CACHE_VERSION = 'local:7';
    const ACTIVE_SCOPES_STORAGE_KEY = 'gg_active_scopes';
    const ACTIVE_TAGS_STORAGE_KEY = 'gg_active_tags';
    const HUD_MIN_WIDTH = 260;
    const HUD_MIN_HEIGHT = 220;
    const DATA_REFRESH_AFTER_SAVE_MS = 2500;
    const SAVE_COMPLETE_RESET_MS = 1000;
    const DATA_FETCH_TIMEOUT_MS = 8000;
    const LOCAL_WRITE_TIMEOUT_MS = 15000;
    const DATA_FETCH_MAX_ATTEMPTS = 3;
    const DATA_FETCH_RETRY_DELAY_MS = 400;
    const DATA_CACHE_MAX_AGE_MS = 12 * 60 * 60 * 1000;
    const STREETVIEW_RETRY_DELAY_MS = 500;
    const RESULT_SCREEN_GRACE_MS = 500;
    const QUEUED_PANO_FORCE_MS = 2000;
    const VISIBILITY_POLL_INTERVAL_MS = 200;
    const HOOK_POLL_MIN_DELAY_MS = 25;
    const HOOK_POLL_MAX_DELAY_MS = 1000;
    const MISSING_PANOID_PLACEHOLDER = "YOUR_PANOID_HERE";
    const META_SAVE_BUTTON_LABEL = 'Save Meta';
    const SEARCH_DEBOUNCE_MS = 120;
    const META_LIST_PAGE_SIZE = 120;
    const HUD_IMAGE_PRELOAD_MARGIN_PX = 800;

    /**
     * @typedef {Object} Meta
     * @property {string} id
     * @property {string} title
     * @property {string} description
     * @property {string} [scope]
     * @property {string[]} [tags]
     * @property {number} [lat]
     * @property {number} [lng]
     */

    let userLocationMap = {};
    let proximityIndexDirty = true;
    let proximityIndexVersion = 0;
    let metaRenderVersion = 0;
    let lastProximityCacheKey = null;
    let lastProximityMatches = [];
    let indexedLocationEntries = [];
    let indexedSegments = [];

    /** @type {Meta[]} Loaded meta definitions */
    let metasData = [];
    let metaById = new Map();
    let metaSearchTextById = null;
    const incrementalListStates = new WeakMap();
    const metaListInteractionStates = new WeakMap();
    let userMetaIds = new Set();
    let dataLoadSequence = 0;
    let hudImageObserver = null;
    let lastHudRenderKey = null;
    let uiInitialized = false;

    function normalizeMetaIds(value) {
        return Array.isArray(value)
            ? value.filter(id => typeof id === 'string' && id.trim())
            : [];
    }

    function getLocationMetaIds(entry) {
        if (!entry) return [];
        if (Array.isArray(entry)) return normalizeMetaIds(entry);
        return normalizeMetaIds(entry.metas);
    }

    function normalizeCoordinate(value) {
        if (value === null || value === undefined || value === '') return null;
        if (typeof value !== 'number' && typeof value !== 'string') return null;
        const parsed = Number(value);
        return Number.isFinite(parsed) ? parsed : null;
    }

    function normalizeLocationEntry(entry) {
        if (!entry) return null;

        const normalized = Array.isArray(entry)
            ? { metas: getLocationMetaIds(entry) }
            : (typeof entry === 'object' ? { ...entry, metas: getLocationMetaIds(entry) } : null);
        if (!normalized) return null;

        normalized.lat = normalizeCoordinate(normalized.lat);
        normalized.lng = normalizeCoordinate(normalized.lng);
        ['country', 'nominatimCountry', 'region', 'city', 'road'].forEach(field => {
            if (!Object.prototype.hasOwnProperty.call(normalized, field)) {
                normalized[field] = null;
            }
        });

        // Segment entry: point A is lat/lng, point B is latB/lngB (both null while B is not
        // linked yet) and `road` is a list.
        if (normalized.segment) {
            normalized.road = getSegmentRoadList(normalized.road);
            normalized.latB = normalizeCoordinate(normalized.latB);
            normalized.lngB = normalizeCoordinate(normalized.lngB);
            if (normalized.latB === null || normalized.lngB === null) {
                normalized.latB = null;
                normalized.lngB = null;
            }
        }
        return normalized;
    }

    function getCurrentLocationSnapshot() {
        return {
            lat: normalizeCoordinate(currentLocationData.lat),
            lng: normalizeCoordinate(currentLocationData.lng),
            country: currentLocationData.country || null,
            nominatimCountry: currentLocationData.nominatimCountry || null,
            region: currentLocationData.region || null,
            city: currentLocationData.city || null,
            road: currentLocationData.road || null
        };
    }

    // Mandatory fields always stored on every location entry.
    // region/city/road are always present as null so the nodes exist in the JSON;
    // addMetaIdsToLocationMap fills in the relevant one based on the meta's scope.
    function getMandatoryLocationSnapshot() {
        return {
            lat: normalizeCoordinate(currentLocationData.lat),
            lng: normalizeCoordinate(currentLocationData.lng),
            country: currentLocationData.country || null,
            nominatimCountry: currentLocationData.nominatimCountry || null,
            region: null,
            city: null,
            road: null
        };
    }

    // Returns mandatory fields plus the field relevant to the given scope:
    //   region -> region
    //   city -> region + city (region needed to disambiguate same-named cities)
    //   road -> road
    // Other scopes (countrywide, 100km, 10km, 1km, unique) get only mandatory fields.
    // The scope-relevant keys are always present (null if unavailable).
    function getLocationSnapshotForScope(scope) {
        const normalizedScope = normalizeScope(scope);
        const snapshot = getMandatoryLocationSnapshot();

        if (normalizedScope === 'region') {
            snapshot.region = currentLocationData.region || null;
        } else if (normalizedScope === 'city') {
            snapshot.region = currentLocationData.region || null;
            snapshot.city = currentLocationData.city || null;
        } else if (normalizedScope === 'road') {
            // Whole road: the highway code (E20), not the name of one stretch of it.
            snapshot.road = chooseRoadRef(currentLocationData.roadSources) || currentLocationData.road || null;
        } else if (normalizedScope === 'segment') {
            // A segment stores a LIST of roads; this location's road is the first one.
            snapshot.road = getSegmentRoadList(chooseRoadRef(currentLocationData.roadSources) || currentLocationData.road);
            snapshot.latB = null;
            snapshot.lngB = null;
            snapshot.segment = true;
        }

        return snapshot;
    }

    // ---- Road name selection -------------------------------------------------------
    // Each geocoder source gives { names: [...], refs: [...] }. A "ref" (E20, N7, SP 12)
    // identifies a whole highway, not a precise stretch, so it is only a last resort.
    // A value is a ref when a source says so (OSM ref / int_ref tag, Google short_name
    // different from long_name) or, failing that, when it looks like a bare road code.
    function newRoadSources() {
        return { google: { names: [], refs: [] }, nominatim: { names: [], refs: [] } };
    }

    function normalizeRoadKey(value) {
        return stripDiacritics(String(value || '')).toLowerCase().replace(/\s+/g, ' ').trim();
    }

    function getKnownRoadRefs(roadSources) {
        const known = new Set();
        ['google', 'nominatim'].forEach(src => {
            ((roadSources && roadSources[src] && roadSources[src].refs) || []).forEach(r => {
                const k = normalizeRoadKey(r);
                if (k) known.add(k);
            });
        });
        return known;
    }

    // "E20", "N7", "SP 12", "A-1": a bare road code.
    const ROAD_CODE_RE = /^[a-z]{0,3}[\s-]?\d{1,4}[a-z]?$/i;

    function isRoadCode(value) {
        return ROAD_CODE_RE.test(String(value || '').trim());
    }

    function isRoadRefLike(name, knownRefs) {
        const k = normalizeRoadKey(name);
        if (!k) return false;
        if (knownRefs && knownRefs.has(k)) return true;
        return isRoadCode(k);
    }

    function pickRoadName(source, knownRefs) {
        const names = ((source && source.names) || []).map(n => String(n || '').trim()).filter(Boolean);
        return names.find(n => !isRoadRefLike(n, knownRefs)) || null;
    }

    // One road per location. A real name beats a ref; when both sources have a real name,
    // Google's is kept (it is the label shown on Google Maps). A ref is used only if
    // neither source has a real name.
    function chooseRoad(roadSources) {
        const known = getKnownRoadRefs(roadSources);
        const g = pickRoadName(roadSources && roadSources.google, known);
        if (g) return g;
        const n = pickRoadName(roadSources && roadSources.nominatim, known);
        if (n) return n;
        for (const src of ['google', 'nominatim']) {
            const source = (roadSources && roadSources[src]) || {};
            const any = (source.refs || [])[0] || (source.names || [])[0];
            if (any) return String(any).trim();
        }
        return null;
    }

    // Road for a "segment" scope: the highway code (E20) is wanted, not the local name of
    // the stretch. OSM ref tags are the most reliable, then Google short names that look
    // like a code, then any ref, then the usual name.
    function chooseRoadRef(roadSources) {
        const refs = [
            ...(((roadSources && roadSources.nominatim) || {}).refs || []),
            ...(((roadSources && roadSources.google) || {}).refs || [])
        ].map(r => String(r || '').trim()).filter(Boolean);
        return refs.find(isRoadCode) || refs[0] || chooseRoad(roadSources);
    }

    // Roads identifying the current location for the "road" scope: the highway code (E20)
    // first, then every other name/ref the geocoders gave, so entries stored earlier under
    // the name of a stretch ("via aloag santo domingo") still match.
    function getRoadScopeNames() {
        const names = [];
        const add = v => {
            const k = String(v || '').toLowerCase().trim();
            if (k && !names.includes(k)) names.push(k);
        };
        add(chooseRoadRef(currentLocationData.roadSources));
        add(currentLocationData.road);
        getRoadCandidateKeys(currentLocationData.roadSources).forEach(add);
        return names;
    }

    // Every name and ref the geocoders gave for the current road, normalized.
    function getRoadCandidateKeys(roadSources) {
        const keys = new Set();
        ['google', 'nominatim'].forEach(src => {
            const source = (roadSources && roadSources[src]) || {};
            [...(source.names || []), ...(source.refs || [])].forEach(v => {
                const k = normalizeRoadKey(v);
                if (k) keys.add(k);
            });
        });
        return Array.from(keys);
    }

    // Region / city: one raw value per source. Nominatim has priority (its language is
    // fixed to English, so a place always gets the same name), Google is the fallback.
    function newPlaceSources() {
        return { google: { region: null, city: null }, nominatim: { region: null, city: null } };
    }

    function applyPlaceNames() {
        const src = currentLocationData.placeSources || newPlaceSources();
        currentLocationData.region = src.nominatim.region || src.google.region || null;
        // City: Google's "locality" is the real city (Quito); Nominatim's town/village is often
        // just a neighbourhood (Carapungo), so it is only the fallback.
        currentLocationData.city = src.google.city || src.nominatim.city || null;
    }

    // Google route component: short_name differing from long_name is the road code (E20).
    function addGoogleRouteComponent(target, comp) {
        const long = String(comp.long_name || '').trim();
        const short = String(comp.short_name || '').trim();
        if (long) target.names.push(long);
        if (short && short !== long) target.refs.push(short);
    }

    // Region / city come from Nominatim first, so wait for it (or for both sources).
    async function waitForPlaceGeocoding(timeoutMs = 10000) {
        const deadline = Date.now() + timeoutMs;
        let announced = false;
        while (true) {
            const done = currentLocationData.geocodeDone || {};
            if (done.nominatim) return true;
            if (Date.now() >= deadline) return false;
            if (!announced) {
                announced = true;
                updateStatus('Waiting for location geocoding...');
            }
            await new Promise(resolve => setTimeout(resolve, 150));
        }
    }

    // Waits for the geocoding the given scope depends on (road / region / city).
    async function waitForScopeGeocoding(scope) {
        const normalized = normalizeScope(scope);
        if (normalized === 'road' || normalized === 'segment') return waitForRoadGeocoding();
        if (normalized === 'region' || normalized === 'city') return waitForPlaceGeocoding();
        return true;
    }

    function markGeocodeDone(source, latStr, lngStr) {
        if (currentLocationData.lat !== latStr || currentLocationData.lng !== lngStr) return;
        currentLocationData.geocodeDone = currentLocationData.geocodeDone || { google: false, nominatim: false };
        currentLocationData.geocodeDone[source] = true;
    }

    // Waits (up to timeoutMs) until the road of the current location is final: both
    // geocoders answered, or Google already gave a highway code (E20).
    // Returns true when final, false on timeout (the link then uses what is known).
    async function waitForRoadGeocoding(timeoutMs = 10000) {
        const deadline = Date.now() + timeoutMs;
        let announced = false;
        while (true) {
            const done = currentLocationData.geocodeDone || {};
            const sources = currentLocationData.roadSources;
            const googleRefs = ((sources && sources.google && sources.google.refs) || []);
            const googleHasRef = googleRefs.some(isRoadCode);
            if ((done.google && done.nominatim) || (done.google && googleHasRef)) return true;
            if (Date.now() >= deadline) return false;
            if (!announced) {
                announced = true;
                updateStatus('Waiting for road geocoding...');
            }
            await new Promise(resolve => setTimeout(resolve, 150));
        }
    }

    function getNormalizedRoadNames(value) {
        const values = Array.isArray(value) ? value : [value];
        return values
            .map(road => String(road || '').toLowerCase().trim())
            .filter(Boolean);
    }

    function mergeLocationEntries(baseEntry, overrideEntry) {
        if (!baseEntry) return normalizeLocationEntry(overrideEntry);
        if (!overrideEntry) return normalizeLocationEntry(baseEntry);

        const baseEntryMetaIds = getLocationMetaIds(baseEntry);
        const overrideEntryMetaIds = getLocationMetaIds(overrideEntry);
        const mergedMetaIds = Array.from(new Set([...baseEntryMetaIds, ...overrideEntryMetaIds]));

        const baseData = Array.isArray(baseEntry) ? { metas: baseEntryMetaIds } : { ...baseEntry };
        const overrideData = Array.isArray(overrideEntry) ? { metas: overrideEntryMetaIds } : { ...overrideEntry };
        return normalizeLocationEntry({ ...baseData, ...overrideData, metas: mergedMetaIds });
    }

    function ensureLocationEntry(locations, panoid) {
        if (!locations[panoid]) {
            const locationSnapshot = getMandatoryLocationSnapshot();
            locations[panoid] = {
                metas: [],
                ...locationSnapshot
            };
        } else if (Array.isArray(locations[panoid])) {
            const locationSnapshot = getMandatoryLocationSnapshot();
            locations[panoid] = {
                metas: getLocationMetaIds(locations[panoid]),
                ...locationSnapshot
            };
        } else {
            locations[panoid] = normalizeLocationEntry(locations[panoid]) || {
                metas: [],
                ...getMandatoryLocationSnapshot()
            };
        }

        // Ensure mandatory fields are filled on existing entries that may
        // have been created by an older version without them.
        const entry = locations[panoid];
        const mandatory = getMandatoryLocationSnapshot();
        if (entry.lat == null) entry.lat = mandatory.lat;
        if (entry.lng == null) entry.lng = mandatory.lng;
        if (entry.country == null) entry.country = mandatory.country;
        if (entry.nominatimCountry == null) entry.nominatimCountry = mandatory.nominatimCountry;

        return entry;
    }

    // Two names are "the same" when both are empty or when they match (accent/case-insensitive).
    function isSameNullableName(a, b) {
        if (!a && !b) return true;
        return isSameName(a, b);
    }

    // Does this location entry have EXACTLY the shape required by `scope` for the
    // current location? The shape is:
    //   countrywide / 100km / 10km / 1km / unique -> region, city, road all empty
    //   region -> same region, no city, no road
    //   city   -> same region + same city, no road
    //   road   -> a shared road name, no region, no city
    //   segment-> like road but flagged `segment: true`, with a LIST of roads and the two
    //             corners of the stretch: lat/lng (A) and latB/lngB (B). One entry holds
    //             one meta (see findSegmentLinkKey / evaluateProximityMetas)
    // Because the shape is exact, an entry created for one scope is never reused
    // (and therefore never "upgraded" with extra fields) by a meta of another scope.
    function entryFitsScope(entry, scope) {
        if (!entry || typeof entry !== 'object' || Array.isArray(entry)) return false;
        const normalizedScope = normalizeScope(scope);
        const entryRoads = getNormalizedRoadNames(entry.road);
        const hasRoad = entryRoads.length > 0;

        if (normalizedScope === 'segment') {
            // Shape only: which segment entry a meta joins is decided by findSegmentLinkKey.
            return !!entry.segment && !entry.region && !entry.city && hasRoad;
        }
        if (entry.segment) return false;

        if (normalizedScope === 'region') {
            return isSameNullableName(entry.region, currentLocationData.region) &&
                !entry.city && !hasRoad;
        }
        if (normalizedScope === 'city') {
            return isSameNullableName(entry.region, currentLocationData.region) &&
                isSameNullableName(entry.city, currentLocationData.city) && !hasRoad;
        }
        if (normalizedScope === 'road') {
            const curRoads = getRoadScopeNames();
            return !entry.region && !entry.city && hasRoad && curRoads.length > 0 &&
                curRoads.some(cr => entryRoads.some(er => isSameName(cr, er)));
        }
        // countrywide, 100km, 10km, 1km, unique
        return !entry.region && !entry.city && !hasRoad;
    }

    // For name-based scopes (countrywide, region, city, road), find an existing
    // location entry (any panoid) that has the same country and EXACTLY the shape
    // of the scope (see entryFitsScope). Returns the key, or null if there is none
    // or the scope is distance-based/unique.
    function findMatchingLocationKey(locations, scope) {
        const normalizedScope = normalizeScope(scope);
        if (!['countrywide', 'region', 'city', 'road'].includes(normalizedScope)) return null;

        const curLat = normalizeCoordinate(currentLocationData.lat);
        const curLng = normalizeCoordinate(currentLocationData.lng);
        const curCountry = normalizeCountry(currentLocationData.country, curLat, curLng);
        const curNomCountry = normalizeCountry(currentLocationData.nominatimCountry, curLat, curLng);

        for (const [key, entry] of Object.entries(locations)) {
            if (!entry || typeof entry !== 'object' || Array.isArray(entry)) continue;

            const entryCountry = normalizeCountry(entry.nominatimCountry || entry.country, entry.lat, entry.lng);
            if (entryCountry !== curCountry && entryCountry !== curNomCountry) continue;

            if (entryFitsScope(entry, normalizedScope)) return key;
        }
        return null;
    }

    // Keys of a location map are either "<panoid>" or "<panoid>__<scope>" (a second,
    // third... entry created for the same panoid because it needs a different shape).
    const SCOPED_KEY_SUFFIX_RE = /^(countrywide|region|city|road|segment|100km|10km|1km|unique)(_\d+)?$/;

    function isOwnLocationKey(key, panoid) {
        if (key === panoid) return true;
        return key.startsWith(panoid + '__') && SCOPED_KEY_SUFFIX_RE.test(key.slice(panoid.length + 2));
    }

    // panoid -> its location keys ("<panoid>" and "<panoid>__<scope>[_n]"), same rule
    // as isOwnLocationKey.
    const SCOPED_KEY_RE = /^(.+)__(?:countrywide|region|city|road|segment|100km|10km|1km|unique)(?:_\d+)?$/;
    let panoidKeyIndex = new Map();

    function buildPanoidKeyIndex(locations) {
        const index = new Map();
        const add = (panoid, key) => {
            const keys = index.get(panoid);
            if (keys) keys.push(key);
            else index.set(panoid, [key]);
        };
        Object.keys(locations).forEach(key => {
            add(key, key);
            const scoped = SCOPED_KEY_RE.exec(key);
            if (scoped) add(scoped[1], key);
        });
        return index;
    }

    function getOwnLocationKeys(locations, panoid) {
        if (!locations || !panoid) return [];
        return Object.keys(locations).filter(key => isOwnLocationKey(key, panoid));
    }

    // Every meta id linked "here": in the entry of this panoid or in any of the
    // "<panoid>__<scope>" entries created for it.
    function getLinkedMetaIdsForPanoid(locations, panoid) {
        const ids = new Set();
        // Display paths read the live map through the per-panoid key index instead of
        // scanning every key. The index shares the proximity indexes' invalidation
        // (proximityIndexDirty, set after every change of userLocationMap).
        let keys;
        if (panoid && locations === userLocationMap) {
            if (proximityIndexDirty) rebuildProximityIndexes();
            keys = panoidKeyIndex.get(panoid) || [];
        } else {
            keys = getOwnLocationKeys(locations, panoid);
        }
        keys.forEach(key => {
            getLocationMetaIds(locations[key]).forEach(id => ids.add(id));
        });
        return ids;
    }

    // Picks the key where a meta of `scope` must be stored when no matching entry
    // exists elsewhere: reuse an entry of this panoid that has the right shape,
    // otherwise create a NEW entry ("<panoid>" if free, else "<panoid>__<scope>").
    function resolveKeyForNewLink(locations, panoid, scope) {
        const normalizedScope = normalizeScope(scope);
        // A segment entry belongs to ONE meta (its rectangle is part of the entry), so an
        // existing entry is never reused for a new segment link.
        const ownKey = normalizedScope === 'segment' ? null : getOwnLocationKeys(locations, panoid)
            .find(key => entryFitsScope(locations[key], normalizedScope));
        if (ownKey) return ownKey;

        if (!locations[panoid]) return panoid;

        const baseKey = `${panoid}__${normalizedScope}`;
        let candidate = baseKey;
        let counter = 2;
        while (locations[candidate]) {
            candidate = `${baseKey}_${counter++}`;
        }
        return candidate;
    }

    // Adds the meta ids to the location map and returns a Map(metaId -> key used).
    // `forcedKeys` (Map metaId -> key) skips the key resolution, so the same
    // decision can be replayed on another map.
    function addMetaIdsToLocationMap(locations, panoid, metaIds, scopeOverride = null, forcedKeys = null) {
        const usedKeys = new Map();

        metaIds.forEach(id => {
            // Determine the scope for this meta.
            // scopeOverride takes priority (e.g. unsaved admin form scope);
            // otherwise look up the meta's scope from the in-memory index.
            const scope = scopeOverride || (() => {
                const meta = getMetaById(id);
                return meta ? meta.scope : null;
            })();

            // 1. an existing entry (of any panoid) that already has the exact shape
            //    of the scope is reused;
            // 2. otherwise an entry of this panoid with the exact shape is reused;
            // 3. otherwise a new entry is created. An existing entry with another
            //    shape is NEVER reused, or it would be modified for its other metas.
            let targetKey = forcedKeys && forcedKeys.get(id);
            if (!targetKey) {
                if (scope) {
                    targetKey = (normalizeScope(scope) === 'segment'
                        ? findSegmentLinkKey(locations, id)
                        : findMatchingLocationKey(locations, scope)) ||
                        resolveKeyForNewLink(locations, panoid, scope);
                } else {
                    targetKey = panoid;
                }
            }

            const entry = ensureLocationEntry(locations, targetKey);
            if (!entry.metas.includes(id)) {
                entry.metas.push(id);
            }

            // Fill scope-relevant location fields (only ever happens on a new entry,
            // as reused entries already have these fields).
            if (scope) {
                const scopedSnapshot = getLocationSnapshotForScope(scope);
                if ('region' in scopedSnapshot && !entry.region) entry.region = scopedSnapshot.region;
                if ('city' in scopedSnapshot && !entry.city) entry.city = scopedSnapshot.city;
                if (scopedSnapshot.segment) {
                    applyCurrentLocationToSegmentEntry(entry, scopedSnapshot.road);
                    debugLog('[BetterMetas] Segment link:', {
                        meta: id,
                        key: targetKey,
                        pointA: [entry.lat, entry.lng],
                        pointB: [entry.latB, entry.lngB],
                        roads: entry.road
                    });
                } else if ('road' in scopedSnapshot && !entry.road) {
                    entry.road = scopedSnapshot.road;
                }
            }

            usedKeys.set(id, targetKey);
        });

        return usedKeys;
    }

    // Removes the meta ids from ONE exact entry (used when the entry key is known,
    // e.g. the admin "linked locations" list).
    function removeMetaIdsFromLocationMap(locations, panoid, metaIds) {
        if (!locations || !locations[panoid]) return;

        const idsToRemove = new Set(metaIds);
        const entry = ensureLocationEntry(locations, panoid);
        entry.metas = entry.metas.filter(id => !idsToRemove.has(id));

        if (entry.metas.length === 0) {
            delete locations[panoid];
        }
    }

    // Removes the meta ids from every entry linked to this panoid
    // ("<panoid>" and "<panoid>__<scope>").
    function removeMetaIdsFromPanoidLocations(locations, panoid, metaIds) {
        getOwnLocationKeys(locations, panoid).forEach(key => {
            removeMetaIdsFromLocationMap(locations, key, metaIds);
        });
    }

    // Same country test as findMatchingLocationKey, for a single entry.
    function entryMatchesCurrentCountry(entry) {
        const curLat = normalizeCoordinate(currentLocationData.lat);
        const curLng = normalizeCoordinate(currentLocationData.lng);
        const curCountry = normalizeCountry(currentLocationData.country, curLat, curLng);
        const curNomCountry = normalizeCountry(currentLocationData.nominatimCountry, curLat, curLng);
        const entryCountry = normalizeCountry(entry.nominatimCountry || entry.country, entry.lat, entry.lng);
        return entryCountry === curCountry || entryCountry === curNomCountry;
    }

    // Keys of the entries that hold `metaId` and that represent the CURRENT location
    // for a meta of `scope`: the entries of this panoid, plus (for name-based scopes)
    // a shared entry of another panoid that fits the scope and the current country.
    function findLinkedKeysForCurrentLocation(locations, panoid, metaId, scope) {
        const normalizedScope = normalizeScope(scope);
        const isNameBased = ['countrywide', 'region', 'city', 'road'].includes(normalizedScope);
        return Object.keys(locations).filter(key => {
            const entry = locations[key];
            if (!getLocationMetaIds(entry).includes(metaId)) return false;
            if (isOwnLocationKey(key, panoid)) return true;
            return isNameBased && entry && typeof entry === 'object' && !Array.isArray(entry) &&
                entryMatchesCurrentCountry(entry) && entryFitsScope(entry, normalizedScope);
        });
    }

    // A meta changed scope: unlink it from the entry(ies) of its OLD scope for the
    // current location and link it again with the NEW scope, so the location gets the
    // fields of the new scope (region / city / road) from the current location.
    // Returns Map(metaId -> key used), or null if the meta was not linked here.
    function relinkMetaForScopeChange(locations, panoid, metaId, oldScope, newScope) {
        const keys = findLinkedKeysForCurrentLocation(locations, panoid, metaId, oldScope);
        if (keys.length === 0) return null;
        keys.forEach(key => removeMetaIdsFromLocationMap(locations, key, [metaId]));
        return addMetaIdsToLocationMap(locations, panoid, [metaId], newScope);
    }

    // ---- Landscape import (scopes 100km / 10km / 1km) -------------------------------
    // A landscape file (Map-Making-App style: { customCoordinates: [{ lat, lng, ... }] })
    // describes a zone. Its central location is stored as an extra location entry linked
    // to the meta, under a dedicated key so it never collides with a panoid entry.
    const LANDSCAPE_SCOPES = ['100km', '10km', '1km'];
    const LANDSCAPE_CENTER_KEY_PREFIX = 'center_';

    function isLandscapeScope(scope) {
        return LANDSCAPE_SCOPES.includes(normalizeScope(scope));
    }

    function getLandscapeCenterKey(metaId) {
        return `${LANDSCAPE_CENTER_KEY_PREFIX}${metaId}`;
    }

    function extractLandscapePoints(json) {
        const list = Array.isArray(json) ? json
            : Array.isArray(json?.customCoordinates) ? json.customCoordinates
            : Array.isArray(json?.locations) ? json.locations
            : null;
        if (!list) return [];
        return list
            .map(item => ({
                lat: normalizeCoordinate(item?.lat ?? item?.latitude),
                lng: normalizeCoordinate(item?.lng ?? item?.lon ?? item?.longitude)
            }))
            .filter(pt => pt.lat !== null && pt.lng !== null && Math.abs(pt.lat) <= 90 && Math.abs(pt.lng) <= 180);
    }

    // Geometric median (Weiszfeld): the point minimising the sum of distances to all
    // panoramas. Unlike the mean or the bounding-box centre it is not dragged away by
    // a few distant outliers. Longitude is scaled by cos(lat) so distances are ~metric.
    function computeGeometricMedian(points) {
        const count = points.length;
        if (count === 0) return null;

        const refLng = points[0].lng;
        const unwrapLng = lng => {
            let diff = lng - refLng;
            while (diff > 180) diff -= 360;
            while (diff < -180) diff += 360;
            return refLng + diff;
        };
        const meanLat = points.reduce((sum, pt) => sum + pt.lat, 0) / count;
        const k = Math.cos(meanLat * Math.PI / 180) || 1e-6;
        const xs = points.map(pt => pt.lat);
        const ys = points.map(pt => unwrapLng(pt.lng) * k);

        let x = xs.reduce((a, b) => a + b, 0) / count;
        let y = ys.reduce((a, b) => a + b, 0) / count;
        for (let iter = 0; iter < 1000; iter++) {
            let num = 0, numY = 0, den = 0;
            for (let i = 0; i < count; i++) {
                const dist = Math.max(Math.hypot(xs[i] - x, ys[i] - y), 1e-12);
                num += xs[i] / dist;
                numY += ys[i] / dist;
                den += 1 / dist;
            }
            const nextX = num / den;
            const nextY = numY / den;
            const moved = Math.hypot(nextX - x, nextY - y);
            x = nextX;
            y = nextY;
            if (moved < 1e-10) break;
        }

        let lng = y / k;
        while (lng > 180) lng -= 360;
        while (lng < -180) lng += 360;
        return { lat: Number(x.toFixed(6)), lng: Number(lng.toFixed(6)) };
    }

    // ---- Covering a landscape with several centers -----------------------------------
    // A distance scope matches every location within `radius` km of an entry (see
    // getDistanceForScope), so a zone wider than the radius needs several entries.
    // Greedy maximum coverage: repeatedly pick the center that covers the most
    // still-uncovered locations, until none is worth adding.
    const LANDSCAPE_EARTH_RADIUS_KM = 6371;
    const LANDSCAPE_MAX_CENTERS = 30;          // hard cap of entries per meta
    const LANDSCAPE_MIN_GAIN_RATIO = 0.01;     // a center must cover >= 1% of the locations
    const LANDSCAPE_MAX_SAMPLE_POINTS = 3000;  // big files are sampled (evenly, deterministic)
    const LANDSCAPE_MAX_POINT_CANDIDATES = 2000;
    const LANDSCAPE_MAX_GRID_CANDIDATES = 2000;

    function latLngToUnitVector(lat, lng) {
        const la = lat * Math.PI / 180;
        const lo = lng * Math.PI / 180;
        return [Math.cos(la) * Math.cos(lo), Math.cos(la) * Math.sin(lo), Math.sin(la)];
    }

    function sampleLandscapePoints(points, maxCount) {
        if (points.length <= maxCount) return points;
        let seed = 12345;
        const random = () => {
            seed = (seed * 1664525 + 1013904223) >>> 0;
            return seed / 4294967296;
        };
        const copy = points.slice();
        for (let i = 0; i < maxCount; i++) {
            const j = i + Math.floor(random() * (copy.length - i));
            const tmp = copy[i];
            copy[i] = copy[j];
            copy[j] = tmp;
        }
        return copy.slice(0, maxCount);
    }

    // Returns the centers ({ lat, lng }) needed to cover the landscape with discs of
    // `radiusKm`, most useful first. A single center (the geometric median) is returned
    // when it already covers the zone.
    function computeLandscapeCenters(points, radiusKm) {
        if (!points.length) return [];
        const chord2 = Math.pow(2 * Math.sin(radiusKm / (2 * LANDSCAPE_EARTH_RADIUS_KM)), 2);
        const roundCenter = (lat, lng) => ({ lat: Number(lat.toFixed(6)), lng: Number(lng.toFixed(6)) });

        // 1. One central location is enough if it covers (almost) every location.
        const median = computeGeometricMedian(points);
        const medianVec = latLngToUnitVector(median.lat, median.lng);
        let insideMedian = 0;
        points.forEach(pt => {
            const v = latLngToUnitVector(pt.lat, pt.lng);
            const d2 = (v[0] - medianVec[0]) ** 2 + (v[1] - medianVec[1]) ** 2 + (v[2] - medianVec[2]) ** 2;
            if (d2 <= chord2) insideMedian++;
        });
        if (insideMedian >= points.length * (1 - LANDSCAPE_MIN_GAIN_RATIO)) return [median];

        // 2. Greedy maximum coverage on unit vectors (exact distances, no projection).
        const sample = sampleLandscapePoints(points, LANDSCAPE_MAX_SAMPLE_POINTS);
        const n = sample.length;
        const xs = new Float64Array(n);
        const ys = new Float64Array(n);
        const zs = new Float64Array(n);
        sample.forEach((pt, i) => {
            const v = latLngToUnitVector(pt.lat, pt.lng);
            xs[i] = v[0]; ys[i] = v[1]; zs[i] = v[2];
        });

        // Candidates: some of the locations themselves + a grid over the zone.
        const candidates = sampleLandscapePoints(sample, LANDSCAPE_MAX_POINT_CANDIDATES)
            .map(pt => latLngToUnitVector(pt.lat, pt.lng));

        const refLng = sample[0].lng;
        const relLng = lng => (((lng - refLng + 180) % 360) + 360) % 360 - 180;
        let minLat = Infinity, maxLat = -Infinity, minRel = Infinity, maxRel = -Infinity, sumLat = 0;
        sample.forEach(pt => {
            const rel = relLng(pt.lng);
            minLat = Math.min(minLat, pt.lat);
            maxLat = Math.max(maxLat, pt.lat);
            minRel = Math.min(minRel, rel);
            maxRel = Math.max(maxRel, rel);
            sumLat += pt.lat;
        });
        const cosLat = Math.max(0.05, Math.cos(sumLat / n * Math.PI / 180));
        const radiusDeg = radiusKm / 111.195;
        let stepDeg = Math.max(radiusDeg / 3,
            Math.sqrt((maxLat - minLat) * (maxRel - minRel) * cosLat / LANDSCAPE_MAX_GRID_CANDIDATES));
        if (!(stepDeg > 0)) stepDeg = radiusDeg / 3;
        for (let lat = minLat; lat <= maxLat + stepDeg; lat += stepDeg) {
            for (let rel = minRel; rel <= maxRel + stepDeg / cosLat; rel += stepDeg / cosLat) {
                candidates.push(latLngToUnitVector(Math.max(-90, Math.min(90, lat)), refLng + rel));
            }
        }

        const uncovered = new Uint8Array(n).fill(1);
        const countUncovered = c => {
            let count = 0;
            for (let i = 0; i < n; i++) {
                if (!uncovered[i]) continue;
                const dx = xs[i] - c[0], dy = ys[i] - c[1], dz = zs[i] - c[2];
                if (dx * dx + dy * dy + dz * dz <= chord2) count++;
            }
            return count;
        };

        // Lazy greedy: gains only decrease, so a stale gain is an upper bound.
        const upper = candidates.map(countUncovered);
        const freshRound = new Int32Array(candidates.length).fill(-1);
        const minGain = Math.max(1, Math.ceil(LANDSCAPE_MIN_GAIN_RATIO * n));
        const centers = [];
        for (let round = 0; round < LANDSCAPE_MAX_CENTERS; round++) {
            let best = -1;
            for (;;) {
                let bi = -1, bv = 0;
                for (let c = 0; c < upper.length; c++) {
                    if (upper[c] > bv) { bv = upper[c]; bi = c; }
                }
                if (bi < 0) break;
                if (freshRound[bi] === round) { best = bi; break; }
                upper[bi] = countUncovered(candidates[bi]);
                freshRound[bi] = round;
            }
            if (best < 0) break;
            // The first center is always kept; further ones must be worth it.
            if (centers.length > 0 && upper[best] < minGain) break;

            const c = candidates[best];
            for (let i = 0; i < n; i++) {
                if (!uncovered[i]) continue;
                const dx = xs[i] - c[0], dy = ys[i] - c[1], dz = zs[i] - c[2];
                if (dx * dx + dy * dy + dz * dz <= chord2) uncovered[i] = 0;
            }
            upper[best] = 0;
            centers.push(roundCenter(
                Math.atan2(c[2], Math.hypot(c[0], c[1])) * 180 / Math.PI,
                Math.atan2(c[1], c[0]) * 180 / Math.PI
            ));
        }
        return centers;
    }

    // Centers of an imported landscape for the scope the meta is saved with, each
    // carrying the country found at import time.
    function buildLandscapeCenters(landscapeImport, scope) {
        if (!landscapeImport || !landscapeImport.points?.length) return null;
        const radiusKm = getDistanceForScope(scope);
        if (!(radiusKm > 0)) return null;
        return computeLandscapeCenters(landscapeImport.points, radiusKm).map(center => ({
            ...center,
            country: landscapeImport.country || null,
            nominatimCountry: landscapeImport.nominatimCountry || null
        }));
    }

    // Country of a coordinate (English names, same source as the rest of the script).
    // Falls back to the country of the current location if the lookup fails.
    async function geocodeCountryForCoordinates(lat, lng) {
        try {
            const url = `https://nominatim.openstreetmap.org/reverse?format=json&zoom=3&lat=${lat}&lon=${lng}&accept-language=en`;
            const response = await fetch(url);
            const data = await response.json();
            const name = data?.address?.country;
            if (name) {
                const country = normalizeCountry(name, lat, lng);
                return { country, nominatimCountry: country };
            }
        } catch (err) {
            console.warn('[BetterMetas] Landscape country lookup failed:', err);
        }
        return {
            country: currentLocationData.country || currentLocationData.nominatimCountry || null,
            nominatimCountry: currentLocationData.nominatimCountry || currentLocationData.country || null
        };
    }

    function isLandscapeCenterKey(key) {
        return String(key).startsWith(LANDSCAPE_CENTER_KEY_PREFIX);
    }

    function isSameCoordinate(a, b) {
        const x = normalizeCoordinate(a);
        const y = normalizeCoordinate(b);
        return x !== null && y !== null && Math.abs(x - y) < 1e-6;
    }

    function hasLandscapeCenterEntry(locations, metaId) {
        return Object.keys(locations || {}).some(key =>
            isLandscapeCenterKey(key) && getLocationMetaIds(locations[key]).includes(metaId));
    }

    // Unlinks the meta from every centre entry it is in (an entry left without any
    // meta is deleted). Entries are replaced, never mutated, so a previous map
    // snapshot (used for rollback) stays intact.
    function removeLandscapeCenterEntry(locations, metaId) {
        Object.keys(locations).forEach(key => {
            if (!isLandscapeCenterKey(key)) return;
            const entry = normalizeLocationEntry(locations[key]);
            if (!entry || !entry.metas.includes(metaId)) return;

            const remaining = entry.metas.filter(id => id !== metaId);
            if (remaining.length === 0) {
                delete locations[key];
            } else {
                locations[key] = { ...entry, metas: remaining };
            }
        });
    }

    // Links the meta to ONE centre location. If a centre entry already exists at the same
    // coordinates (e.g. created for another meta of the same landscape), the meta is
    // added to its list of metas instead of creating a duplicate location.
    // Returns the key of the entry holding the meta.
    function addLandscapeCenterEntry(locations, metaId, center) {
        const sharedKey = Object.keys(locations).find(key =>
            isLandscapeCenterKey(key) &&
            isSameCoordinate(locations[key]?.lat, center.lat) &&
            isSameCoordinate(locations[key]?.lng, center.lng));
        if (sharedKey) {
            const entry = normalizeLocationEntry(locations[sharedKey]);
            locations[sharedKey] = { ...entry, metas: Array.from(new Set([...entry.metas, metaId])) };
            return sharedKey;
        }

        const baseKey = getLandscapeCenterKey(metaId);
        let key = baseKey;
        let counter = 2;
        while (locations[key]) key = `${baseKey}_${counter++}`;
        locations[key] = {
            metas: [metaId],
            lat: center.lat,
            lng: center.lng,
            country: center.country || null,
            nominatimCountry: center.nominatimCountry || null,
            region: null,
            city: null,
            road: null
        };
        return key;
    }

    // Replaces ALL the centres of the meta (previous ones are dropped first, so
    // re-importing moves them). Returns the keys of the entries holding the meta.
    function setLandscapeCenterEntries(locations, metaId, centers) {
        removeLandscapeCenterEntry(locations, metaId);
        return centers.map(center => addLandscapeCenterEntry(locations, metaId, center));
    }

    function normalizeLocationMap(value) {
        if (!value || typeof value !== 'object' || Array.isArray(value)) return {};

        const normalized = {};
        Object.entries(value).forEach(([panoid, entry]) => {
            const normalizedEntry = normalizeLocationEntry(entry);
            if (normalizedEntry) {
                normalized[panoid] = normalizedEntry;
            }
        });
        return normalized;
    }

    function normalizeMetaList(value) {
        return Array.isArray(value)
            ? value
                .filter(meta => meta && typeof meta.id === 'string' && meta.id.trim())
                .map(meta => ({
                    ...meta,
                    scope: normalizeScope(meta.scope),
                    tags: normalizeTags(meta.tags)
                }))
            : [];
    }

    function stringifyJsonContent(content) {
        return JSON.stringify(content, null, 2).replace(/[^\x00-\x7F]/g, (char) => {
            return `\\u${char.charCodeAt(0).toString(16).padStart(4, '0')}`;
        });
    }

    function normalizeDataSnapshot(value) {
        if (!value || typeof value !== 'object') return null;
        return {
            userLocationMap: normalizeLocationMap(value.userLocationMap),
            userMetas: normalizeMetaList(value.userMetas)
        };
    }

    function buildUniqueMetas(userMetas) {
        const seen = new Set();
        return (userMetas || []).filter(meta => {
            if (!meta || !meta.id || seen.has(meta.id)) return false;
            seen.add(meta.id);
            return true;
        });
    }

    function applyDataSnapshot(snapshot, options = {}) {
        const normalized = options.alreadyNormalized ? snapshot : normalizeDataSnapshot(snapshot);
        if (!normalized) return null;

        const tempUserMetas = normalized.userMetas.slice();
        const tempUserLocationMap = { ...normalized.userLocationMap };

        if (options.prunePending) {
            pruneConfirmedPendingLocalChanges(tempUserMetas, tempUserLocationMap);
        }

        const pending = mergePendingLocalChangesInto(tempUserMetas, tempUserLocationMap);

        userLocationMap = tempUserLocationMap;
        proximityIndexDirty = true;
        userMetaIds = new Set(tempUserMetas.map(meta => meta.id).filter(Boolean));
        metasData = buildUniqueMetas(tempUserMetas);
        rebuildMetaIndexes();

        return { pending, userMetas: tempUserMetas, userLocationMap: tempUserLocationMap };
    }

    function rebuildMetaIndexes() {
        metaById = new Map();
        metaSearchTextById = null;
        metasData.forEach(meta => {
            metaById.set(meta.id, meta);
        });
        metaRenderVersion += 1;
        proximityIndexDirty = true;
    }

    function ensureMetaSearchIndex() {
        if (metaSearchTextById) return metaSearchTextById;

        metaSearchTextById = new Map();
        metasData.forEach(meta => {
            // Search goes through the id (which embeds the country), the
            // title, the scope and the tags - NOT the description.
            // The id is also indexed with separators turned into spaces so
            // that "united states" matches "united-states-of-america_...".
            metaSearchTextById.set(meta.id, [
                meta.id,
                String(meta.id).replace(/[-_]+/g, ' '),
                meta.title,
                meta.scope,
                ...(meta.tags || [])
            ].filter(Boolean).join(' ').toLowerCase());
        });
        return metaSearchTextById;
    }

    // ---- Segments (scope "segment") --------------------------------------------------
    // A segment is stored in ONE location entry:
    //   lat / lng     corner A (the panorama the entry is keyed on)
    //   latB / lngB   corner B (null until a second location is linked)
    //   road          LIST of roads of the stretch (names / refs)
    // A location matches when it is on ANY road of the list and inside the rectangle
    // spanned by A and B (see isInsideSegment). An entry holds a single meta, so a meta can
    // have several entries = several stretches.
    function toLocalKm(lat, lng, refLat, refLng, cosLat) {
        let dLng = lng - refLng;
        while (dLng > 180) dLng -= 360;
        while (dLng < -180) dLng += 360;
        return [dLng * cosLat * 111.32, (lat - refLat) * 110.57];
    }

    // Is the position inside the stretch? The road itself is already checked by the caller
    // (same name/ref), so the geometry only has to say whether the position lies between A
    // and B. A and B are the two opposite corners of an axis-aligned rectangle (north/south,
    // east/west), grown by SEGMENT_BOX_MARGIN_KM on every side: the box contains the bends
    // and detours of the road, and a road running exactly north-south or east-west still
    // gets some width. A single point (B not linked yet) is a circle of SEGMENT_CORRIDOR_KM.
    function isInsideSegment(lat, lng, points) {
        const cosLat = Math.max(0.05, Math.cos(lat * Math.PI / 180));
        // Coordinates relative to the position, so the position is the origin (0, 0).
        const xy = points.map(p => toLocalKm(p.lat, p.lng, lat, lng, cosLat));
        if (xy.length === 1) return Math.hypot(xy[0][0], xy[0][1]) <= SEGMENT_CORRIDOR_KM;
        const xs = xy.map(c => c[0]), ys = xy.map(c => c[1]);
        return 0 >= Math.min(...xs) - SEGMENT_BOX_MARGIN_KM && 0 <= Math.max(...xs) + SEGMENT_BOX_MARGIN_KM &&
            0 >= Math.min(...ys) - SEGMENT_BOX_MARGIN_KM && 0 <= Math.max(...ys) + SEGMENT_BOX_MARGIN_KM;
    }

    // Distinct, trimmed roads (accent/case-insensitive) from a string or a list.
    function getSegmentRoadList(value) {
        const seen = new Set();
        const list = [];
        (Array.isArray(value) ? value : [value]).forEach(road => {
            const text = road === null || road === undefined ? '' : String(road).trim();
            const key = normalizeRoadKey(text);
            if (!key || seen.has(key)) return;
            seen.add(key);
            list.push(text);
        });
        return list;
    }

    function hasSegmentPointB(entry) {
        return !!entry && normalizeCoordinate(entry.latB) !== null && normalizeCoordinate(entry.lngB) !== null;
    }

    // Does the road list of the entry cover the current location (any road in common with
    // the names/refs the geocoders gave for it)?
    function segmentRoadsCoverCurrentLocation(entry) {
        const curRoadKeys = getRoadCandidateKeys(currentLocationData.roadSources);
        return getSegmentRoadList(entry.road).some(road => curRoadKeys.includes(normalizeRoadKey(road)));
    }

    // Which existing segment entry of `metaId` does the current location belong to?
    //   1. one that already has A or B at this exact position;
    //   2. one that already has A and B and whose rectangle contains the position
    //      (the link then only adds the road to its list);
    //   3. otherwise the nearest one that has no B yet: the position becomes its point B.
    // null when there is none (position outside every complete rectangle): a new stretch
    // starts with the position as point A.
    function findSegmentLinkKey(locations, metaId) {
        const curLat = normalizeCoordinate(currentLocationData.lat);
        const curLng = normalizeCoordinate(currentLocationData.lng);
        if (curLat === null || curLng === null) return null;

        const candidates = Object.entries(locations || {}).filter(([, entry]) =>
            entry && typeof entry === 'object' && !Array.isArray(entry) && entry.segment &&
            getLocationMetaIds(entry).includes(metaId) && entryMatchesCurrentCountry(entry));

        const exact = candidates.find(([, entry]) =>
            (isSameCoordinate(entry.lat, curLat) && isSameCoordinate(entry.lng, curLng)) ||
            (isSameCoordinate(entry.latB, curLat) && isSameCoordinate(entry.lngB, curLng)));
        if (exact) return exact[0];

        const containing = candidates.find(([, entry]) => hasSegmentPointB(entry) &&
            normalizeCoordinate(entry.lat) !== null && normalizeCoordinate(entry.lng) !== null &&
            isInsideSegment(curLat, curLng, [
                { lat: normalizeCoordinate(entry.lat), lng: normalizeCoordinate(entry.lng) },
                { lat: normalizeCoordinate(entry.latB), lng: normalizeCoordinate(entry.lngB) }
            ]));
        if (containing) return containing[0];

        // Outside every complete rectangle: the nearest stretch without B gets the position
        // as point B; when there is none, null makes the caller start a new stretch.
        let bestKey = null;
        let bestDistance = Infinity;
        candidates.forEach(([key, entry]) => {
            if (hasSegmentPointB(entry)) return;
            const lat = normalizeCoordinate(entry.lat);
            const lng = normalizeCoordinate(entry.lng);
            if (lat === null || lng === null) return;
            const distance = getHaversineDistance(lat, lng, curLat, curLng);
            if (distance < bestDistance) {
                bestKey = key;
                bestDistance = distance;
            }
        });
        return bestKey;
    }

    // Writes the current location into a segment entry: its road joins the list when the
    // list does not cover it yet, and the position becomes point B when B is still empty
    // (a new entry has the position as point A, so B stays empty). `currentRoads` is the
    // road list of the current location (see getLocationSnapshotForScope).
    function applyCurrentLocationToSegmentEntry(entry, currentRoads) {
        entry.segment = true;
        const roads = getSegmentRoadList(entry.road);
        if (!segmentRoadsCoverCurrentLocation({ road: roads })) roads.push(...getSegmentRoadList(currentRoads));
        entry.road = getSegmentRoadList(roads);

        if (!hasSegmentPointB(entry)) {
            const atPointA = isSameCoordinate(entry.lat, currentLocationData.lat) &&
                isSameCoordinate(entry.lng, currentLocationData.lng);
            const curLat = normalizeCoordinate(currentLocationData.lat);
            const curLng = normalizeCoordinate(currentLocationData.lng);
            const canSetB = !atPointA && curLat !== null && curLng !== null;
            entry.latB = canSetB ? curLat : null;
            entry.lngB = canSetB ? curLng : null;
        }
    }

    // A pending (not yet confirmed) segment entry is confirmed once the saved file has its
    // point B (when it has one) and every road of its list.
    function isSegmentGeometryConfirmed(rawEntry, pendingEntry) {
        if (!pendingEntry || Array.isArray(pendingEntry) || !pendingEntry.segment) return true;
        if (!rawEntry || Array.isArray(rawEntry)) return false;
        if (hasSegmentPointB(pendingEntry) &&
            !(isSameCoordinate(rawEntry.latB, pendingEntry.latB) && isSameCoordinate(rawEntry.lngB, pendingEntry.lngB))) {
            return false;
        }
        const rawRoads = getSegmentRoadList(rawEntry.road).map(normalizeRoadKey);
        return getSegmentRoadList(pendingEntry.road).every(road => rawRoads.includes(normalizeRoadKey(road)));
    }

    // One indexed stretch per segment entry and meta: its roads and its corner(s).
    // Without point B the stretch is a single point (a circle, see isInsideSegment).
    function buildSegmentIndex(entries) {
        const segments = [];
        entries.forEach(({ metaIds, lat, lng, latB, lngB, country, roads, segment }) => {
            if (!segment || lat === null || lng === null) return;
            const roadKeys = Array.from(new Set((roads || []).map(normalizeRoadKey).filter(Boolean)));
            if (roadKeys.length === 0) return;
            const points = [{ lat, lng }];
            if (latB !== null && latB !== undefined && lngB !== null && lngB !== undefined) {
                points.push({ lat: latB, lng: lngB });
            }
            metaIds.forEach(id => segments.push({ metaId: id, roads: roadKeys, country, points }));
        });
        return segments;
    }

    function rebuildProximityIndexes() {
        indexedLocationEntries = [];
        panoidKeyIndex = buildPanoidKeyIndex(userLocationMap);
        Object.values(userLocationMap).forEach(entry => {
            const lat = normalizeCoordinate(entry.lat);
            const lng = normalizeCoordinate(entry.lng);
            const country = normalizeCountry(entry.nominatimCountry || entry.country, lat, lng);
            indexedLocationEntries.push({
                metaIds: getLocationMetaIds(entry),
                lat,
                lng,
                latB: normalizeCoordinate(entry.latB),
                lngB: normalizeCoordinate(entry.lngB),
                country,
                regionKey: normalizeNameForMatch(entry.region),
                cityKey: normalizeNameForMatch(entry.city),
                roads: getNormalizedRoadNames(entry.road),
                roadKeys: getNormalizedRoadNames(entry.road).map(normalizeNameForMatch).filter(Boolean),
                segment: !!entry.segment
            });
        });
        indexedSegments = buildSegmentIndex(indexedLocationEntries);
        proximityIndexDirty = false;
        proximityIndexVersion += 1;
        lastProximityCacheKey = null;
    }

    function getMetaById(metaId) {
        return metaById.get(metaId);
    }

    function debounce(callback, delay = SEARCH_DEBOUNCE_MS) {
        let timer = null;
        return function(...args) {
            clearTimeout(timer);
            timer = setTimeout(() => callback.apply(this, args), delay);
        };
    }

    // All persistent values (settings, HUD geometry, pending changes, caches) go
    // through these three helpers, backed by GM storage. Values written by older
    // versions in localStorage are moved to GM storage the first time they are read.
    function readStoredValue(key, defaultValue = null) {
        try {
            const value = GM_getValue(key, null);
            if (value !== null && value !== undefined) return value;

            const legacy = localStorage.getItem(key);
            if (legacy !== null) {
                GM_setValue(key, legacy);
                localStorage.removeItem(key);
                return legacy;
            }
        } catch (err) {
            console.warn(`[BetterMetas] Could not read stored value "${key}":`, err);
        }
        return defaultValue;
    }

    function writeStoredValue(key, value) {
        try {
            GM_setValue(key, value);
        } catch (err) {
            console.warn(`[BetterMetas] Could not save stored value "${key}":`, err);
        }
    }

    function clearStoredValue(key) {
        try {
            GM_setValue(key, null);
            localStorage.removeItem(key);
        } catch (err) {
            console.warn(`[BetterMetas] Could not clear stored value "${key}":`, err);
        }
    }

    function loadCachedDataSnapshot() {
        try {
            const cached = JSON.parse(readStoredValue(DATA_CACHE_STORAGE_KEY) || 'null');
            if (!cached || typeof cached !== 'object') return null;
            if (cached.version !== DATA_CACHE_VERSION) {
                clearStoredValue(DATA_CACHE_STORAGE_KEY);
                return null;
            }
            if (!cached.timestamp || Date.now() - cached.timestamp > DATA_CACHE_MAX_AGE_MS) {
                clearStoredValue(DATA_CACHE_STORAGE_KEY);
                return null;
            }
            // Saved already normalized (see fetchLocationData) and tied to
            // DATA_CACHE_VERSION, so it is not normalized a second time.
            if (!Array.isArray(cached.userMetas) || !cached.userLocationMap ||
                typeof cached.userLocationMap !== 'object' || Array.isArray(cached.userLocationMap)) {
                clearStoredValue(DATA_CACHE_STORAGE_KEY);
                return null;
            }
            return { userLocationMap: cached.userLocationMap, userMetas: cached.userMetas };
        } catch (err) {
            console.warn('[BetterMetas] Invalid cached data snapshot:', err);
            clearStoredValue(DATA_CACHE_STORAGE_KEY);
            return null;
        }
    }

    function saveDataSnapshotCache(snapshot) {
        if (!snapshot || typeof snapshot !== 'object') return;

        try {
            writeStoredValue(DATA_CACHE_STORAGE_KEY, JSON.stringify({
                version: DATA_CACHE_VERSION,
                timestamp: Date.now(),
                userLocationMap: snapshot.userLocationMap || {},
                userMetas: snapshot.userMetas || []
            }));
        } catch (err) {
            console.warn('[BetterMetas] Could not save data cache:', err);
        }
    }

    function applyCachedDataSnapshot() {
        const cached = loadCachedDataSnapshot();
        if (!cached) return false;

        applyDataSnapshot(cached, { alreadyNormalized: true });
        debugLog(`[BetterMetas] Loaded cached DB: ${Object.keys(userLocationMap).length} locs, ${metasData.length} metas.`);
        if (currentPanoid) {
            updateStatus(`ID: ${currentPanoid.substring(0,12)}...`);
            refreshDisplay();
        } else {
            updateStatus(`Cached DB (${metasData.length} metas)`);
        }
        return true;
    }

    let currentPanoid = null;
    let selectedMetaIds = new Set();
    let selectedAdminMetaId = null;
    let adminSortMode = 'newest';
    let activeMutationCount = 0;
    let backgroundRefreshTimer = null;

    const ALL_SCOPES = ['countrywide', 'region', 'city', 'road', 'segment', '100km', '10km', '1km', 'unique'];
    const LINKED_META_SCOPE_ORDER = ['unique', '1km', '10km', 'segment', 'road', 'city', '100km', 'region', 'countrywide'];
    // "segment" scope: two bounds A and B are the opposite corners of a rectangle, grown by
    // SEGMENT_BOX_MARGIN_KM on every side; a single bound matches within SEGMENT_CORRIDOR_KM.
    const SEGMENT_CORRIDOR_KM = 5;
    const SEGMENT_BOX_MARGIN_KM = 1.5;
    const LINKED_META_SCOPE_RANK = new Map(LINKED_META_SCOPE_ORDER.map((scope, index) => [scope, index]));
    const TAG_PRESETS = ['plants', 'landscape', 'bollards', 'poles', 'signs', 'plates', 'cars', 'soil', 'structures', 'road', 'camera', 'language', 'architecture', 'antenna'];
    let activeScopes = loadActiveScopes();
    let activeTags = loadActiveTags();

    // Locking & Visibility State
    let nextPanoid = null;
    let nextPanoidQueuedAt = 0;
    let userDismissed = false;

    // Active StreetView Instance
    let svInstance = null;
    let hooksInstalled = false;
    let googleWatcherInstalled = false;
    let watchedGoogleObject = null;
    let watchedMapsObject = null;
    let locationExtractionSequence = 0;
    let streetViewListenerInstance = null;
    let streetViewListenerHandles = [];
    let sharedGeocoder = null;
    let activeNominatimController = null;
    let activeNominatimKey = null;
    const recentlyGeocodedLocations = new Set();

    /** Current Location State */
    let currentLocationData = {
        address: null,
        country: null,          // Normalized (Google preferred)
        nominatimCountry: null, // Raw Nominatim result
        googleCountry: null,    // Raw Google result
        region: null,
        city: null,
        road: null,
        roadSources: newRoadSources(),
        placeSources: newPlaceSources(),
        geocodeDone: { google: false, nominatim: false },
        lat: null,
        lng: null
    };

    function getScopeLabel(scope) {
        if (!scope) return '';
        if (/^\d+km$/i.test(scope)) return scope;
        return scope.charAt(0).toUpperCase() + scope.slice(1);
    }

    function normalizeScope(scope, fallback = 'countrywide') {
        const normalized = String(scope || '').trim().toLowerCase();
        if (!normalized) return fallback;
        if (normalized === 'longitude') return 'region';
        return ALL_SCOPES.includes(normalized) ? normalized : fallback;
    }

    function sortLinkedMetasByPrecision(metas) {
        return metas
            .map((meta, index) => ({ meta, index }))
            .sort((a, b) => {
                const rankA = LINKED_META_SCOPE_RANK.get(normalizeScope(a.meta.scope)) ?? Number.MAX_SAFE_INTEGER;
                const rankB = LINKED_META_SCOPE_RANK.get(normalizeScope(b.meta.scope)) ?? Number.MAX_SAFE_INTEGER;
                return rankA - rankB || a.index - b.index;
            })
            .map(({ meta }) => meta);
    }

    function normalizeTags(value) {
        const tags = Array.isArray(value)
            ? value
            : String(value || '').split(',');
        const seen = new Set();
        return tags
            .map(tag => String(tag || '').trim().toLowerCase())
            .filter(tag => TAG_PRESETS.includes(tag))
            .filter(tag => {
                if (seen.has(tag)) return false;
                seen.add(tag);
                return true;
            });
    }

    function renderScopePills(scopes, selectedScopes = null) {
        return scopes.map(scope => {
            const selectedClass = selectedScopes && selectedScopes.has(scope) ? ' gg-tag-selected' : '';
            return `<span class="gg-tag-pill gg-scope-pill${selectedClass}" data-value="${escapeHtml(scope)}">${escapeHtml(getScopeLabel(scope))}</span>`;
        }).join('');
    }

    function renderTagPills(tags) {
        return tags.map(tag => `<span class="gg-tag-pill gg-tag-filter-pill">${escapeHtml(tag)}</span>`).join('');
    }

    function renderTagFilterPills(tags, selectedTags = null) {
        return tags.map(tag => {
            const selectedClass = selectedTags && selectedTags.has(tag) ? ' gg-tag-selected' : '';
            return `<span class="gg-tag-pill gg-tag-filter-pill${selectedClass}" data-value="${escapeHtml(tag)}">${escapeHtml(tag)}</span>`;
        }).join('');
    }

    const HTML_ESCAPES = {
        '&': '&amp;',
        '<': '&lt;',
        '>': '&gt;',
        '"': '&quot;',
        "'": '&#39;'
    };

    function escapeHtml(value) {
        return String(value ?? '').replace(/[&<>"']/g, char => HTML_ESCAPES[char]);
    }

    // Discord-like inline formatting for meta descriptions.
    // Supported: **bold** and *italic* (nestable). Everything else is plain
    // text. The input is escaped character by character, so no HTML from the
    // description can ever reach the DOM.
    const META_FORMAT_DELIMITERS = [
        { marker: '**', char: '*', tag: 'strong' },
        { marker: '*', char: '*', tag: 'em' }
    ];

    function findClosingFormatMarker(source, delimiter, fromIndex) {
        const { marker, char } = delimiter;
        let index = source.indexOf(marker, fromIndex);
        while (index !== -1) {
            const previous = source[index - 1];
            const next = source[index + marker.length];
            // The closing marker must hug non-space text and must not be
            // part of a longer run of the same character (e.g. "***").
            if (previous && !/\s/.test(previous) && previous !== char && next !== char) {
                return index;
            }
            index = source.indexOf(marker, index + 1);
        }
        return -1;
    }

    function formatMetaDescription(value) {
        const format = (source) => {
            let html = '';
            let plainText = ''; // run of plain characters, escaped once when it ends
            let i = 0;
            while (i < source.length) {
                const delimiter = META_FORMAT_DELIMITERS.find(d => source.startsWith(d.marker, i));
                if (delimiter) {
                    const contentStart = i + delimiter.marker.length;
                    const first = source[contentStart];
                    // The opening marker must be followed by non-space text
                    // (so "2 * 3 * 4" stays plain), must not continue a run of
                    // the same character, and must not be glued to a word when
                    // followed by punctuation (so a footnote star like
                    // "Wusta*, or ..." is not treated as an opener).
                    const previous = source[i - 1];
                    const isFootnoteStar = previous && /[\p{L}\p{N}]/u.test(previous) && /[^\p{L}\p{N}\s]/u.test(first || '');
                    if (first && !/\s/.test(first) && first !== delimiter.char && previous !== delimiter.char && !isFootnoteStar) {
                        const end = findClosingFormatMarker(source, delimiter, contentStart + 1);
                        if (end !== -1) {
                            html += escapeHtml(plainText);
                            plainText = '';
                            html += `<${delimiter.tag}>${format(source.slice(contentStart, end))}</${delimiter.tag}>`;
                            i = end + delimiter.marker.length;
                            continue;
                        }
                    }
                }
                plainText += source[i];
                i += 1;
            }
            return html + escapeHtml(plainText);
        };
        return format(String(value ?? ''));
    }

    // "Côte d'Ivoire" -> "cote-d-ivoire"
    function slugifyForMetaId(value) {
        return stripDiacritics(String(value || ''))
            .toLowerCase()
            .replace(/[^a-z0-9]+/g, '-')
            .replace(/^-+|-+$/g, '') || 'unknown';
    }

    // New format: "<country>_<timestamp>_<random>", e.g. "kenya_1718000000000_a1b2c".
    // The country comes from the detected location (same value that is stored
    // on the location entry). Falls back to "unknown" when nothing is detected yet.
    function generateMetaId() {
        const location = getCurrentLocationSnapshot();
        const country = normalizeCountry(location.country || location.nominatimCountry, location.lat, location.lng);
        return `${slugifyForMetaId(country)}_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`;
    }

    function getSafeImageUrl(value) {
        if (!value) return '';
        const text = String(value).trim();
        // Images imported into data/<country>/ are stored as a relative path.
        if (LOCAL_IMAGE_PATH_RE.test(text)) return getRawFileUrl(text);
        try {
            const url = new URL(text, window.location.href);
            return ['http:', 'https:'].includes(url.protocol) ? url.href : '';
        } catch (err) {
            return '';
        }
    }

    function renderMetaImage(imageUrl, deferred = false) {
        const safeUrl = getSafeImageUrl(imageUrl);
        if (!safeUrl) return '';
        const sourceAttribute = deferred
            ? `data-gg-src="${escapeHtml(safeUrl)}"`
            : `src="${escapeHtml(safeUrl)}"`;
        return `<img ${sourceAttribute} class="gg-meta-image" loading="lazy" decoding="async" alt="">`;
    }

    // Some image hosts (e.g. plonkit.net) send a Cross-Origin-Resource-Policy
    // header that makes browsers block a direct <img src="..."> load from a
    // different origin like geoguessr.com. GM_xmlhttpRequest runs outside the
    // page's fetch/img pipeline, so it is not subject to that header; we use it
    // to download the image ourselves and hand the <img> a local blob: URL
    // instead. This works regardless of where the image is actually hosted
    // (plonkit, Discord CDN, imgur, etc.).
    // LRU cache url -> Promise<Blob|null>: a Map iterates in insertion order, so the
    // first key is the least recently used. Capped so a long session cannot keep
    // every downloaded image in memory.
    const IMAGE_CACHE_MAX_ENTRIES = 100;
    const imageBlobCache = new Map();
    const IMAGE_FETCH_TIMEOUT_MS = 30000;

    function getImageRequestHeaders(url) {
        const headers = { Accept: 'image/avif,image/webp,image/apng,image/*,*/*;q=0.8' };
        try {
            // Look like a same-site load: hosts with hotlink protection
            // usually only accept their own origin as Referer.
            headers.Referer = `${new URL(url).origin}/`;
        } catch (err) {
            // Ignore: the request is still sent without a Referer.
        }
        return headers;
    }

    function fetchImageBlob(url) {
        if (imageBlobCache.has(url)) {
            // Hit: move the entry to the most recently used position.
            const cached = imageBlobCache.get(url);
            imageBlobCache.delete(url);
            imageBlobCache.set(url, cached);
            return cached;
        }

        const promise = new Promise(resolve => {
            // Failures are logged unconditionally (not behind DEBUG_LOGGING):
            // when the proxy fails, the direct-load fallback below triggers
            // the browser's CORP error, which hides the real cause.
            // Failed downloads are not cached, so a later hover can retry.
            const fail = reason => {
                console.warn('[BetterMetas] Image proxy failed:', url, reason);
                imageBlobCache.delete(url);
                resolve(null);
            };

            if (typeof GM_xmlhttpRequest !== 'function') {
                fail('GM_xmlhttpRequest unavailable');
                return;
            }
            GM_xmlhttpRequest({
                method: 'GET',
                url,
                headers: getImageRequestHeaders(url),
                responseType: 'blob',
                timeout: IMAGE_FETCH_TIMEOUT_MS,
                onload: (response) => {
                    if (response.status < 200 || response.status >= 300 || !response.response) {
                        fail(`HTTP ${response.status}`);
                        return;
                    }
                    const blob = response.response;
                    if (blob.type && !blob.type.startsWith('image/')) {
                        fail(`not an image (${blob.type})`);
                        return;
                    }
                    resolve(blob);
                },
                onerror: () => fail('network error'),
                ontimeout: () => fail('timeout')
            });
        });

        imageBlobCache.set(url, promise);
        while (imageBlobCache.size > IMAGE_CACHE_MAX_ENTRIES) {
            imageBlobCache.delete(imageBlobCache.keys().next().value);
        }
        // A failure that happens synchronously is reported before the entry above
        // exists: drop failed downloads here too so a later hover can retry.
        promise.then(blob => {
            if (blob === null && imageBlobCache.get(url) === promise) imageBlobCache.delete(url);
        });
        return promise;
    }

    // ---- Image import: remote URL -> data/<country>/<file> via local server ----
    const LOCAL_IMAGE_PATH_RE = /^data\/[a-z0-9_-]+\/[^/\\?#]+\.(png|jpe?g|webp|gif|avif)$/i;
    const IMAGE_EXT_BY_TYPE = { 'image/png': '.png', 'image/jpeg': '.jpg', 'image/webp': '.webp', 'image/gif': '.gif', 'image/avif': '.avif' };

    function isLocalImagePath(value) {
        return LOCAL_IMAGE_PATH_RE.test(String(value || '').trim());
    }

    function localFileExists(path) {
        return new Promise(resolve => {
            GM_xmlhttpRequest({
                method: 'GET',
                url: getRawFileUrl(path),
                responseType: 'blob',
                onload: r => resolve(r.status >= 200 && r.status < 300),
                onerror: () => resolve(false),
                ontimeout: () => resolve(false)
            });
        });
    }

    function putLocalBinaryFile(path, blob) {
        return new Promise((resolve, reject) => {
            GM_xmlhttpRequest({
                method: 'PUT',
                url: getRawFileUrl(path),
                headers: { 'Content-Type': blob.type || 'application/octet-stream' },
                data: blob,
                timeout: LOCAL_WRITE_TIMEOUT_MS,
                onload: r => (r.status >= 200 && r.status < 300)
                    ? resolve()
                    : reject(new Error(`HTTP ${r.status}: ${r.responseText || r.statusText || 'unknown error'}`)),
                onerror: () => reject(new Error('Local server request failed')),
                ontimeout: () => reject(new Error('Local server request timed out'))
            });
        });
    }

    function deleteLocalFile(path) {
        return new Promise((resolve, reject) => {
            GM_xmlhttpRequest({
                method: 'DELETE',
                url: getRawFileUrl(path),
                timeout: LOCAL_WRITE_TIMEOUT_MS,
                onload: r => (r.status >= 200 && r.status < 300) || r.status === 404
                    ? resolve()
                    : reject(new Error(`HTTP ${r.status}: ${r.responseText || r.statusText || 'unknown error'}`)),
                onerror: () => reject(new Error('Local server request failed')),
                ontimeout: () => reject(new Error('Local server request timed out'))
            });
        });
    }

    // Deletes an imported image (data/<country>/<file>) from disk. The caller
    // must already have checked that no other meta uses it. A failure never
    // aborts the calling save/delete: the user is just told about it.
    async function removeLocalImage(imagePath) {
        if (!isLocalImagePath(imagePath)) return;
        try {
            await deleteLocalFile(imagePath);
            imageBlobCache.delete(getRawFileUrl(imagePath));
        } catch (imgErr) {
            console.warn('[BetterMetas] Image delete failed:', imgErr);
            await showToolAlert('Image Not Deleted', `The meta change went through, but the unused image ${imagePath} could not be removed from disk (${imgErr.message}).`);
        }
    }

    // Undoes an image import after a failed save: deletes the file unless a loaded
    // meta still points to it (e.g. the import overwrote an image other metas use).
    async function removeImageIfUnused(imagePath) {
        const path = String(imagePath || '').trim();
        if (!isLocalImagePath(path)) return;
        if (metasData.some(meta => String(meta.imageUrl || '').trim() === path)) return;
        await removeLocalImage(path);
    }

    // ---- Image compression (applied when an image is imported) -------------------
    const IMAGE_MAX_DIMENSION_PX = 1600;       // longest side after resize
    const IMAGE_WEBP_QUALITY = 0.8;            // 0..1
    const IMAGE_SKIP_REENCODE_WEBP_BELOW_BYTES = 250 * 1024; // already-WebP images this small are kept as is

    function formatBytes(bytes) {
        return bytes >= 1048576 ? `${(bytes / 1048576).toFixed(1)} MB` : `${Math.round(bytes / 1024)} KB`;
    }

    // Converts any imported image (png, jpg, gif, avif...) to WebP, with the longest side
    // limited to IMAGE_MAX_DIMENSION_PX. Notes:
    //  - an animated GIF becomes a still WebP (first frame);
    //  - an image that is already a small WebP is kept as is;
    //  - if the conversion is impossible (browser cannot encode WebP, decoding error),
    //    the original blob is returned unchanged.
    async function compressImageBlob(blob) {
        if (!blob || !String(blob.type || '').startsWith('image/')) return blob;
        const isWebp = blob.type === 'image/webp';
        let bitmap = null;
        try {
            bitmap = await createImageBitmap(blob);
            const scale = Math.min(1, IMAGE_MAX_DIMENSION_PX / Math.max(bitmap.width, bitmap.height));
            if (isWebp && scale === 1 && blob.size <= IMAGE_SKIP_REENCODE_WEBP_BELOW_BYTES) return blob;

            const canvas = document.createElement('canvas');
            canvas.width = Math.max(1, Math.round(bitmap.width * scale));
            canvas.height = Math.max(1, Math.round(bitmap.height * scale));
            const ctx = canvas.getContext('2d');
            ctx.imageSmoothingQuality = 'high';
            ctx.drawImage(bitmap, 0, 0, canvas.width, canvas.height);

            const out = await new Promise(resolve => canvas.toBlob(resolve, 'image/webp', IMAGE_WEBP_QUALITY));
            // Browsers that cannot encode WebP silently return PNG: keep the original then.
            if (!out || out.type !== 'image/webp') return blob;
            // Re-encoding a WebP only makes sense if it gets smaller.
            if (isWebp && scale === 1 && out.size >= blob.size) return blob;
            console.log(`[BetterMetas] Image compressed: ${formatBytes(blob.size)} -> ${formatBytes(out.size)} (${canvas.width}x${canvas.height})`);
            return out;
        } catch (err) {
            console.warn('[BetterMetas] Image compression failed, keeping the original:', err);
            return blob;
        } finally {
            if (bitmap && typeof bitmap.close === 'function') bitmap.close();
        }
    }

    // Downloads `url` and saves it to data/<countrySlug>/<name>. Returns the
    // relative path to store in the meta's imageUrl.
    async function importRemoteImage(url, countrySlug) {
        const originalBlob = await fetchImageBlob(url);
        if (!originalBlob) throw new Error('Could not download the image');
        const blob = await compressImageBlob(originalBlob);

        const folder = slugifyForMetaId(countrySlug) || 'unknown';
        let fileName = 'image';
        try {
            fileName = decodeURIComponent(new URL(url).pathname.split('/').filter(Boolean).pop() || 'image');
        } catch (err) {
            // Keep the default name.
        }
        fileName = fileName.replace(/[<>:"/\\|?*\x00-\x1f]/g, '_').replace(/[. ]+$/, '') || 'image';
        if (blob !== originalBlob) {
            // Re-encoded as WebP: the file extension must follow.
            fileName = fileName.replace(/\.(png|jpe?g|webp|gif|avif)$/i, '') + '.webp';
        } else if (!/\.(png|jpe?g|webp|gif|avif)$/i.test(fileName)) {
            fileName += IMAGE_EXT_BY_TYPE[blob.type] || '.png';
        }

        const dot = fileName.lastIndexOf('.');
        const stem = fileName.slice(0, dot);
        const ext = fileName.slice(dot);
        let path = `data/${folder}/${fileName}`;
        if (await localFileExists(path)) {
            const overwrite = await showToolConfirm(
                'Image Already Exists',
                `An image named "${fileName}" already exists in data/${folder}/. Overwrite it?\n\nYES replaces the existing file.\nNO keeps it and saves the new image under a different name.`,
                { confirmText: 'YES', cancelText: 'NO' }
            );
            if (overwrite) {
                // Drop any cached copy so the HUD shows the new image.
                imageBlobCache.delete(getRawFileUrl(path));
            } else {
                for (let i = 2; await localFileExists(path); i++) {
                    path = `data/${folder}/${stem}_${i}${ext}`;
                }
            }
        }
        await putLocalBinaryFile(path, blob);
        return path;
    }

    // Value to store in a meta: local paths are kept, remote URLs are imported
    // into the country folder (falling back to the remote URL on failure).
    async function resolveImageForSave(rawValue, countrySlug) {
        const text = String(rawValue || '').trim();
        if (!text) return null;
        if (isLocalImagePath(text)) return text;
        const safeUrl = getSafeImageUrl(text);
        if (!safeUrl) return null;
        const localPrefix = getRawFileUrl('');
        if (safeUrl.startsWith(localPrefix)) return safeUrl.slice(localPrefix.length);
        if (!countrySlug || countrySlug === 'unknown') {
            await showToolAlert('Country Unknown', 'The country of this location is not known yet, so the image was not imported. The remote URL was kept; save the meta again later to import it.');
            return safeUrl;
        }
        try {
            return await importRemoteImage(safeUrl, countrySlug);
        } catch (err) {
            console.warn('[BetterMetas] Image import failed:', err);
            await showToolAlert('Image Import Failed', `The image could not be saved locally (${err.message}). The remote URL was kept instead.`);
            return safeUrl;
        }
    }

    // Country folder for a meta: taken from the location it is linked to
    // (whatever its scope), falling back to the id prefix ("namibia_...").
    // Folder name for a location-like object. `country` comes first because
    // normalizeCountry keeps territories separate (madeira, hawaii, hong-kong...),
    // unlike nominatimCountry (portugal, united-states, china). If `country` has
    // no Latin letters (e.g. Cyrillic) the English nominatimCountry is used.
    function getCountryFolderForLocation(location) {
        for (const name of [location?.country, location?.nominatimCountry]) {
            if (!name) continue;
            const slug = slugifyForMetaId(normalizeCountry(name, location.lat, location.lng));
            if (slug !== 'unknown') return slug;
        }
        return null;
    }

    // Waits (up to timeoutMs) for the geocoders to report a country for the
    // current location. Resolves to its folder name, or null on timeout.
    async function waitForDetectedCountryFolder(timeoutMs = 10000) {
        const deadline = Date.now() + timeoutMs;
        while (true) {
            const folder = getCountryFolderForLocation(getCurrentLocationSnapshot());
            if (folder || Date.now() >= deadline) return folder;
            await new Promise(resolve => setTimeout(resolve, 250));
        }
    }

    function getCountrySlugForMeta(meta) {
        const metaId = meta?.id;
        if (metaId) {
            for (const entry of Object.values(userLocationMap)) {
                if (!entry) continue;
                if (!getLocationMetaIds(entry).includes(metaId)) continue;
                const folder = getCountryFolderForLocation(entry);
                if (folder) return folder;
            }
        }
        return String(metaId || '').split('_')[0] || 'unknown';
    }

    // Full-screen viewer: wheel = zoom (towards cursor), drag = pan,
    // double-click = reset, click on the backdrop / Esc = close.
    function closeImageLightbox() {
        document.getElementById('gg-image-lightbox')?.remove();
    }

    function openImageLightbox(src) {
        closeImageLightbox();
        const overlay = document.createElement('div');
        overlay.id = 'gg-image-lightbox';
        const img = document.createElement('img');
        img.src = src;
        img.alt = '';
        img.draggable = false;
        const hint = document.createElement('div');
        hint.className = 'gg-lightbox-hint';
        hint.textContent = 'Scroll to zoom · drag to move · double-click to reset · Esc to close';
        overlay.append(img, hint);
        document.body.appendChild(overlay);

        let scale = 1, x = 0, y = 0;
        let drag = null;
        const apply = () => {
            img.style.transform = `translate(-50%, -50%) translate(${x}px, ${y}px) scale(${scale})`;
        };
        apply();

        overlay.addEventListener('wheel', e => {
            e.preventDefault();
            const next = Math.min(10, Math.max(1, scale * (e.deltaY < 0 ? 1.15 : 1 / 1.15)));
            const cx = e.clientX - window.innerWidth / 2;
            const cy = e.clientY - window.innerHeight / 2;
            const ratio = next / scale;
            x = cx - (cx - x) * ratio;
            y = cy - (cy - y) * ratio;
            scale = next;
            if (scale === 1) { x = 0; y = 0; }
            apply();
        }, { passive: false });

        overlay.addEventListener('mousedown', e => {
            if (e.button !== 0) return;
            drag = { startX: e.clientX, startY: e.clientY, x, y, moved: false };
            overlay.classList.add('gg-dragging');
            e.preventDefault();
        });
        window.addEventListener('mousemove', onMove);
        window.addEventListener('mouseup', onUp);
        document.addEventListener('keydown', onKey, true);

        function onMove(e) {
            if (!drag) return;
            const dx = e.clientX - drag.startX;
            const dy = e.clientY - drag.startY;
            if (Math.abs(dx) + Math.abs(dy) > 3) drag.moved = true;
            x = drag.x + dx;
            y = drag.y + dy;
            apply();
        }
        function onUp(e) {
            if (!drag) return;
            const wasClick = !drag.moved;
            drag = null;
            overlay.classList.remove('gg-dragging');
            if (wasClick && e.target === overlay) cleanup();
        }
        function onKey(e) {
            if (e.key !== 'Escape') return;
            e.stopPropagation();
            cleanup();
        }
        function cleanup() {
            window.removeEventListener('mousemove', onMove);
            window.removeEventListener('mouseup', onUp);
            document.removeEventListener('keydown', onKey, true);
            overlay.remove();
        }
        img.addEventListener('dblclick', () => { scale = 1; x = 0; y = 0; apply(); });
    }

    document.addEventListener('click', event => {
        const image = event.target instanceof Element ? event.target.closest('.gg-meta-image') : null;
        if (!image || !image.src) return;
        if (!image.closest('#gg-meta-hud, #gg-existing-metas')) return;
        event.preventDefault();
        event.stopPropagation();
        openImageLightbox(image.src);
    }, true);

    async function applyProxiedImageSrc(image, url) {
        if (url.startsWith('data:')) {
            image.src = url;
            return;
        }
        const blob = await fetchImageBlob(url);
        if (!image.isConnected) return;
        if (blob) {
            const objectUrl = URL.createObjectURL(blob);
            image.dataset.ggObjectUrl = objectUrl;
            image.src = objectUrl;
        } else {
            // Fallback: try a direct load. It may still be blocked by the
            // host's CORP header, but it's better than showing nothing.
            image.src = url;
        }
    }

    // Loads every deferred (data-gg-src) image under `root` through the
    // GM_xmlhttpRequest proxy right away (no lazy observer).
    function loadDeferredImages(root) {
        root?.querySelectorAll('.gg-meta-image[data-gg-src]').forEach(image => {
            const src = image.dataset.ggSrc;
            delete image.dataset.ggSrc;
            if (src) applyProxiedImageSrc(image, src);
        });
    }

    function revokeImageObjectUrls(root) {
        root?.querySelectorAll('.gg-meta-image[data-gg-object-url]').forEach(image => {
            URL.revokeObjectURL(image.dataset.ggObjectUrl);
            delete image.dataset.ggObjectUrl;
        });
    }

    function resetHudImageLoading(container) {
        hudImageObserver?.disconnect();
        hudImageObserver = null;
        container?.querySelectorAll('.gg-meta-image[src]').forEach(image => {
            if (image.dataset.ggObjectUrl) {
                URL.revokeObjectURL(image.dataset.ggObjectUrl);
                delete image.dataset.ggObjectUrl;
            }
            image.removeAttribute('src');
        });
    }

    function startHudImageLoading(container) {
        const images = Array.from(container?.querySelectorAll('.gg-meta-image[data-gg-src]') || []);
        if (images.length === 0) return;
        let pendingImageCount = images.length;

        const loadImage = image => {
            const src = image.dataset.ggSrc;
            if (!src) return;
            delete image.dataset.ggSrc;
            hudImageObserver?.unobserve(image);
            applyProxiedImageSrc(image, src);
            pendingImageCount -= 1;
            if (pendingImageCount === 0) {
                hudImageObserver?.disconnect();
                hudImageObserver = null;
            }
        };

        if (typeof IntersectionObserver !== 'function') {
            images.forEach(loadImage);
            return;
        }

        hudImageObserver = new IntersectionObserver(entries => {
            entries.forEach(entry => {
                if (entry.isIntersecting) loadImage(entry.target);
            });
        }, {
            root: container,
            rootMargin: `${HUD_IMAGE_PRELOAD_MARGIN_PX}px 0px`
        });
        images.forEach(image => hudImageObserver.observe(image));
    }

    function renderStaticTags(tags) {
        return (Array.isArray(tags) ? tags : [])
            .map(tag => `<span class="gg-tag-static">${escapeHtml(tag)}</span>`)
            .join('');
    }

    function getEventElementTarget(event) {
        const target = event && event.target;
        if (!target) return null;
        if (target.nodeType === 1) return target;
        return target.parentElement || null;
    }

    function loadActiveScopes() {
        try {
            const storedScopes = JSON.parse(readStoredValue(ACTIVE_SCOPES_STORAGE_KEY) || 'null');
            if (Array.isArray(storedScopes)) {
                const knownScopes = storedScopes
                    .map(scope => normalizeScope(scope, null))
                    .filter(Boolean);
                // "segment" is newer than the stored list: follow "road" when unknown.
                if (!storedScopes.includes('segment') && knownScopes.includes('road')) knownScopes.push('segment');
                if (knownScopes.length > 0) return new Set(knownScopes);
            }
        } catch (err) {
            console.warn('[BetterMetas] Invalid active scopes:', err);
        }
        return new Set(ALL_SCOPES);
    }

    // Unlike scopes (default = all selected = show all), the default tag
    // filter is an EMPTY set, which also means "show all" (see isTagActive).
    function loadActiveTags() {
        try {
            const storedTags = JSON.parse(readStoredValue(ACTIVE_TAGS_STORAGE_KEY) || 'null');
            if (Array.isArray(storedTags)) {
                const knownTags = storedTags.filter(tag => TAG_PRESETS.includes(tag));
                return new Set(knownTags);
            }
        } catch (err) {
            console.warn('[BetterMetas] Invalid active tags:', err);
        }
        return new Set();
    }




    // --- Styles ---
    // The stylesheet lives in styles.css and is served by local-server.js like the
    // data files: edits show up on the next page load, no rebuild. The last copy is
    // cached so the UI is styled immediately and still works if the server is down.
    // Until a stylesheet is available the UI is kept hidden (no unstyled flash).
    const STYLES_FILE = 'styles.css';
    const STYLES_CACHE_STORAGE_KEY = 'gg_styles_cache';
    const STYLES_PENDING_CLASS = 'gg-styles-pending';
    const PENDING_STYLES = `
        html.${STYLES_PENDING_CLASS} #gg-meta-hud,
        html.${STYLES_PENDING_CLASS} #gg-modal-backdrop,
        html.${STYLES_PENDING_CLASS} #gg-meta-preview-popup,
        html.${STYLES_PENDING_CLASS} #gg-dialog-modal,
        html.${STYLES_PENDING_CLASS} #gg-meta-modal,
        html.${STYLES_PENDING_CLASS} #gg-settings-modal,
        html.${STYLES_PENDING_CLASS} #gg-meta-admin-modal { display: none !important; }
    `;
    let stylesElement = null;

    function applyStyles(css) {
        if (!stylesElement) {
            stylesElement = document.createElement('style');
            (document.head || document.documentElement).appendChild(stylesElement);
        }
        stylesElement.textContent = css;
        document.documentElement.classList.remove(STYLES_PENDING_CLASS);
    }

    async function addStyles() {
        const cachedCss = readStoredValue(STYLES_CACHE_STORAGE_KEY);
        if (cachedCss) {
            applyStyles(cachedCss);
        } else {
            const pendingStyle = document.createElement('style');
            pendingStyle.textContent = PENDING_STYLES;
            (document.head || document.documentElement).appendChild(pendingStyle);
            document.documentElement.classList.add(STYLES_PENDING_CLASS);
        }

        try {
            const response = await requestRawText(getRawFileUrl(STYLES_FILE), STYLES_FILE);
            if (response.status !== 200 || !response.responseText) {
                throw new Error(`${STYLES_FILE} HTTP ${response.status}`);
            }
            if (response.responseText !== cachedCss) {
                applyStyles(response.responseText);
                writeStoredValue(STYLES_CACHE_STORAGE_KEY, response.responseText);
            }
        } catch (err) {
            console.warn(`[BetterMetas] Could not load ${STYLES_FILE}${cachedCss ? ', using the cached copy' : ''}:`, err);
        }
    }

    function getSavedHudSize() {
        try {
            const savedSize = JSON.parse(readStoredValue(HUD_SIZE_STORAGE_KEY) || 'null');
            if (
                savedSize &&
                Number.isFinite(savedSize.width) &&
                Number.isFinite(savedSize.height) &&
                savedSize.width >= HUD_MIN_WIDTH &&
                savedSize.height >= HUD_MIN_HEIGHT
            ) {
                return savedSize;
            }
        } catch (err) {
            console.warn('[BetterMetas] Invalid saved HUD size:', err);
        }

        return null;
    }

    function applyHudSize(hud, size) {
        if (size) {
            hud.style.width = `${size.width}px`;
            hud.style.height = `${size.height}px`;
            hud.style.maxWidth = 'calc(100vw - 1rem)';
            hud.style.maxHeight = 'calc(100vh - 1rem)';
        } else {
            hud.style.width = '';
            hud.style.height = '';
            hud.style.maxWidth = '';
            hud.style.maxHeight = '';
        }
    }

    function getCurrentHudSize(hud) {
        const rect = hud.getBoundingClientRect();
        const computed = window.getComputedStyle(hud);
        return {
            width: Math.round(parseFloat(computed.width) || rect.width),
            height: Math.round(parseFloat(computed.height) || rect.height)
        };
    }

    function getSavedHudPosition() {
        try {
            const savedPosition = JSON.parse(readStoredValue(HUD_POSITION_STORAGE_KEY) || 'null');
            if (
                savedPosition &&
                Number.isFinite(savedPosition.left) &&
                Number.isFinite(savedPosition.top)
            ) {
                return savedPosition;
            }
        } catch (err) {
            console.warn('[BetterMetas] Invalid saved HUD position:', err);
        }

        return null;
    }

    function applyHudPosition(hud, position) {
        if (position) {
            hud.style.left = `${position.left}px`;
            hud.style.top = `${position.top}px`;
            hud.style.right = 'auto';
            hud.style.transform = 'none';
        } else {
            hud.style.left = '';
            hud.style.top = '';
            hud.style.right = '';
            hud.style.transform = '';
        }
    }

    function clampHudPosition(left, top, hud) {
        const rect = hud.getBoundingClientRect();
        const maxLeft = Math.max(0, window.innerWidth - rect.width);
        const maxTop = Math.max(0, window.innerHeight - rect.height);
        return {
            left: Math.min(Math.max(0, left), maxLeft),
            top: Math.min(Math.max(0, top), maxTop)
        };
    }

    function saveHudPosition(hud) {
        const rect = hud.getBoundingClientRect();
        writeStoredValue(HUD_POSITION_STORAGE_KEY, JSON.stringify({
            left: Math.round(rect.left),
            top: Math.round(rect.top)
        }));
    }

    // Every meta comes from the local data files; this guards against an id that is
    // not part of the loaded data.
    function isUserMeta(metaId) {
        return userMetaIds.has(metaId);
    }

    function countAdminMetaLocations(metaId) {
        return Object.values(userLocationMap).filter(entry => getLocationMetaIds(entry).includes(metaId)).length;
    }

    function removeMetaIdFromLocationEntries(locations, metaId) {
        let changed = false;
        Object.keys(locations || {}).forEach(panoid => {
            const entry = normalizeLocationEntry(locations[panoid]);
            if (!entry) return;
            const filteredMetaIds = entry.metas.filter(id => id !== metaId);
            if (filteredMetaIds.length === entry.metas.length) return;

            changed = true;
            if (filteredMetaIds.length === 0) {
                delete locations[panoid];
            } else {
                locations[panoid] = { ...entry, metas: filteredMetaIds };
            }
        });
        return changed;
    }

    const LANDSCAPE_FORMS = {
        create: { box: 'meta-landscape-import', btn: 'meta-landscape-btn', file: 'meta-landscape-file', scope: 'meta-scope' },
        admin: { box: 'gg-admin-landscape-import', btn: 'gg-admin-landscape-btn', file: 'gg-admin-landscape-file', scope: 'gg-admin-meta-scope' }
    };
    // Centre computed from an imported file, waiting for the form to be saved.
    const landscapeCenterState = { create: null, admin: null };

    // The import button is only shown for 100km / 10km / 1km.
    function refreshLandscapeImportUi(formKey) {
        const cfg = LANDSCAPE_FORMS[formKey];
        const box = document.getElementById(cfg.box);
        if (!box) return;

        const scope = document.getElementById(cfg.scope)?.value;
        const visible = !!scope && isLandscapeScope(scope);
        box.style.display = visible ? '' : 'none';
        if (!visible) landscapeCenterState[formKey] = null;
    }

    function initLandscapeImport(formKey) {
        const cfg = LANDSCAPE_FORMS[formKey];
        const btn = document.getElementById(cfg.btn);
        const fileInput = document.getElementById(cfg.file);
        if (!btn || !fileInput) return;

        btn.addEventListener('click', () => {
            fileInput.value = '';
            fileInput.click();
        });
        fileInput.addEventListener('change', async () => {
            const file = fileInput.files && fileInput.files[0];
            if (!file) return;
            try {
                const points = extractLandscapePoints(JSON.parse(await file.text()));
                if (points.length === 0) {
                    throw new Error('No coordinates found. Expected { "customCoordinates": [{ "lat": ..., "lng": ... }] }.');
                }
                const median = computeGeometricMedian(points);
                const countryInfo = await geocodeCountryForCoordinates(median.lat, median.lng);
                landscapeCenterState[formKey] = { points, ...countryInfo };
            } catch (err) {
                console.error('[BetterMetas] Landscape import failed:', err);
                landscapeCenterState[formKey] = null;
                await showToolAlert('Import Failed', err.message || String(err));
            }
            refreshLandscapeImportUi(formKey);
        });
    }

    function setAdminScopeSelection(scope) {
        const normalizedScope = normalizeScope(scope);
        const scopeContainer = document.getElementById('gg-admin-scope-presets');
        const scopeInput = document.getElementById('gg-admin-meta-scope');
        if (!scopeContainer || !scopeInput) return;

        scopeInput.value = normalizedScope;
        refreshLandscapeImportUi('admin');
        scopeContainer.querySelectorAll('.gg-tag-pill').forEach(pill => {
            pill.classList.toggle('gg-tag-selected', pill.dataset.value === normalizedScope);
        });
    }

    function setAdminTagSelection(tags) {
        const normalizedTags = normalizeTags(tags);
        const tagContainer = document.getElementById('gg-admin-tag-presets');
        const tagInput = document.getElementById('gg-admin-meta-tags');
        if (!tagContainer || !tagInput) return;

        tagInput.value = normalizedTags.join(', ');
        tagContainer.querySelectorAll('.gg-tag-pill').forEach(pill => {
            pill.classList.toggle('gg-tag-selected', normalizedTags.includes(pill.textContent.trim().toLowerCase()));
        });
    }

    function updateAdminImagePreview() {
        const preview = document.getElementById('gg-admin-image-preview');
        const imageInput = document.getElementById('gg-admin-meta-image');
        if (preview) {
            preview.removeAttribute('src');
            preview.style.display = 'none';
        }
        if (imageInput?.matches(':hover')) showAdminImageUrlPreview();
    }

    function showAdminImageUrlPreview() {
        const imageInput = document.getElementById('gg-admin-meta-image');
        const previewPopup = document.getElementById('gg-meta-preview-popup');
        const modal = document.getElementById('gg-meta-admin-modal');
        if (!imageInput || !previewPopup || !modal) return;

        const safeUrl = getSafeImageUrl(imageInput.value);
        if (!safeUrl) {
            hideAdminImageUrlPreview();
            return;
        }

        delete previewPopup.dataset.ggPreviewCleanupId;
        previewPopup.dataset.ggPreviewMode = 'image-url';
        previewPopup.classList.add('gg-image-url-preview');
        revokeImageObjectUrls(previewPopup);
        previewPopup.innerHTML = `<img class="gg-meta-image" alt="">`;
        const previewImage = previewPopup.querySelector('img');
        previewImage?.addEventListener('load', positionAdminImageUrlPreview, { once: true });
        previewImage?.addEventListener('error', hideAdminImageUrlPreview, { once: true });
        if (previewImage) applyProxiedImageSrc(previewImage, safeUrl);
        positionAdminImageUrlPreview();
    }

    function positionAdminImageUrlPreview() {
        const imageInput = document.getElementById('gg-admin-meta-image');
        const previewPopup = document.getElementById('gg-meta-preview-popup');
        const modal = document.getElementById('gg-meta-admin-modal');
        if (!imageInput || !previewPopup || !modal) return;

        const modalRect = modal.getBoundingClientRect();
        const inputRect = imageInput.getBoundingClientRect();
        const leftPos = Math.max(8, modalRect.left - 290);

        previewPopup.style.left = `${leftPos}px`;
        previewPopup.classList.add('gg-visible');

        const height = previewPopup.offsetHeight;
        const adjustedTop = Math.min(
            Math.max(8, inputRect.top + (inputRect.height / 2) - (height / 2)),
            Math.max(8, window.innerHeight - height - 8)
        );
        previewPopup.style.top = `${adjustedTop}px`;
    }

    function hideAdminImageUrlPreview() {
        const previewPopup = document.getElementById('gg-meta-preview-popup');
        if (!previewPopup) return;

        previewPopup.classList.remove('gg-visible');
        if (previewPopup.dataset.ggPreviewMode !== 'image-url') return;

        const cleanupId = `${Date.now()}-${Math.random()}`;
        previewPopup.dataset.ggPreviewCleanupId = cleanupId;
        setTimeout(() => {
            if (
                previewPopup.dataset.ggPreviewCleanupId !== cleanupId ||
                previewPopup.dataset.ggPreviewMode !== 'image-url' ||
                previewPopup.classList.contains('gg-visible')
            ) {
                return;
            }

            const objectUrl = previewPopup.querySelector('img')?.dataset.ggObjectUrl;
            if (objectUrl) URL.revokeObjectURL(objectUrl);
            previewPopup.classList.remove('gg-image-url-preview');
            previewPopup.innerHTML = '';
            delete previewPopup.dataset.ggPreviewMode;
            delete previewPopup.dataset.ggPreviewCleanupId;
        }, 220);
    }

    function formatLocationValue(value) {
        if (Array.isArray(value)) return value.filter(Boolean).join(', ');
        return value || '';
    }

    function getAdminMetaLinkedLocations(metaId) {
        const linkedLocations = [];
        const metaScope = getMetaById(metaId)?.scope;
        Object.entries(userLocationMap).forEach(([panoid, rawEntry]) => {
            const entry = normalizeLocationEntry(rawEntry);
            if (!entry || !getLocationMetaIds(entry).includes(metaId)) return;
            linkedLocations.push({
                panoid,
                ...entry,
                scope: metaScope,
                displayCountry: entry.country || entry.nominatimCountry || ''
            });
        });
        return linkedLocations.sort((a, b) => compareAdminText(formatAdminLocationLabel(a), formatAdminLocationLabel(b)));
    }

    function formatAdminLocationLabel(location) {
        // Distance scopes (100km / 10km / 1km) are located by coordinates, not by name:
        // "<lat> <lng> (<scope>)", so they are told apart from countrywide / region / city / road.
        if (isLandscapeScope(location.scope)) {
            const lat = normalizeCoordinate(location.lat);
            const lng = normalizeCoordinate(location.lng);
            if (lat !== null && lng !== null) {
                return `${lat.toFixed(6)} ${lng.toFixed(6)} (${normalizeScope(location.scope)})`;
            }
        }

        if (normalizeScope(location.scope) === 'segment') {
            const formatPoint = (latValue, lngValue) => {
                const lat = normalizeCoordinate(latValue);
                const lng = normalizeCoordinate(lngValue);
                return lat !== null && lng !== null ? `${lat.toFixed(6)} ${lng.toFixed(6)}` : '';
            };
            const points = [
                formatPoint(location.lat, location.lng),
                formatPoint(location.latB, location.lngB)
            ].filter(Boolean).join(' \u2192 ');
            // The roads are listed apart (collapsed) by renderAdminLinkedLocations.
            return `${location.displayCountry || 'Unknown country'}, ${points || 'segment'}`;
        }

        const parts = [
            location.displayCountry || 'Unknown country',
            formatLocationValue(location.region),
            formatLocationValue(location.city),
            formatLocationValue(location.road)
        ].filter(Boolean);
        return parts.length ? parts.join(', ') : location.panoid;
    }

    function getGoogleMapsUrlForLocation(location) {
        const lat = normalizeCoordinate(location.lat);
        const lng = normalizeCoordinate(location.lng);
        if (lat !== null && lng !== null) {
            return `https://www.google.com/maps?q=${encodeURIComponent(`${lat},${lng}`)}`;
        }

        const query = formatAdminLocationLabel(location);
        return `https://www.google.com/maps/search/?api=1&query=${encodeURIComponent(query)}`;
    }

    function renderAdminLinkedLocations(metaId) {
        const container = document.getElementById('gg-admin-linked-locations');
        if (!container) return;

        const linkedLocations = getAdminMetaLinkedLocations(metaId);
        if (linkedLocations.length === 0) {
            container.innerHTML = '<div class="gg-form-hint gg-list-empty-state">No linked locations found.</div>';
            return;
        }

        // Segments: the roads sit in a dropdown, collapsed by default.
        const renderSegmentRoads = location => {
            if (normalizeScope(location.scope) !== 'segment') return '';
            const roads = getSegmentRoadList(location.road);
            if (roads.length === 0) return '';
            return `
                <details class="gg-admin-location-roads">
                    <summary>${roads.length} road${roads.length > 1 ? 's' : ''}</summary>
                    <ul>${roads.map(road => `
                        <li>
                            <span class="gg-admin-location-road-name">${escapeHtml(road)}</span>
                            <button type="button" class="gg-admin-location-remove gg-admin-road-remove" data-panoid="${escapeHtml(location.panoid)}" data-road="${escapeHtml(road)}" title="Remove this road" aria-label="Remove this road">
                                <svg aria-hidden="true" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><line x1="18" y1="6" x2="6" y2="18"></line><line x1="6" y1="6" x2="18" y2="18"></line></svg>
                            </button>
                        </li>`).join('')}</ul>
                </details>`;
        };

        // Re-rendering (after a road removal, a sync...) must not collapse the dropdowns
        // the user opened: remember them, for the same meta only.
        const openRoadPanoids = new Set();
        if (container.dataset.metaId === metaId) {
            container.querySelectorAll('.gg-admin-location-item').forEach(item => {
                if (item.querySelector('.gg-admin-location-roads[open]')) {
                    openRoadPanoids.add(item.querySelector('.gg-admin-location-remove')?.dataset.panoid);
                }
            });
        }
        container.dataset.metaId = metaId;

        container.innerHTML = linkedLocations.map(location => `
            <div class="gg-admin-location-item">
                <button type="button" class="gg-admin-location-open" data-map-url="${escapeHtml(getGoogleMapsUrlForLocation(location))}" title="Open in Google Maps">
                    <svg class="gg-admin-location-pin" aria-hidden="true" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M20 10c0 5-8 12-8 12S4 15 4 10a8 8 0 1 1 16 0Z"></path><circle cx="12" cy="10" r="2.5"></circle></svg>
                    <span class="gg-admin-location-label">${escapeHtml(formatAdminLocationLabel(location))}</span>
                    <svg class="gg-admin-location-external" aria-hidden="true" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M15 3h6v6"></path><path d="M10 14 21 3"></path><path d="M18 13v6a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h6"></path></svg>
                </button>
                <button type="button" class="gg-admin-location-remove" data-panoid="${escapeHtml(location.panoid)}" title="Unlink this location from the meta" aria-label="Unlink this location from the meta">
                    <svg aria-hidden="true" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><line x1="18" y1="6" x2="6" y2="18"></line><line x1="6" y1="6" x2="18" y2="18"></line></svg>
                </button>
                ${renderSegmentRoads(location)}
            </div>
        `).join('');

        container.querySelectorAll('.gg-admin-location-item').forEach(item => {
            const panoid = item.querySelector('.gg-admin-location-remove')?.dataset.panoid;
            const details = item.querySelector('.gg-admin-location-roads');
            if (details && openRoadPanoids.has(panoid)) details.open = true;
        });

        container.querySelectorAll('.gg-admin-location-open').forEach(item => {
            item.addEventListener('click', (e) => {
                e.preventDefault();
                e.stopPropagation();
                const url = item.dataset.mapUrl;
                if (url) window.open(url, '_blank', 'noopener,noreferrer');
            });
        });

        container.querySelectorAll('.gg-admin-location-remove').forEach(btn => {
            btn.addEventListener('click', (e) => {
                e.preventDefault();
                e.stopPropagation();
                if (btn.dataset.road) removeRoadFromAdminSegment(metaId, btn.dataset.panoid, btn.dataset.road);
                else unlinkMetaFromAdminLocation(metaId, btn.dataset.panoid);
            });
        });
    }

    function getSelectedAdminMeta() {
        if (!selectedAdminMetaId) return null;
        return getMetaById(selectedAdminMetaId) || null;
    }

    function applyAdminMetaLocally(meta) {
        const normalizedMeta = normalizeMetaList([meta])[0];
        if (!normalizedMeta) return false;

        let found = false;
        metasData = metasData.map(existingMeta => {
            if (existingMeta.id !== normalizedMeta.id) return existingMeta;
            found = true;
            return { ...existingMeta, ...normalizedMeta };
        });

        if (!found) metasData.unshift(normalizedMeta);
        rebuildMetaIndexes();
        return true;
    }

    function applyAdminDeleteLocally(metaId) {
        userLocationMap = { ...userLocationMap };
        removeMetaIdFromLocationEntries(userLocationMap, metaId);
        metasData = metasData.filter(meta => meta.id !== metaId);
        rebuildMetaIndexes();
        userMetaIds.delete(metaId);
        selectedAdminMetaId = null;
        proximityIndexDirty = true;
        if (currentPanoid) refreshDisplay();
    }

    // Entries are copied (not shared) because a link/unlink can now touch several
    // entries (<panoid>, <panoid>__<scope>, or a matched entry of another panoid),
    // and the previous map is kept as a rollback snapshot.
    function copyLocationMapForPanoid(locations, panoid) {
        const copy = {};
        Object.entries(locations || {}).forEach(([key, entry]) => {
            if (Array.isArray(entry)) {
                copy[key] = [...entry];
            } else if (entry && typeof entry === 'object') {
                copy[key] = { ...entry, metas: Array.isArray(entry.metas) ? [...entry.metas] : entry.metas };
            } else {
                copy[key] = entry;
            }
        });
        if (copy[panoid]) copy[panoid] = normalizeLocationEntry(copy[panoid]);
        return copy;
    }

    function createLocalDataSnapshot() {
        return {
            userLocationMap,
            metasData,
            userMetaIds: new Set(userMetaIds),
            pendingLocalChanges: structuredClone(loadPendingLocalChanges())
        };
    }

    function restoreLocalDataSnapshot(snapshot) {
        if (!snapshot) return;

        userLocationMap = snapshot.userLocationMap;
        proximityIndexDirty = true;
        metasData = snapshot.metasData;
        rebuildMetaIndexes();
        userMetaIds = snapshot.userMetaIds;
        savePendingLocalChanges(snapshot.pendingLocalChanges || getEmptyPendingLocalChanges());

        renderAdminMetas(document.getElementById('gg-admin-search')?.value || '');
        if (selectedAdminMetaId) openAdminMetaDetails(selectedAdminMetaId);
        if (currentPanoid) refreshDisplay();
    }

    // Reads the admin form without side effects (the image is only imported later).
    function readAdminMetaForm() {
        const readValue = id => (document.getElementById(id)?.value || '').trim();
        return {
            title: readValue('gg-admin-meta-title'),
            description: readValue('gg-admin-meta-desc'),
            rawImage: readValue('gg-admin-meta-image'),
            scope: normalizeScope(readValue('gg-admin-meta-scope')),
            tags: normalizeTags(readValue('gg-admin-meta-tags'))
        };
    }

    // Builds the edited meta; a remote image URL is imported to disk here.
    async function buildAdminMeta(existingMeta, form) {
        const updatedMeta = {
            ...existingMeta,
            title: form.title,
            description: form.description,
            imageUrl: await resolveImageForSave(form.rawImage, getCountrySlugForMeta(existingMeta)),
            scope: form.scope,
            tags: form.tags
        };

        // Only bump 'updatedAt' when something actually changed, so a no-op
        // save keeps the previous timestamp (and is skipped by the
        // "IfChanged" file write).
        const hasChanged = ['title', 'description', 'imageUrl', 'scope', 'tags'].some(key => {
            const before = key === 'imageUrl' ? (existingMeta[key] || null) : existingMeta[key];
            return JSON.stringify(before) !== JSON.stringify(updatedMeta[key]);
        });
        if (hasChanged) updatedMeta.updatedAt = new Date().toISOString();

        return updatedMeta;
    }

    function getEmptyPendingLocalChanges() {
        return { metas: [], locations: {} };
    }

    function normalizePendingLocalChanges(value) {
        const normalized = getEmptyPendingLocalChanges();
        if (!value || typeof value !== 'object') return normalized;

        normalized.metas = normalizeMetaList(value.metas);

        normalized.locations = normalizeLocationMap(value.locations);

        return normalized;
    }

    function loadPendingLocalChanges() {
        try {
            return normalizePendingLocalChanges(JSON.parse(readStoredValue(PENDING_LOCAL_CHANGES_STORAGE_KEY) || 'null'));
        } catch (err) {
            console.warn('[BetterMetas] Invalid pending local changes:', err);
            return getEmptyPendingLocalChanges();
        }
    }

    function savePendingLocalChanges(pending) {
        const normalized = normalizePendingLocalChanges(pending);
        if (normalized.metas.length === 0 && Object.keys(normalized.locations).length === 0) {
            clearStoredValue(PENDING_LOCAL_CHANGES_STORAGE_KEY);
            return;
        }

        writeStoredValue(PENDING_LOCAL_CHANGES_STORAGE_KEY, JSON.stringify(normalized));
    }

    function mergePendingLocalChangesInto(userMetas, userLocations) {
        const pending = loadPendingLocalChanges();
        const confirmedMetaIds = new Set((userMetas || []).map(meta => meta.id).filter(Boolean));

        pending.metas.forEach(meta => {
            if (!confirmedMetaIds.has(meta.id)) {
                userMetas.push(meta);
                confirmedMetaIds.add(meta.id);
            }
        });

        Object.keys(pending.locations).forEach(panoid => {
            userLocations[panoid] = mergeLocationEntries(userLocations[panoid], pending.locations[panoid]);
        });

        return pending;
    }

    function pruneConfirmedPendingLocalChanges(rawUserMetas, rawUserLocations) {
        const pending = loadPendingLocalChanges();
        const rawMetaIds = new Set((rawUserMetas || []).map(meta => meta.id).filter(Boolean));

        const pruned = getEmptyPendingLocalChanges();
        pruned.metas = pending.metas.filter(meta => !rawMetaIds.has(meta.id));

        Object.keys(pending.locations).forEach(panoid => {
            const rawMetaIdsForLocation = new Set(getLocationMetaIds(rawUserLocations[panoid]));
            const allPendingMetaIds = getLocationMetaIds(pending.locations[panoid]);
            const pendingMetaIds = allPendingMetaIds.filter(id => !rawMetaIdsForLocation.has(id));
            // A segment already saved without its point B / last road is still pending.
            const geometryPending = !isSegmentGeometryConfirmed(rawUserLocations[panoid], pending.locations[panoid]);

            if (pendingMetaIds.length > 0 || geometryPending) {
                const keptMetaIds = pendingMetaIds.length > 0 ? pendingMetaIds : allPendingMetaIds;
                const pendingEntry = Array.isArray(pending.locations[panoid])
                    ? { metas: keptMetaIds }
                    : { ...pending.locations[panoid], metas: keptMetaIds };
                pruned.locations[panoid] = pendingEntry;
            }
        });

        savePendingLocalChanges(pruned);
    }

    // Records the links in the pending changes under the SAME keys that were used in
    // the live map (usedKeys), with a copy of the live entry's fields. Pending entries
    // are merged over the live map by key, so a pending entry must never carry
    // different region/city/road values than the entry it lands on.
    function addLiveLinksToPending(pending, liveLocations, usedKeys) {
        usedKeys.forEach((key, metaId) => {
            const liveEntry = liveLocations[key];
            if (!liveEntry) return;
            const pendingEntry = pending.locations[key] || { ...normalizeLocationEntry(liveEntry), metas: [] };
            pendingEntry.metas = Array.from(new Set([...getLocationMetaIds(pendingEntry), metaId]));
            // A segment entry changes after its creation (point B, more roads): the pending
            // copy follows the live entry.
            if (liveEntry.segment) {
                pendingEntry.segment = true;
                pendingEntry.road = liveEntry.road;
                pendingEntry.latB = liveEntry.latB;
                pendingEntry.lngB = liveEntry.lngB;
            }
            pending.locations[key] = pendingEntry;
        });
    }

    function rememberLocalLocationLinks(usedKeys) {
        const pending = loadPendingLocalChanges();
        addLiveLinksToPending(pending, userLocationMap, usedKeys);
        savePendingLocalChanges(pending);
    }

    function forgetLocalLocationLinks(panoid, metaIds) {
        const pending = loadPendingLocalChanges();
        removeMetaIdsFromPanoidLocations(pending.locations, panoid, metaIds);
        savePendingLocalChanges(pending);
    }

    function rememberLocalMeta(meta, usedKeys) {
        const pending = loadPendingLocalChanges();
        if (!pending.metas.some(existing => existing.id === meta.id)) {
            pending.metas.push(meta);
        }
        addLiveLinksToPending(pending, userLocationMap, usedKeys);
        savePendingLocalChanges(pending);
    }

    function applyLocalLocationLinks(panoid, metaIds, scopeOverride = null) {
        currentPanoid = panoid;
        nextPanoid = null;
        updateStatus(`ID: ${panoid.substring(0,12)}...`);
        userLocationMap = copyLocationMapForPanoid(userLocationMap, panoid);
        const usedKeys = addMetaIdsToLocationMap(userLocationMap, panoid, metaIds, scopeOverride);
        proximityIndexDirty = true;
        rememberLocalLocationLinks(usedKeys);
        debugLog('[BetterMetas] Applied local location links:', {
            panoid,
            metaIds,
            usedKeys: Object.fromEntries(usedKeys),
            linkedMetaIds: Array.from(getLinkedMetaIdsForPanoid(userLocationMap, panoid))
        });
        refreshDisplay();
    }

    function applyLocalLandscapeCenters(metaId, centers) {
        const updatedMap = { ...userLocationMap };
        const keys = setLandscapeCenterEntries(updatedMap, metaId, centers);
        userLocationMap = updatedMap;
        proximityIndexDirty = true;

        const pending = loadPendingLocalChanges();
        removeLandscapeCenterEntry(pending.locations, metaId);
        keys.forEach(key => {
            pending.locations[key] = { ...updatedMap[key] };
        });
        savePendingLocalChanges(pending);
    }

    function applyLocalLandscapeCenterRemoval(metaId) {
        const updatedMap = { ...userLocationMap };
        removeLandscapeCenterEntry(updatedMap, metaId);
        userLocationMap = updatedMap;
        proximityIndexDirty = true;

        const pending = loadPendingLocalChanges();
        removeLandscapeCenterEntry(pending.locations, metaId);
        savePendingLocalChanges(pending);
    }

    // Live-map + pending-changes counterpart of relinkMetaForScopeChange.
    // Returns false (and changes nothing) if the meta is not linked to this location.
    function applyLocalScopeRelink(panoid, metaId, oldScope, newScope) {
        const updatedMap = copyLocationMapForPanoid(userLocationMap, panoid);
        const usedKeys = relinkMetaForScopeChange(updatedMap, panoid, metaId, oldScope, newScope);
        if (!usedKeys) return false;

        userLocationMap = updatedMap;
        proximityIndexDirty = true;

        const pending = loadPendingLocalChanges();
        Object.keys(pending.locations).forEach(key => {
            const remaining = getLocationMetaIds(pending.locations[key]).filter(id => id !== metaId);
            if (remaining.length === 0) {
                delete pending.locations[key];
            } else {
                pending.locations[key] = { ...pending.locations[key], metas: remaining };
            }
        });
        addLiveLinksToPending(pending, userLocationMap, usedKeys);
        savePendingLocalChanges(pending);
        return true;
    }

    function applyLocalLocationUnlinks(panoid, metaIds) {
        currentPanoid = panoid;
        nextPanoid = null;
        updateStatus(`ID: ${panoid.substring(0,12)}...`);
        userLocationMap = copyLocationMapForPanoid(userLocationMap, panoid);
        removeMetaIdsFromPanoidLocations(userLocationMap, panoid, metaIds);
        proximityIndexDirty = true;
        forgetLocalLocationLinks(panoid, metaIds);
        debugLog('[BetterMetas] Applied local location unlinks:', {
            panoid,
            metaIds,
            linkedMetaIds: Array.from(getLinkedMetaIdsForPanoid(userLocationMap, panoid))
        });
        refreshDisplay();
    }

    function applyLocalSavedMeta(meta, panoid) {
        currentPanoid = panoid;
        nextPanoid = null;
        updateStatus(`ID: ${panoid.substring(0,12)}...`);

        if (!getMetaById(meta.id)) {
            metasData = [meta, ...metasData];
            rebuildMetaIndexes();
        }

        userMetaIds.add(meta.id);
        userLocationMap = copyLocationMapForPanoid(userLocationMap, panoid);
        const usedKeys = addMetaIdsToLocationMap(userLocationMap, panoid, [meta.id], meta.scope);
        proximityIndexDirty = true;
        rememberLocalMeta(meta, usedKeys);
        debugLog('[BetterMetas] Applied local saved meta:', {
            panoid,
            metaId: meta.id,
            usedKeys: Object.fromEntries(usedKeys),
            linkedMetaIds: Array.from(getLinkedMetaIdsForPanoid(userLocationMap, panoid))
        });
        refreshDisplay();
    }

    function setControlsDisabled(container, disabled) {
        if (!container) return;

        container.classList.toggle('gg-operation-busy', disabled);
        container.querySelectorAll('button, input, textarea, select').forEach(control => {
            if (disabled) {
                control.dataset.ggWasDisabled = control.disabled ? '1' : '0';
                control.disabled = true;
            } else {
                control.disabled = control.dataset.ggWasDisabled === '1';
                delete control.dataset.ggWasDisabled;
            }
        });
    }

    function setButtonBusy(button, busy, busyText = '') {
        if (!button) return;

        if (busy) {
            if (!button.dataset.ggOriginalHtml) button.dataset.ggOriginalHtml = button.innerHTML;
            button.disabled = true;
            if (busyText) button.innerHTML = `<span class="gg-spinner"></span>${escapeHtml(busyText)}`;
            return;
        }

        if (button.dataset.ggOriginalHtml) {
            button.innerHTML = button.dataset.ggOriginalHtml;
            delete button.dataset.ggOriginalHtml;
        }
    }

    function beginMutationUi({ scope = null, button = null, busyText = 'Saving...', statusText = '' } = {}) {
        if (activeMutationCount > 0) {
            updateStatus('Finishing previous change...');
            return null;
        }

        activeMutationCount += 1;
        if (statusText) updateStatus(statusText);
        if (scope) setControlsDisabled(scope, true);
        setButtonBusy(button, true, busyText);

        return ({ buttonText = null, restoreButton = true } = {}) => {
            if (buttonText && button) {
                button.textContent = buttonText;
                delete button.dataset.ggOriginalHtml;
            } else if (restoreButton) {
                setButtonBusy(button, false);
            }
            if (scope) setControlsDisabled(scope, false);
            activeMutationCount = Math.max(0, activeMutationCount - 1);
        };
    }

    // Skeleton shared by the changes that are applied locally first and then written
    // to disk: busy UI, rollback snapshot, failure alert. `run` does the work and
    // throws on failure; the local state is then restored and the user is told.
    // `prepare` runs first, under the busy UI (e.g. waiting for geocoding).
    // Returns null if another change is still running, otherwise whether it succeeded.
    async function runMutation({ ui, failTitle, prepare = null, run }) {
        const finishUi = beginMutationUi(ui);
        if (!finishUi) return null;

        try {
            if (prepare) await prepare();
            const snapshot = createLocalDataSnapshot();
            try {
                await run();
                return true;
            } catch (err) {
                console.error(err);
                restoreLocalDataSnapshot(snapshot);
                await showToolAlert(failTitle, err.message || String(err));
                updateStatus(failTitle);
                return false;
            }
        } finally {
            finishUi();
        }
    }

    function scheduleBackgroundDataRefresh(delay = DATA_REFRESH_AFTER_SAVE_MS) {
        clearTimeout(backgroundRefreshTimer);
        backgroundRefreshTimer = setTimeout(() => {
            backgroundRefreshTimer = null;
            fetchLocationData();
        }, delay);
    }

    function setElementDisplay(id, display) {
        const el = document.getElementById(id);
        if (el) el.style.display = display;
    }

    function showBackdrop() {
        const backdrop = document.getElementById('gg-modal-backdrop');
        if (backdrop) backdrop.classList.add('gg-visible');
    }

    function hideBackdrop() {
        const backdrop = document.getElementById('gg-modal-backdrop');
        if (backdrop) backdrop.classList.remove('gg-visible');
    }

    function showMetaModal() {
        hideSettingsModal();
        hideAdminModal();
        setElementDisplay('gg-meta-modal', 'block');
        showBackdrop();
    }

    function showSettingsModal() {
        hideMetaModal();
        hideAdminModal();
        setElementDisplay('gg-settings-modal', 'block');
        showBackdrop();
    }

    function showAdminModal() {
        hideSettingsModal();
        hideMetaModal();
        setElementDisplay('gg-meta-admin-modal', 'block');
        showBackdrop();
    }

    function hideMetaModal() {
        setElementDisplay('gg-meta-modal', 'none');
        const list = document.getElementById('gg-existing-metas');
        if (list) resetIncrementalList(list);
        metaSearchTextById = null;
    }

    function hideSettingsModal() {
        setElementDisplay('gg-settings-modal', 'none');
    }

    function hideAdminModal() {
        setElementDisplay('gg-meta-admin-modal', 'none');
        const list = document.getElementById('gg-admin-meta-list');
        if (list) resetIncrementalList(list);
        metaSearchTextById = null;
    }

    function hideAllModals({ hideBackdropOverlay = true } = {}) {
        hideMetaModal();
        hideSettingsModal();
        hideAdminModal();
        if (hideBackdropOverlay) hideBackdrop();
    }

    function hidePreviewPopup() {
        const previewPopup = document.getElementById('gg-meta-preview-popup');
        if (!previewPopup) return;
        if (previewPopup.dataset.ggPreviewMode === 'image-url') {
            hideAdminImageUrlPreview();
            return;
        }
        previewPopup.classList.remove('gg-visible');
        const cleanupId = `${Date.now()}-${Math.random()}`;
        previewPopup.dataset.ggPreviewCleanupId = cleanupId;
        setTimeout(() => {
            if (
                previewPopup.dataset.ggPreviewCleanupId !== cleanupId ||
                previewPopup.classList.contains('gg-visible') ||
                previewPopup.dataset.ggPreviewMode === 'image-url'
            ) return;
            revokeImageObjectUrls(previewPopup);
            previewPopup.innerHTML = '';
            delete previewPopup.dataset.ggPreviewMode;
            delete previewPopup.dataset.ggPreviewCleanupId;
        }, 220);
    }

    const UI_CONTEXT_CLASSES = [
        'gg-context-normal',
        'gg-context-edit',
        'gg-context-pat',
        'gg-context-danger',
        'gg-context-neutral'
    ];

    function setUiContext(element, context = 'neutral') {
        if (!element) return;
        element.classList.remove(...UI_CONTEXT_CLASSES);
        element.classList.add(`gg-context-${context}`);
    }

    function getVisibleModalElementsForDialogBlur() {
        return ['gg-meta-modal', 'gg-settings-modal', 'gg-meta-admin-modal']
            .map(id => document.getElementById(id))
            .filter(modal => modal && window.getComputedStyle(modal).display !== 'none');
    }

    function showToolDialog({
        title = 'BetterMetas',
        message = '',
        confirmText = 'OK',
        cancelText = '',
        danger = false
    } = {}) {
        const dialog = document.getElementById('gg-dialog-modal');
        const backdrop = document.getElementById('gg-modal-backdrop');
        if (!dialog) return Promise.resolve(false);

        const backdropWasVisible = Boolean(backdrop && backdrop.classList.contains('gg-visible'));
        const backgroundModals = getVisibleModalElementsForDialogBlur();
        setUiContext(dialog, danger ? 'danger' : (cancelText ? 'normal' : 'neutral'));
        dialog.innerHTML = `
            <div class="gg-modal-header">${escapeHtml(title)}</div>
            <div class="gg-dialog-message">${escapeHtml(message)}</div>
            <div class="gg-dialog-actions">
                ${cancelText ? `<button class="gg-btn-secondary" id="gg-dialog-cancel">${escapeHtml(cancelText)}</button>` : ''}
                <button class="${danger ? 'gg-btn-danger' : 'gg-btn-primary'}" id="gg-dialog-confirm">${escapeHtml(confirmText)}</button>
            </div>
        `;

        showBackdrop();
        backgroundModals.forEach(modal => modal.classList.add('gg-modal-background-blurred'));
        dialog.style.display = 'block';

        return new Promise(resolve => {
            const close = (result) => {
                dialog.style.display = 'none';
                dialog.innerHTML = '';
                backgroundModals.forEach(modal => modal.classList.remove('gg-modal-background-blurred'));
                if (!backdropWasVisible) hideBackdrop();
                resolve(result);
            };

            const confirmBtn = dialog.querySelector('#gg-dialog-confirm');
            const cancelBtn = dialog.querySelector('#gg-dialog-cancel');

            confirmBtn.addEventListener('click', () => close(true), { once: true });
            if (cancelBtn) cancelBtn.addEventListener('click', () => close(false), { once: true });

            requestAnimationFrame(() => confirmBtn.focus());
        });
    }

    function showToolAlert(title, message, confirmText = 'OK') {
        return showToolDialog({ title, message, confirmText });
    }

    function showToolConfirm(title, message, {
        confirmText = 'OK',
        cancelText = 'Cancel',
        danger = false
    } = {}) {
        return showToolDialog({ title, message, confirmText, cancelText, danger });
    }

    // --- UI Construction ---
    // Typing in a form must not trigger the game's keyboard shortcuts.
    function keepKeysInsideInputs(container) {
        container.querySelectorAll('input, textarea').forEach(input => {
            ['keydown', 'keypress', 'keyup'].forEach(type => {
                input.addEventListener(type, event => event.stopPropagation());
            });
        });
    }

    function createHUD() {
        if (document.getElementById('gg-meta-hud')) return;

        // HUD
        const hud = document.createElement('div');
        hud.id = 'gg-meta-hud';
        applyHudSize(hud, getSavedHudSize());
        applyHudPosition(hud, getSavedHudPosition());
        hud.innerHTML = `
            <div class="gg-meta-title">
                <span>BetterMetas</span>
                <div class="gg-normal-controls">
                    <button id="gg-meta-admin-btn" title="Manage Metas" aria-label="Manage Metas">
                        <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><ellipse cx="12" cy="5" rx="9" ry="3"></ellipse><path d="M3 5v14c0 1.66 4.03 3 9 3s9-1.34 9-3V5"></path><path d="M3 12c0 1.66 4.03 3 9 3s9-1.34 9-3"></path></svg>
                    </button>
                    <button id="gg-settings-btn" title="Settings" aria-label="Open Settings">
                        <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="3"></circle><path d="M19.4 15a1.65 1.65 0 0 0 .33 1.82l.06.06a2 2 0 0 1 0 2.83 2 2 0 0 1-2.83 0l-.06-.06a1.65 1.65 0 0 0-1.82-.33 1.65 1.65 0 0 0-1 1.51V21a2 2 0 0 1-2 2 2 2 0 0 1-2-2v-.09A1.65 1.65 0 0 0 9 19.4a1.65 1.65 0 0 0-1.82.33l-.06.06a2 2 0 0 1-2.83 0 2 2 0 0 1 0-2.83l.06-.06a1.65 1.65 0 0 0 .33-1.82 1.65 1.65 0 0 0-1.51-1H3a2 2 0 0 1-2-2 2 2 0 0 1 2-2h.09A1.65 1.65 0 0 0 4.6 9a1.65 1.65 0 0 0-.33-1.82l-.06-.06a2 2 0 0 1 0-2.83 2 2 0 0 1 2.83 0l.06.06a1.65 1.65 0 0 0 1.82.33H9a1.65 1.65 0 0 0 1-1.51V3a2 2 0 0 1 2-2 2 2 0 0 1 2 2v.09a1.65 1.65 0 0 0 1 1.51 1.65 1.65 0 0 0 1.82-.33l.06-.06a2 2 0 0 1 2.83 0 2 2 0 0 1 0 2.83l-.06.06a1.65 1.65 0 0 0-.33 1.82V9a1.65 1.65 0 0 0 1.51 1H21a2 2 0 0 1 2 2 2 2 0 0 1-2 2h-.09a1.65 1.65 0 0 0-1.51 1z"></path></svg>
                    </button>

                    <button id="gg-meta-add-btn" title="Add or Link Metas" aria-label="Add or Link Metas">+ Add</button>
                </div>
            </div>
            <div class="gg-resize-grip" id="gg-resize-grip" title="Drag to resize" aria-label="Resize window">
                <svg xmlns="http://www.w3.org/2000/svg" width="10" height="10" viewBox="0 0 12 12" fill="none">
                    <path d="M11 1L1 11M11 5L5 11M11 9L9 11" stroke="currentColor" stroke-width="1.3" stroke-linecap="round"></path>
                </svg>
            </div>
            <div id="gg-location-info" class="gg-hidden-control">
                <!-- Filled by JS -->
            </div>

            <div class="gg-admin-sort-control gg-hud-sort-control">
                <label class="gg-form-label" for="gg-hud-sort-options">Sort by</label>
                <span class="gg-admin-sort-select-wrap">
                    <select id="gg-hud-sort-options" class="gg-form-input gg-admin-sort-select">
                        <option value="precision">Precision</option>
                        <option value="newest">Recently Updated</option>
                        <option value="title">Title</option>
                        <option value="scope">Scope</option>
                        <option value="tags">Tags</option>
                    </select>
                </span>
            </div>

            <div id="gg-meta-container" class="gg-meta-content">
                <div class="gg-empty-state">Waiting for location...</div>
            </div>
            <div id="gg-status" class="gg-status-msg" title="Click to retry finding location">Waiting for location...</div>
        `;
        document.body.appendChild(hud);

        // Main panel sort selector
        const hudSortSelect = document.getElementById('gg-hud-sort-options');
        if (hudSortSelect) {
            hudSortSelect.value = hudSortMode;
            resizeSortSelectToContent(hudSortSelect);
            hudSortSelect.addEventListener('change', (e) => {
                hudSortMode = HUD_SORT_MODES.includes(e.target.value) ? e.target.value : 'precision';
                try {
                    writeStoredValue(HUD_SORT_STORAGE_KEY, hudSortMode);
                } catch (err) {
                    console.warn('[BetterMetas] Could not save the panel sort mode:', err);
                }
                resizeSortSelectToContent(hudSortSelect);
                lastHudRenderKey = null;
                refreshDisplay();
            });
            // Keep typing / key shortcuts of the page from reacting to the select.
            hudSortSelect.addEventListener('keydown', (e) => e.stopPropagation());
            hudSortSelect.addEventListener('keyup', (e) => e.stopPropagation());
        }

        // Dragging: grab the title bar (but not its buttons) to move the HUD.
        function startHudDrag(e) {
            if (typeof e.button === 'number' && e.button !== 0) return;

            const target = getEventElementTarget(e);
            if (target && target.closest('button, input, textarea, select, svg')) return;

            e.preventDefault();

            const startX = e.clientX;
            const startY = e.clientY;
            const startRect = hud.getBoundingClientRect();
            const previousUserSelect = document.body.style.userSelect;
            document.body.style.userSelect = 'none';
            hud.classList.add('gg-dragging');

            const onPointerMove = (moveEvent) => {
                const rawLeft = startRect.left + moveEvent.clientX - startX;
                const rawTop = startRect.top + moveEvent.clientY - startY;
                const { left, top } = clampHudPosition(rawLeft, rawTop, hud);
                hud.style.left = `${Math.round(left)}px`;
                hud.style.top = `${Math.round(top)}px`;
                hud.style.right = 'auto';
                hud.style.transform = 'none';
            };

            const onPointerUp = () => {
                document.removeEventListener('pointermove', onPointerMove);
                document.removeEventListener('pointerup', onPointerUp);
                document.body.style.userSelect = previousUserSelect;
                hud.classList.remove('gg-dragging');
                saveHudPosition(hud);
            };

            document.addEventListener('pointermove', onPointerMove);
            document.addEventListener('pointerup', onPointerUp);
        }

        hud.querySelector('.gg-meta-title').addEventListener('pointerdown', startHudDrag);

        // Resizing: a small always-visible grip in the corner, no need to
        // go through Settings > Resize HUD. Resizes live and auto-saves.
        function startHudGripResize(e) {
            if (typeof e.button === 'number' && e.button !== 0) return;

            e.preventDefault();
            e.stopPropagation();

            const startX = e.clientX;
            const startY = e.clientY;
            const startSize = getCurrentHudSize(hud);
            const previousUserSelect = document.body.style.userSelect;
            document.body.style.userSelect = 'none';
            hud.classList.add('gg-dragging');

            const onPointerMove = (moveEvent) => {
                const maxWidth = window.innerWidth - 16;
                const maxHeight = window.innerHeight - 16;
                const width = Math.min(maxWidth, Math.max(HUD_MIN_WIDTH, startSize.width + moveEvent.clientX - startX));
                const height = Math.min(maxHeight, Math.max(HUD_MIN_HEIGHT, startSize.height + moveEvent.clientY - startY));

                hud.style.width = `${Math.round(width)}px`;
                hud.style.height = `${Math.round(height)}px`;
                hud.style.maxWidth = 'calc(100vw - 1rem)';
                hud.style.maxHeight = 'calc(100vh - 1rem)';
            };

            const onPointerUp = () => {
                document.removeEventListener('pointermove', onPointerMove);
                document.removeEventListener('pointerup', onPointerUp);
                document.body.style.userSelect = previousUserSelect;
                hud.classList.remove('gg-dragging');

                const size = getCurrentHudSize(hud);
                writeStoredValue(HUD_SIZE_STORAGE_KEY, JSON.stringify(size));
            };

            document.addEventListener('pointermove', onPointerMove);
            document.addEventListener('pointerup', onPointerUp);
        }

        hud.querySelector('#gg-resize-grip').addEventListener('pointerdown', startHudGripResize);

        // Backdrop
        const backdrop = document.createElement('div');
        backdrop.id = 'gg-modal-backdrop';
        document.body.appendChild(backdrop);

        // Preview Popup
        const previewPopup = document.createElement('div');
        previewPopup.id = 'gg-meta-preview-popup';
        document.body.appendChild(previewPopup);

        const dialogModal = document.createElement('div');
        dialogModal.id = 'gg-dialog-modal';
        dialogModal.className = 'gg-context-surface gg-context-neutral';
        document.body.appendChild(dialogModal);

        // Close preview on outside click
        document.addEventListener('click', (e) => {
            if (!previewPopup.classList.contains('gg-visible')) return;

            const target = getEventElementTarget(e);
            const clickedMetaItem = target?.closest('.gg-meta-list-item');
            const clickedMetaAction = target?.closest('.gg-btn-link-meta, .gg-meta-link-toggle');
            if (clickedMetaItem && !clickedMetaAction) return;

            hidePreviewPopup();
        });

        // SETTINGS MODAL
        const settingsModal = document.createElement('div');
        settingsModal.id = 'gg-settings-modal';
        settingsModal.style.display = 'none';
        settingsModal.innerHTML = `
            <div class="gg-modal-container gg-context-surface gg-context-neutral">
                <div class="gg-modal-header">Settings</div>

                <div class="gg-form-group gg-form-group-lg">
                    <label class="gg-form-label">Scope Filter</label>
                    <div id="gg-settings-scope-filter" class="gg-pill-grid">
                        <!-- Filled by JS -->
                    </div>
                </div>

                <div class="gg-form-group gg-form-group-lg">
                    <label class="gg-form-label">Tag Filter</label>
                    <div id="gg-settings-tag-filter" class="gg-pill-grid">
                        <!-- Filled by JS -->
                    </div>
                </div>
                <hr class="gg-modal-divider">

                <button class="gg-btn-primary" id="gg-save-settings">Save Changes</button>

                <button class="gg-btn-secondary" id="gg-close-settings">Cancel</button>
            </div>
        `;
        document.body.appendChild(settingsModal);

        // ADMIN MODAL
        const adminModal = document.createElement('div');
        adminModal.id = 'gg-meta-admin-modal';
        adminModal.className = 'gg-context-surface gg-context-pat';
        adminModal.style.display = 'none';
        adminModal.innerHTML = `
            <div id="gg-admin-main-view" class="gg-modal-subview">
                <div class="gg-modal-header">Manage Metas</div>
                <div class="gg-form-group gg-admin-controls">
                    <input type="text" id="gg-admin-search" class="gg-form-input" placeholder="Filter by country, title or tags (e.g. Kenya; snorkel)">
                    <div class="gg-admin-sort-control">
                        <label class="gg-form-label" for="gg-admin-sort-options">Sort by</label>
                        <span class="gg-admin-sort-select-wrap">
                            <select id="gg-admin-sort-options" class="gg-form-input gg-admin-sort-select">
                                <option value="newest">Recently Updated</option>
                                <option value="title">Title</option>
                                <option value="scope">Scope</option>
                                <option value="tags">Tags</option>
                            </select>
                        </span>
                    </div>
                </div>
                <div id="gg-admin-meta-list" class="gg-admin-meta-list"></div>
                <hr class="gg-modal-divider">
                <button class="gg-btn-secondary" id="gg-admin-close-btn">Close</button>
            </div>

            <div id="gg-admin-details-view" class="gg-modal-subview gg-hidden">
                <div class="gg-modal-header gg-modal-header-with-back">
                    <button id="gg-admin-back-btn" class="gg-modal-back-btn" title="Back to Meta List" aria-label="Back to Meta List">
                        <svg xmlns="http://www.w3.org/2000/svg" width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><line x1="19" y1="12" x2="5" y2="12"></line><polyline points="12 19 5 12 12 5"></polyline></svg>
                    </button>
                    Meta Details
                </div>

                <div class="gg-admin-details-grid">
                    <div class="gg-form-group">
                        <label class="gg-form-label">Title</label>
                        <input type="text" id="gg-admin-meta-title" class="gg-form-input">
                    </div>
                    <div class="gg-form-group">
                        <label class="gg-form-label">Image URL (optional)</label>
                        <input type="text" id="gg-admin-meta-image" class="gg-form-input">
                    </div>
                    <div class="gg-form-group">
                        <label class="gg-form-label">Description</label>
                        <textarea id="gg-admin-meta-desc" class="gg-form-input" rows="4"></textarea>
                        <div class="gg-form-hint">Formatting: **bold** and *italic*</div>
                    </div>
                    <div class="gg-form-group">
                        <label class="gg-form-label">Scope</label>
                        <input type="text" id="gg-admin-meta-scope" class="gg-form-input gg-hidden-control">
                        <div id="gg-admin-scope-presets" class="gg-pill-grid">
                            ${renderScopePills(ALL_SCOPES)}
                        </div>
                        <div id="gg-admin-landscape-import" style="display:none">
                            <button type="button" class="gg-btn-secondary" id="gg-admin-landscape-btn">IMPORT FILE (.JSON)</button>
                            <input type="file" id="gg-admin-landscape-file" accept=".json,application/json" style="display:none">
                        </div>
                    </div>
                    <div class="gg-form-group">
                        <label class="gg-form-label">Tags</label>
                        <input type="text" id="gg-admin-meta-tags" class="gg-form-input gg-hidden-control">
                        <div id="gg-admin-tag-presets" class="gg-pill-grid">
                            ${renderTagPills(TAG_PRESETS)}
                        </div>
                    </div>
                </div>

                <hr class="gg-modal-divider">

                <div class="gg-form-group">
                    <label class="gg-form-label">Linked Locations</label>
                    <div id="gg-admin-linked-locations" class="gg-admin-linked-locations"></div>
                </div>

                <hr class="gg-modal-divider">

                <div class="gg-admin-actions">
                    <button class="gg-btn-primary gg-btn-edit" id="gg-admin-save-btn">Save Meta</button>
                    <button class="gg-btn-primary" id="gg-admin-link-btn">Link to Location</button>
                    <button class="gg-btn-danger" id="gg-admin-delete-btn">Delete Meta</button>
                </div>
            </div>
        `;
        document.body.appendChild(adminModal);

        keepKeysInsideInputs(adminModal);

        adminModal.querySelector('#gg-admin-scope-presets').addEventListener('click', (e) => {
            const target = getEventElementTarget(e);
            if (!target || !target.classList.contains('gg-tag-pill')) return;

            adminModal.querySelectorAll('#gg-admin-scope-presets .gg-tag-pill').forEach(pill => {
                pill.classList.toggle('gg-tag-selected', pill === target);
            });
            document.getElementById('gg-admin-meta-scope').value = target.dataset.value || '';
            refreshLandscapeImportUi('admin');
        });

        adminModal.querySelector('#gg-admin-tag-presets').addEventListener('click', (e) => {
            const target = getEventElementTarget(e);
            if (!target || !target.classList.contains('gg-tag-pill')) return;

            target.classList.toggle('gg-tag-selected');
            const selectedTags = Array.from(adminModal.querySelectorAll('#gg-admin-tag-presets .gg-tag-pill.gg-tag-selected'))
                .map(pill => pill.textContent.trim());
            document.getElementById('gg-admin-meta-tags').value = normalizeTags(selectedTags).join(', ');
        });

        const adminImageInput = adminModal.querySelector('#gg-admin-meta-image');
        adminImageInput.addEventListener('input', updateAdminImagePreview);
        adminImageInput.addEventListener('mouseenter', showAdminImageUrlPreview);
        adminImageInput.addEventListener('mouseleave', hideAdminImageUrlPreview);

        // MODAL
        const modal = document.createElement('div');
        modal.id = 'gg-meta-modal';
        modal.className = 'gg-context-surface gg-context-normal';
        modal.style.display = 'none';
        modal.innerHTML = `
            <div id="meta-main-view" class="gg-modal-subview">
                <div class="gg-modal-header">Add metas to location</div>

                <div class="gg-form-group">
                    <input type="text" id="meta-search" class="gg-form-input" placeholder="Filter by country, title or tags (e.g. Kenya; snorkel)">
                </div>
                <div id="gg-existing-metas"></div>

                <hr class="gg-modal-divider">

                <div id="gg-selection-actions" class="gg-selection-actions">
                    <button class="gg-btn-primary" id="gg-link-selected-btn">
                        Link Selected Metas (0)
                    </button>
                </div>

                <hr class="gg-modal-divider">

                <div>
                    <button class="gg-btn-primary gg-btn-edit" id="meta-details-btn">
                        Create New Meta
                    </button>
                </div>

                <div id="gg-json-output"></div>

                <button class="gg-btn-secondary" id="meta-close-btn">Close</button>
            </div>

            <div id="meta-details-view" class="gg-modal-subview gg-hidden">
                <div class="gg-modal-header gg-modal-header-with-back">
                    <button id="meta-back-btn" class="gg-modal-back-btn" title="Back to Meta Selection" aria-label="Back to Meta Selection">
                        <svg xmlns="http://www.w3.org/2000/svg" width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><line x1="19" y1="12" x2="5" y2="12"></line><polyline points="12 19 5 12 12 5"></polyline></svg>
                    </button>
                    Meta Details
                </div>

                <div class="gg-form-group">
                    <label class="gg-form-label">Title</label>
                    <input type="text" id="meta-title" class="gg-form-input" placeholder="e.g. Kenya Snorkel">
                </div>

                <div class="gg-form-group">
                    <label class="gg-form-label">Description</label>
                    <textarea id="meta-desc" class="gg-form-input" rows="3" placeholder="Describe the hint..."></textarea>
                    <div class="gg-form-hint">Formatting: **bold** and *italic*</div>
                </div>

                <div class="gg-form-group">
                    <label class="gg-form-label">Image URL (optional)</label>
                    <input type="text" id="meta-image" class="gg-form-input" placeholder="https://...">
                </div>

                <div class="gg-form-group">
                    <label class="gg-form-label">Scope</label>
                    <input type="text" id="meta-scope" class="gg-form-input gg-hidden-control">
                    <div id="meta-scope-presets" class="gg-pill-grid">
                        ${renderScopePills(ALL_SCOPES)}
                    </div>
                    <div id="meta-landscape-import" style="display:none">
                        <button type="button" class="gg-btn-secondary" id="meta-landscape-btn">IMPORT FILE (.JSON)</button>
                        <input type="file" id="meta-landscape-file" accept=".json,application/json" style="display:none">
                    </div>
                </div>

                <div class="gg-form-group">
                    <label class="gg-form-label">Tags</label>
                    <!-- Input hidden, using pills only -->
                    <input type="text" id="meta-tags" class="gg-form-input gg-hidden-control" placeholder="">
                    <div id="meta-tag-presets" class="gg-pill-grid">
                        ${renderTagPills(TAG_PRESETS)}
                    </div>
                </div>

                <hr class="gg-modal-divider">

                <button class="gg-btn-primary gg-btn-edit" id="meta-generate-btn">${META_SAVE_BUTTON_LABEL}</button>
            </div>
        `;


        // Presets Logic (Multi-select)
        const presetContainer = modal.querySelector('#meta-tag-presets');

        const updateHiddenInput = () => {
            const selected = Array.from(presetContainer.querySelectorAll('.gg-tag-selected'))
                                  .map(el => el.textContent.trim());
            document.getElementById('meta-tags').value = normalizeTags(selected).join(', ');
        };

        presetContainer.addEventListener('click', (e) => {
            const target = getEventElementTarget(e);
            if (target && target.classList.contains('gg-tag-pill')) {
                target.classList.toggle('gg-tag-selected');
                updateHiddenInput();
            }
        });

        // Scope Logic (Single-select)
        const scopeContainer = modal.querySelector('#meta-scope-presets');

        scopeContainer.addEventListener('click', (e) => {
            const target = getEventElementTarget(e);
            if (target && target.classList.contains('gg-tag-pill')) {
                // Deselect all others
                Array.from(scopeContainer.querySelectorAll('.gg-tag-pill')).forEach(el => {
                   if (el !== target) el.classList.remove('gg-tag-selected');
                });

                // Toggle clicked
                const wasSelected = target.classList.contains('gg-tag-selected');
                if (!wasSelected) {
                    target.classList.add('gg-tag-selected');
                } else {
                    target.classList.remove('gg-tag-selected');
                }

                // Update hidden input
                const selected = scopeContainer.querySelector('.gg-tag-selected');
                document.getElementById('meta-scope').value = selected ? selected.dataset.value : '';
                refreshLandscapeImportUi('create');
            }
        });



        // Add Toggle logic
        const showDetails = () => {
            document.getElementById('meta-main-view').classList.add('gg-hidden');
            document.getElementById('meta-details-view').classList.remove('gg-hidden');
            setUiContext(modal, 'edit');
        };
        const hideDetails = () => {
            document.getElementById('meta-details-view').classList.add('gg-hidden');
            document.getElementById('meta-main-view').classList.remove('gg-hidden');
            setUiContext(modal, 'normal');
        };

        modal.querySelector('#meta-details-btn').addEventListener('click', showDetails);
        modal.querySelector('#meta-back-btn').addEventListener('click', hideDetails);

        keepKeysInsideInputs(modal);

        document.body.appendChild(modal);
        initLandscapeImport('create');
        initLandscapeImport('admin');

        // Event Listeners
        document.getElementById('gg-meta-admin-btn').addEventListener('click', () => {
            selectedAdminMetaId = null;
            adminSortMode = 'newest';
            const searchInput = document.getElementById('gg-admin-search');
            searchInput.value = '';
            updateAdminSortButtons();
            showAdminMainView();
            renderAdminMetas();
            hidePreviewPopup();
            showAdminModal();
            requestAnimationFrame(() => searchInput.focus());
        });

        document.getElementById('gg-meta-add-btn').addEventListener('click', () => {
            syncPanoidForUserAction('open add modal');

            // Opening without an active location is allowed (for testing); linking
            // then asks for a result screen.
            showMetaModal();
            setUiContext(modal, 'normal');
            document.getElementById('meta-main-view').classList.remove('gg-hidden');
            document.getElementById('meta-details-view').classList.add('gg-hidden');
            const searchInput = document.getElementById('meta-search');
            searchInput.value = '';
            document.getElementById('gg-json-output').style.display = 'none';
            selectedMetaIds.clear();
            updateLinkSelectedBtn();
            renderExistingMetas(); // Populate existing metas list
            requestAnimationFrame(() => searchInput.focus());
        });

        // Settings pills are re-rendered each time the modal opens: one delegated
        // listener per container. Only the UI state is toggled here, nothing is saved
        // until "Save Changes".
        ['gg-settings-scope-filter', 'gg-settings-tag-filter'].forEach(id => {
            document.getElementById(id).addEventListener('click', event => {
                getEventElementTarget(event)?.closest('.gg-tag-pill')?.classList.toggle('gg-tag-selected');
            });
        });

        // Clicking a meta title in the panel opens it in the editor.
        document.getElementById('gg-meta-container').addEventListener('click', event => {
            const title = getEventElementTarget(event)?.closest('.gg-clickable-meta-title');
            if (title) openMetaEditorFromTitle(title.dataset.metaId);
        });

        document.getElementById('gg-settings-btn').addEventListener('click', () => {
            // Render Scope Filter
            const scopeContainer = document.getElementById('gg-settings-scope-filter');
            scopeContainer.innerHTML = renderScopePills(ALL_SCOPES, activeScopes);

            // Render Tag Filter
            const tagContainer = document.getElementById('gg-settings-tag-filter');
            tagContainer.innerHTML = renderTagFilterPills(TAG_PRESETS, activeTags);

            hidePreviewPopup();
            showSettingsModal();
        });

        document.getElementById('gg-save-settings').addEventListener('click', () => {
             // Save Scopes from UI state
             const scopeContainer = document.getElementById('gg-settings-scope-filter');
             const selectedFromUI = Array.from(scopeContainer.querySelectorAll('.gg-tag-pill.gg-tag-selected'))
                                         .map(el => el.dataset.value);

             activeScopes = new Set(selectedFromUI);
             writeStoredValue(ACTIVE_SCOPES_STORAGE_KEY, JSON.stringify(Array.from(activeScopes)));

             // Save Tags from UI state
             const tagContainer = document.getElementById('gg-settings-tag-filter');
             const selectedTagsFromUI = Array.from(tagContainer.querySelectorAll('.gg-tag-pill.gg-tag-selected'))
                                         .map(el => el.dataset.value);

             activeTags = new Set(selectedTagsFromUI);
             writeStoredValue(ACTIVE_TAGS_STORAGE_KEY, JSON.stringify(Array.from(activeTags)));

             // Refresh HUD
             if (currentPanoid) refreshDisplay();

             hideSettingsModal();
             hideBackdrop();
        });

        document.getElementById('gg-close-settings').addEventListener('click', () => {
            hideSettingsModal();
            hideBackdrop();
        });

        document.getElementById('gg-admin-search').addEventListener('input', debounce((e) => {
            renderAdminMetas(e.target.value);
        }));

        document.getElementById('gg-admin-sort-options').addEventListener('change', (e) => {
            adminSortMode = e.target.value || 'newest';
            updateAdminSortButtons();
            renderAdminMetas(document.getElementById('gg-admin-search')?.value || '');
        });

        document.getElementById('gg-admin-close-btn').addEventListener('click', (e) => {
            e.preventDefault();
            e.stopPropagation();
            hideAdminModal();
            hideBackdrop();
            hidePreviewPopup();
        });

        document.getElementById('gg-admin-back-btn').addEventListener('click', () => {
            showAdminMainView();
            renderAdminMetas(document.getElementById('gg-admin-search')?.value || '');
        });

        document.getElementById('gg-admin-save-btn').addEventListener('click', saveAdminMeta);

        document.getElementById('gg-admin-delete-btn').addEventListener('click', () => deleteAdminMeta());

        document.getElementById('gg-admin-link-btn').addEventListener('click', () => toggleAdminMetaLink(selectedAdminMetaId));

        document.getElementById('meta-close-btn').addEventListener('click', () => {
            hideMetaModal();
            hideBackdrop();
            hidePreviewPopup();
        });

        // Close when clicking backdrop
        document.getElementById('gg-link-selected-btn').addEventListener('click', () => {
            if (selectedMetaIds.size > 0) {
                linkMultipleMetas(Array.from(selectedMetaIds));
            }
        });

        backdrop.addEventListener('click', () => {
            const dialog = document.getElementById('gg-dialog-modal');
            if (dialog && window.getComputedStyle(dialog).display !== 'none') return;
            hideAllModals();
        });

        document.getElementById('meta-generate-btn').addEventListener('click', generateJSON);



        document.getElementById('gg-status').addEventListener('click', () => {
            syncPanoidForUserAction('manual refresh');
            updateStatus('Refreshing Data...');
            fetchLocationData();
        });

        // --- Existing Metas Browser ---
        document.getElementById('meta-search').addEventListener('input', debounce((e) => {
            renderExistingMetas(e.target.value);
        }));
    }

    function updateAdminSortButtons() {
        const sortSelect = document.getElementById('gg-admin-sort-options');
        if (!sortSelect) return;

        sortSelect.value = adminSortMode;
        resizeSortSelectToContent(sortSelect);
    }

    // Sizes a sort <select> to the text of its selected option.
    let textMeasureContext = null;

    function resizeSortSelectToContent(sortSelect) {
        if (!sortSelect) return;
        const selectedOption = sortSelect.selectedOptions[0];
        if (!selectedOption) return;

        textMeasureContext ||= document.createElement('canvas').getContext('2d');
        const context = textMeasureContext;
        if (!context) return;

        const styles = getComputedStyle(sortSelect);
        context.font = `${styles.fontStyle} ${styles.fontVariant} ${styles.fontWeight} ${styles.fontSize} ${styles.fontFamily}`;
        sortSelect.style.width = `${Math.ceil(context.measureText(selectedOption.text).width + 26)}px`;
    }

    function compareAdminText(a, b) {
        return String(a || '').localeCompare(String(b || ''), undefined, { sensitivity: 'base' });
    }

    function compareAdminTitle(metaA, metaB) {
        return compareAdminText(metaA.title, metaB.title);
    }

    function getAdminMetaUpdatedSortValue(meta, originalIndex) {
        const updatedAtTime = Date.parse(meta.updatedAt || '');
        if (Number.isFinite(updatedAtTime)) return updatedAtTime;
        const timestampMatch = String(meta.id || '').match(/_(\d{10,})_[a-z0-9]+$/);
        if (timestampMatch) return Number(timestampMatch[1]);
        return originalIndex;
    }

    // Shared by the Manage Metas list and the main panel.
    // mode: title | scope | tags | newest. Entries are { meta, index }.
    function compareMetaEntriesByMode(mode, a, b) {
        const metaA = a.meta;
        const metaB = b.meta;
        if (mode === 'scope') {
            const scopeA = ALL_SCOPES.indexOf(normalizeScope(metaA.scope));
            const scopeB = ALL_SCOPES.indexOf(normalizeScope(metaB.scope));
            return (scopeA < 0 ? Number.MAX_SAFE_INTEGER : scopeA) - (scopeB < 0 ? Number.MAX_SAFE_INTEGER : scopeB)
                || compareAdminTitle(metaA, metaB);
        }
        if (mode === 'tags') {
            return compareAdminText((metaA.tags || []).join(', '), (metaB.tags || []).join(', '))
                || compareAdminTitle(metaA, metaB);
        }
        if (mode === 'newest') {
            return getAdminMetaUpdatedSortValue(metaB, b.index) - getAdminMetaUpdatedSortValue(metaA, a.index)
                || compareAdminTitle(metaA, metaB);
        }
        return compareAdminTitle(metaA, metaB);
    }

    function sortAdminMetaEntries(entries) {
        return entries.sort((a, b) => compareMetaEntriesByMode(adminSortMode, a, b));
    }

    // ---- Main panel sort ----------------------------------------------------------
    // 'precision' keeps the historical order (most precise scope first); the other
    // modes are the same as the Manage Metas list.
    const HUD_SORT_STORAGE_KEY = 'gg_hud_sort_mode';
    const HUD_SORT_MODES = ['precision', 'newest', 'title', 'scope', 'tags'];
    let hudSortMode = (() => {
        try {
            const saved = readStoredValue(HUD_SORT_STORAGE_KEY);
            return HUD_SORT_MODES.includes(saved) ? saved : 'precision';
        } catch (err) {
            return 'precision';
        }
    })();

    function sortMetasForHud(metas) {
        if (hudSortMode === 'precision') return sortLinkedMetasByPrecision(metas);
        return metas
            .map((meta, index) => ({ meta, index }))
            .sort((a, b) => compareMetaEntriesByMode(hudSortMode, a, b))
            .map(({ meta }) => meta);
    }

    function getMetaSearchTerms(searchTerm) {
        return searchTerm.toLowerCase().split(/[;,]/).map(term => term.trim()).filter(Boolean);
    }

    function matchesMetaSearch(meta, terms) {
        if (terms.length === 0) return true;
        const indexedContent = ensureMetaSearchIndex().get(meta.id) || '';
        return terms.every(term => indexedContent.includes(term));
    }

    function resetIncrementalList(container, html = '') {
        const previous = incrementalListStates.get(container);
        previous?.observer?.disconnect();
        incrementalListStates.delete(container);
        container.innerHTML = html;
    }

    function renderIncrementalList(container, items, renderItem) {
        resetIncrementalList(container);

        const state = { items, rendered: 0, observer: null };
        const sentinel = document.createElement('button');
        sentinel.type = 'button';
        sentinel.className = 'gg-list-load-more';

        const appendNextPage = () => {
            if (state.rendered >= items.length) return;
            const nextEnd = Math.min(state.rendered + META_LIST_PAGE_SIZE, items.length);
            const template = document.createElement('template');
            template.innerHTML = items.slice(state.rendered, nextEnd).map(renderItem).join('');
            sentinel.before(template.content);
            state.rendered = nextEnd;
            const remaining = items.length - state.rendered;
            if (remaining > 0) {
                sentinel.textContent = `${remaining} more — scroll or click to load`;
            } else {
                sentinel.remove();
                state.observer?.disconnect();
            }
        };

        sentinel.addEventListener('click', appendNextPage);
        container.appendChild(sentinel);
        incrementalListStates.set(container, state);
        appendNextPage();

        if (sentinel.isConnected && typeof IntersectionObserver === 'function') {
            state.observer = new IntersectionObserver(entries => {
                if (entries.some(entry => entry.isIntersecting)) appendNextPage();
            }, { root: container, rootMargin: '160px 0px' });
            state.observer.observe(sentinel);
        }
    }

    function setMetaListClickHandler(container, handler) {
        let state = metaListInteractionStates.get(container);
        if (!state) {
            state = { clickHandler: null, preview: null, clickEventBound: false, previewEventsBound: false };
            metaListInteractionStates.set(container, state);
        }
        if (!state.clickEventBound) {
            state.clickEventBound = true;
            container.addEventListener('click', event => {
                metaListInteractionStates.get(container)?.clickHandler?.(event);
            });
        }
        state.clickHandler = handler;
    }

    function renderMetaListItem(meta, options) {
        const title = options.titleFallback ? meta.title || meta.id : meta.title;
        return `
            <div class="gg-meta-list-item${options.itemClass || ''}" data-meta-id="${escapeHtml(meta.id)}">
                <div class="gg-meta-list-main">
                    <div class="gg-meta-list-title">${escapeHtml(title)}</div>
                    <div class="gg-meta-list-tags">
                        ${options.showScope ? `<span class="gg-tag-static gg-scope-static">${escapeHtml(getScopeLabel(normalizeScope(meta.scope)))}</span>` : ''}
                        ${renderStaticTags(meta.tags)}
                    </div>
                </div>
                ${options.actionHtml}
            </div>
        `;
    }

    function attachMetaPreview(container, modalId, options = {}) {
        const previewPopup = document.getElementById('gg-meta-preview-popup');
        const modal = document.getElementById(modalId);
        let state = metaListInteractionStates.get(container);
        if (!state) {
            state = { clickHandler: null, preview: null, clickEventBound: false, previewEventsBound: false };
            metaListInteractionStates.set(container, state);
        }
        state.preview = { previewPopup, modal, options };

        if (!state.previewEventsBound) {
            state.previewEventsBound = true;
            container.addEventListener('mouseover', event => {
                const current = metaListInteractionStates.get(container)?.preview;
                if (!current) return;
                const item = event.target.closest(current.options.itemSelector || '.gg-meta-list-item');
                if (!item || !container.contains(item) || item.contains(event.relatedTarget)) return;
                const meta = getMetaById(item.dataset.metaId);
                if (!meta || !current.previewPopup || (current.options.requireModal && !current.modal)) return;

                delete current.previewPopup.dataset.ggPreviewCleanupId;
                current.previewPopup.dataset.ggPreviewMode = 'meta';
                current.previewPopup.classList.remove('gg-image-url-preview');
                const previewTags = renderStaticTags(meta.tags);
                revokeImageObjectUrls(current.previewPopup);
                current.previewPopup.innerHTML = `
                    <div class="gg-meta-item-title">${escapeHtml(current.options.titleFallback ? meta.title || meta.id : meta.title)}</div>
                    ${renderMetaImage(meta.imageUrl, true)}
                    <div class="gg-meta-description">${formatMetaDescription(current.options.descriptionFallback ? meta.description || '' : meta.description)}</div>
                    ${previewTags ? `<div class="gg-meta-tags">${previewTags}</div>` : ''}
                `;

                const positionPreviewTop = () => {
                    const itemRect = item.getBoundingClientRect();
                    current.previewPopup.style.top = `${itemRect.top + (itemRect.height / 2) - (current.previewPopup.offsetHeight / 2)}px`;
                };
                // The image now arrives asynchronously via the proxy, so
                // re-center the popup once its real height is known.
                const previewImage = current.previewPopup.querySelector('.gg-meta-image');
                previewImage?.addEventListener('load', () => {
                    if (previewImage.isConnected) positionPreviewTop();
                }, { once: true });
                loadDeferredImages(current.previewPopup);

                if (!current.modal) return;
                const modalRect = current.modal.getBoundingClientRect();
                current.previewPopup.style.left = `${modalRect.left - 290}px`;
                current.previewPopup.classList.add('gg-visible');
                positionPreviewTop();
            });
            container.addEventListener('mouseout', event => {
                const item = event.target.closest('.gg-meta-list-item');
                if (item && !item.contains(event.relatedTarget)) hidePreviewPopup();
            });
        }
    }

    function renderAdminMetas(searchTerm = '') {
        const container = document.getElementById('gg-admin-meta-list');
        if (!container) return;

        const terms = getMetaSearchTerms(searchTerm);

        const filtered = metasData
            .map((meta, index) => ({ meta, index }))
            .filter(entry => matchesMetaSearch(entry.meta, terms));

        const sorted = sortAdminMetaEntries(filtered);

        if (sorted.length === 0) {
            resetIncrementalList(container, '<div class="gg-form-hint gg-list-empty-state">No metas found.</div>');
            return;
        }

        renderIncrementalList(container, sorted, ({ meta }) => renderMetaListItem(meta, {
            itemClass: ' gg-admin-meta-item',
            titleFallback: true,
            showScope: true,
            actionHtml: `<button class="gg-btn-link-meta gg-btn-admin-edit" data-meta-id="${escapeHtml(meta.id)}">Edit</button>`,
        }));

        attachMetaPreview(container, 'gg-meta-admin-modal', { itemSelector: '.gg-admin-meta-item', requireModal: true, titleFallback: true, descriptionFallback: true });
        setMetaListClickHandler(container, event => {
            const btn = event.target.closest('.gg-btn-admin-edit');
            if (!btn) return;
            event.preventDefault();
            event.stopPropagation();
            openAdminMetaDetails(btn.dataset.metaId);
        });
    }

    function showAdminMainView() {
        setUiContext(document.getElementById('gg-meta-admin-modal'), 'pat');
        const mainView = document.getElementById('gg-admin-main-view');
        const detailsView = document.getElementById('gg-admin-details-view');
        if (mainView) mainView.classList.remove('gg-hidden');
        if (detailsView) detailsView.classList.add('gg-hidden');
        selectedAdminMetaId = null;
        hidePreviewPopup();
    }

    function updateAdminLinkButton() {
        const btn = document.getElementById('gg-admin-link-btn');
        if (!btn || !selectedAdminMetaId) return;

        const panoid = currentPanoid;
        if (!panoid || panoid === MISSING_PANOID_PLACEHOLDER) {
            btn.style.display = 'none';
            return;
        }

        const linkedMetaIds = getLinkedMetaIdsForPanoid(userLocationMap, panoid);
        const isLinked = linkedMetaIds.has(selectedAdminMetaId);

        btn.style.display = '';
        btn.textContent = isLinked ? 'Unlink from Location' : 'Link to Location';
        btn.className = isLinked ? 'gg-btn-danger' : 'gg-btn-primary';
        btn.id = 'gg-admin-link-btn';
    }

    async function toggleAdminMetaLink(metaId) {
        if (!metaId) return;

        const panoid = syncPanoidForUserAction('link/unlink meta');
        if (!panoid || panoid === MISSING_PANOID_PLACEHOLDER) {
            await showToolAlert('No Location Detected', 'Please try on a game result screen.');
            return;
        }

        const linkedMetaIds = getLinkedMetaIdsForPanoid(userLocationMap, panoid);
        const isLinked = linkedMetaIds.has(metaId);
        const btn = document.getElementById('gg-admin-link-btn');
        const adminModal = document.getElementById('gg-meta-admin-modal');
        // Use the scope currently selected in the admin form, which may differ
        // from the saved meta scope if the user edited it without saving yet.
        const formScope = document.getElementById('gg-admin-meta-scope')?.value || null;

        // When linking with a scope different from the saved one, the meta's scope
        // is updated too (in memory and in user_metas.json), so the meta and the
        // location it is linked to never disagree. Only the scope is persisted;
        // other unsaved form edits still need "Save Meta".
        const existingMeta = getMetaById(metaId);
        const newScope = (!isLinked && formScope && existingMeta &&
            normalizeScope(formScope) !== normalizeScope(existingMeta.scope))
            ? normalizeScope(formScope)
            : null;
        const scopeUpdatedMeta = newScope
            ? { ...existingMeta, scope: newScope, updatedAt: new Date().toISOString() }
            : null;

        const succeeded = await runMutation({
            ui: {
                scope: adminModal,
                button: btn,
                busyText: isLinked ? 'Unlinking...' : 'Linking...',
                statusText: isLinked ? 'Removing meta...' : 'Linking meta...'
            },
            failTitle: isLinked ? 'Unlink Failed' : 'Link Failed',
            prepare: () => (isLinked ? null : waitForScopeGeocoding(newScope || existingMeta?.scope)),
            run: async () => {
                if (isLinked) {
                    applyLocalLocationUnlinks(panoid, [metaId]);
                    updateStatus('Unlinked. Syncing...');
                    await updateLocalJsonFile(
                        USER_LOCATIONS_FILE,
                        normalizeLocationMap,
                        locations => {
                            removeMetaIdsFromPanoidLocations(locations, panoid, [metaId]);
                            return locations;
                        },
                        `Unlink 1 meta from ${panoid} via BetterMetas`
                    );
                    updateStatus('Unlinked!');
                } else {
                    if (scopeUpdatedMeta) {
                        if (!isUserMeta(metaId)) {
                            throw new Error(`Unknown meta ${metaId}`);
                        }
                        applyAdminMetaLocally(scopeUpdatedMeta);
                        renderAdminMetas(document.getElementById('gg-admin-search')?.value || '');
                    }
                    applyLocalLocationLinks(panoid, [metaId], formScope);
                    updateStatus('Linked. Syncing...');
                    if (scopeUpdatedMeta) {
                        await updateLocalJsonFileIfChanged(
                            USER_METAS_FILE,
                            normalizeMetaList,
                            metas => {
                                let found = false;
                                const updatedMetas = metas.map(meta => {
                                    if (meta.id !== metaId) return meta;
                                    found = true;
                                    return { ...meta, scope: scopeUpdatedMeta.scope, updatedAt: scopeUpdatedMeta.updatedAt };
                                });
                                if (!found) throw new Error(`Meta not found in ${USER_METAS_FILE}: ${metaId}`);
                                return updatedMetas;
                            },
                            `Update scope of meta ${metaId} to ${scopeUpdatedMeta.scope} via BetterMetas`
                        );
                    }
                    await updateLocalJsonFile(
                        USER_LOCATIONS_FILE,
                        normalizeLocationMap,
                        locations => {
                            addMetaIdsToLocationMap(locations, panoid, [metaId], formScope);
                            return locations;
                        },
                        `Link 1 meta to ${panoid} via BetterMetas`
                    );
                    updateStatus('Linked!');
                }
                scheduleBackgroundDataRefresh();
            }
        });
        if (succeeded === null) return;

        updateAdminLinkButton();
        renderAdminLinkedLocations(metaId);
    }

    function openAdminMetaDetails(metaId) {
        const meta = getMetaById(metaId);
        if (!meta) return;

        selectedAdminMetaId = metaId;
        const setValue = (id, value) => {
            const input = document.getElementById(id);
            if (input) input.value = value ?? '';
        };

        setValue('gg-admin-meta-image', meta.imageUrl || '');
        setValue('gg-admin-meta-title', meta.title || '');
        setValue('gg-admin-meta-desc', meta.description || '');
        landscapeCenterState.admin = null;
        setAdminScopeSelection(meta.scope);
        setAdminTagSelection(meta.tags);
        updateAdminImagePreview();
        renderAdminLinkedLocations(meta.id);
        updateAdminLinkButton();

        setUiContext(document.getElementById('gg-meta-admin-modal'), 'edit');

        document.getElementById('gg-admin-main-view')?.classList.add('gg-hidden');
        document.getElementById('gg-admin-details-view')?.classList.remove('gg-hidden');
        hidePreviewPopup();
    }

    function renderExistingMetas(searchTerm = '') {
        const container = document.getElementById('gg-existing-metas');
        if (!container) return;

        const panoid = currentPanoid || MISSING_PANOID_PLACEHOLDER;
        const linkedMetaIds = getLinkedMetaIdsForPanoid(userLocationMap, panoid);

        const terms = getMetaSearchTerms(searchTerm);

        const filtered = metasData.filter(meta => matchesMetaSearch(meta, terms));
        const uniqueFiltered = filtered;

        if (uniqueFiltered.length === 0) {
            resetIncrementalList(container, '<div class="gg-form-hint gg-list-empty-state">No metas found.</div>');
            return;
        }

        renderIncrementalList(container, uniqueFiltered, meta => {
            const isSelected = selectedMetaIds.has(meta.id);
            const isLinked = linkedMetaIds.has(meta.id);
            const actionHtml = isLinked
                        ? '<span class="gg-meta-linked-indicator" title="Already linked to this location">Linked</span>'
                        : `<label class="gg-meta-link-toggle" title="${isSelected ? 'Selected to link' : 'Select to link'}">
                            <input type="checkbox" class="gg-meta-link-checkbox" data-meta-id="${escapeHtml(meta.id)}" ${isSelected ? 'checked' : ''}>
                        </label>`;
            return renderMetaListItem(meta, { titleFallback: false, actionHtml });
        });

        attachMetaPreview(container, 'gg-meta-modal');
        setMetaListClickHandler(container, event => {
            const checkbox = event.target.closest('.gg-meta-link-checkbox');
            if (!checkbox) return;
            const metaId = checkbox.dataset.metaId;
            if (checkbox.checked) selectedMetaIds.add(metaId);
            else selectedMetaIds.delete(metaId);
            updateLinkSelectedBtn();
            const label = checkbox.closest('.gg-meta-link-toggle');
            if (label) label.title = checkbox.checked ? 'Selected to link' : 'Select to link';
        });
    }

    function updateLinkSelectedBtn() {
        const btn = document.getElementById('gg-link-selected-btn');
        if (!btn) return;

        const count = selectedMetaIds.size;
        btn.disabled = count === 0;
        btn.textContent = `Link Selected Metas (${count})`;
    }

    async function linkMultipleMetas(metaIds) {
        const panoid = syncPanoidForUserAction('link metas');
        if (!panoid || panoid === MISSING_PANOID_PLACEHOLDER) {
            await showToolAlert('No Location Detected', 'Please try on a game result screen.');
            return;
        }

        const linkBtn = document.getElementById('gg-link-selected-btn');

        const succeeded = await runMutation({
            ui: {
                scope: document.getElementById('gg-meta-modal'),
                button: linkBtn,
                busyText: 'Linking...',
                statusText: `Linking ${metaIds.length} metas...`
            },
            failTitle: 'Link Failed',
            prepare: async () => {
                for (const scopeToWait of new Set(metaIds.map(id => normalizeScope(getMetaById(id)?.scope)))) {
                    await waitForScopeGeocoding(scopeToWait);
                }
            },
            run: async () => {
                const unknownMetaIds = metaIds.filter(id => !userMetaIds.has(id));

                if (unknownMetaIds.length > 0) {
                    throw new Error(`Unknown meta IDs: ${unknownMetaIds.join(', ')}`);
                }

                applyLocalLocationLinks(panoid, metaIds);
                updateStatus('Linked. Syncing...');
                renderExistingMetas(document.getElementById('meta-search')?.value || '');

                await updateLocalJsonFile(
                    USER_LOCATIONS_FILE,
                    normalizeLocationMap,
                    locations => {
                        addMetaIdsToLocationMap(locations, panoid, metaIds);
                        return locations;
                    },
                    `Link ${metaIds.length} metas to ${panoid} via BetterMetas`
                );

                updateStatus('Linked!');
                scheduleBackgroundDataRefresh();
            }
        });
        if (succeeded === null) return;
        if (succeeded) {
            selectedMetaIds.clear();
            updateLinkSelectedBtn();
            renderExistingMetas(document.getElementById('meta-search')?.value || '');
        }
    }

    async function unlinkMetaFromAdminLocation(metaId, panoid) {
        if (!metaId || !panoid) return;

        const meta = getMetaById(metaId);
        const entry = normalizeLocationEntry((userLocationMap || {})[panoid]);
        if (!entry || !getLocationMetaIds(entry).includes(metaId)) {
            renderAdminLinkedLocations(metaId);
            return;
        }

        const locationLabel = formatAdminLocationLabel({
            panoid,
            ...entry,
            scope: meta?.scope,
            displayCountry: entry.country || entry.nominatimCountry || ''
        });
        const willDeleteLocation = getLocationMetaIds(entry).length <= 1;

        const confirmed = await showToolConfirm(
            'Unlink Location',
            willDeleteLocation
                ? `Remove "${meta ? (meta.title || meta.id) : metaId}" from ${locationLabel}? This is its only linked meta, so the location entry will be removed too.`
                : `Remove "${meta ? (meta.title || meta.id) : metaId}" from ${locationLabel}? The location keeps its other linked metas.`,
            { confirmText: 'Unlink', cancelText: 'Cancel', danger: true }
        );
        if (!confirmed) return;

        const succeeded = await runMutation({
            ui: {
                scope: document.getElementById('gg-meta-admin-modal'),
                busyText: 'Unlinking...',
                statusText: `Unlinking ${panoid}...`
            },
            failTitle: 'Unlink Failed',
            run: async () => {
                userLocationMap = { ...userLocationMap };
                removeMetaIdsFromLocationMap(userLocationMap, panoid, [metaId]);
                proximityIndexDirty = true;
                renderAdminLinkedLocations(metaId);
                if (currentPanoid === panoid) refreshDisplay();
                updateStatus('Unlinked. Syncing...');

                await updateLocalJsonFile(
                    USER_LOCATIONS_FILE,
                    normalizeLocationMap,
                    locations => {
                        removeMetaIdsFromLocationMap(locations, panoid, [metaId]);
                        return locations;
                    },
                    `Unlink meta ${metaId} from ${panoid} via BetterMetas`
                );

                updateStatus('Unlinked!');
                scheduleBackgroundDataRefresh();
            }
        });
        if (succeeded === null) return;

        updateAdminLinkButton();
    }

    // Removes ONE road from the road list of a segment entry. Removing the last road
    // is the same as unlinking the whole location.
    async function removeRoadFromAdminSegment(metaId, panoid, road) {
        if (!metaId || !panoid || !road) return;

        const entry = normalizeLocationEntry((userLocationMap || {})[panoid]);
        const roadKey = normalizeRoadKey(road);
        const roads = entry && entry.segment ? getSegmentRoadList(entry.road) : [];
        if (!roads.some(r => normalizeRoadKey(r) === roadKey)) {
            renderAdminLinkedLocations(metaId);
            return;
        }
        if (roads.length <= 1) {
            await unlinkMetaFromAdminLocation(metaId, panoid);
            return;
        }

        const confirmed = await showToolConfirm(
            'Remove Road',
            `Remove the road "${road}" from this segment? The segment keeps its other roads.`,
            { confirmText: 'Remove', cancelText: 'Cancel', danger: true }
        );
        if (!confirmed) return;

        const withoutRoad = list => getSegmentRoadList(list).filter(r => normalizeRoadKey(r) !== roadKey);

        await runMutation({
            ui: {
                scope: document.getElementById('gg-meta-admin-modal'),
                busyText: 'Removing...',
                statusText: `Removing road ${road}...`
            },
            failTitle: 'Remove Failed',
            run: async () => {
                userLocationMap = { ...userLocationMap, [panoid]: { ...userLocationMap[panoid], road: withoutRoad(entry.road) } };
                proximityIndexDirty = true;

                // A pending copy of the entry would put the road back when merged.
                const pending = loadPendingLocalChanges();
                if (pending.locations[panoid] && !Array.isArray(pending.locations[panoid])) {
                    pending.locations[panoid] = { ...pending.locations[panoid], road: withoutRoad(pending.locations[panoid].road) };
                    savePendingLocalChanges(pending);
                }

                renderAdminLinkedLocations(metaId);
                if (currentPanoid === panoid) refreshDisplay();
                updateStatus('Road removed. Syncing...');

                await updateLocalJsonFile(
                    USER_LOCATIONS_FILE,
                    normalizeLocationMap,
                    locations => {
                        const target = locations[panoid];
                        if (target && !Array.isArray(target) && target.segment) {
                            target.road = withoutRoad(target.road);
                        }
                        return locations;
                    },
                    `Remove road ${road} from segment ${panoid} via BetterMetas`
                );

                updateStatus('Road removed!');
                scheduleBackgroundDataRefresh();
            }
        });
    }

    async function generateJSON() {
        const title = document.getElementById('meta-title').value;
        const desc = document.getElementById('meta-desc').value;
        const tagsStr = document.getElementById('meta-tags').value;
        const tags = normalizeTags(tagsStr);
        const rawImageValue = document.getElementById('meta-image').value;
        const scope = normalizeScope(document.getElementById('meta-scope').value);
        const landscapeCenters = isLandscapeScope(scope) ? buildLandscapeCenters(landscapeCenterState.create, scope) : null;

        if (!title || !desc) {
            await showToolAlert('Missing Details', 'Please fill in Title and Description.');
            return;
        }

        const panoid = syncPanoidForUserAction('save meta') || MISSING_PANOID_PLACEHOLDER;
        if (panoid === MISSING_PANOID_PLACEHOLDER) {
            await showToolAlert('No Location Detected', 'Please try again on a game result screen.');
            return;
        }

        const btn = document.getElementById('meta-generate-btn');
        const output = document.getElementById('gg-json-output');

        // The busy state starts before the image import below, so a second click
        // cannot start a second save (and a second import) while this one runs.
        const finishUi = beginMutationUi({
            scope: document.getElementById('gg-meta-modal'),
            button: btn,
            busyText: 'Saving...',
            statusText: 'Saving meta...'
        });
        if (!finishUi) return;

        output.style.display = 'none';
        let snapshot = null;
        let imageUrl = null;
        let newMeta = null;
        let metaPersisted = false; // user_metas.json already holds the meta

        try {
            // An image import needs the country (folder name); wait for geocoding.
            const needsImageImport = rawImageValue.trim() && !isLocalImagePath(rawImageValue);
            const detectedCountryFolder = needsImageImport ? await waitForDetectedCountryFolder() : null;
            await waitForScopeGeocoding(scope);

            // Generate unique meta ID
            const metaId = generateMetaId();
            imageUrl = await resolveImageForSave(rawImageValue, detectedCountryFolder || getCountryFolderForLocation(getCurrentLocationSnapshot()) || getCountrySlugForMeta({ id: metaId }));
            // Metas created here are always linked to a location right away, and
            // that location entry stores lat/lng/country/nominatimCountry plus the
            // scope-relevant field (region/city/road) based on the meta's scope
            // (see ensureLocationEntry/getLocationSnapshotForScope). Don't duplicate
            // those fields onto the meta itself - user_locations.json is the
            // single source of truth for them.
            newMeta = {
                id: metaId,
                title: title,
                description: desc,
                imageUrl: imageUrl,
                scope: scope,
                tags: tags,
                updatedAt: new Date().toISOString()
            };

            snapshot = createLocalDataSnapshot();
            applyLocalSavedMeta(newMeta, panoid);
            if (landscapeCenters) applyLocalLandscapeCenters(newMeta.id, landscapeCenters);
            updateStatus('Saved. Syncing...');
            hideMetaModal();
            hideBackdrop();

            updateStatus('Saving user_metas.json...');
            await updateLocalJsonFile(
                USER_METAS_FILE,
                normalizeMetaList,
                metas => {
                    if (!metas.some(meta => meta.id === newMeta.id)) {
                        metas.push(newMeta);
                    }
                    return metas;
                },
                `Add meta ${newMeta.id} via BetterMetas`
            );
            metaPersisted = true;

            updateStatus('Saving user_locations.json...');
            await updateLocalJsonFile(
                USER_LOCATIONS_FILE,
                normalizeLocationMap,
                locations => {
                    addMetaIdsToLocationMap(locations, panoid, [newMeta.id], newMeta.scope);
                    if (landscapeCenters) setLandscapeCenterEntries(locations, newMeta.id, landscapeCenters);
                    return locations;
                },
                `Link ${panoid} to ${newMeta.id} via BetterMetas`
            );

            updateStatus('Saved!');
            landscapeCenterState.create = null;
            refreshLandscapeImportUi('create');
            scheduleBackgroundDataRefresh();
            setTimeout(() => finishUi({ buttonText: META_SAVE_BUTTON_LABEL }), SAVE_COMPLETE_RESET_MS);

        } catch (err) {
            console.error('Save error:', err);
            if (snapshot) restoreLocalDataSnapshot(snapshot);
            // The image was imported before the save: drop it again unless the saved
            // meta (or another one) uses it.
            if (!metaPersisted) await removeImageIfUnused(imageUrl);
            showMetaModal();
            // Kept around as a readable backup blob if the local save fails.
            const backup = newMeta ? `\n\nBackup JSON:\n${stringifyJsonContent({ action: 'add_meta', panoid, meta: newMeta })}` : '';
            output.textContent = `Error saving locally:\n${err.message}${backup}`;
            output.style.display = 'block';
            await showToolAlert('Save Failed', err.message);
            finishUi();
        }
    }

    async function refreshAfterAdminMutation({ optimisticMeta = null } = {}) {
        clearStoredValue(DATA_CACHE_STORAGE_KEY);
        if (optimisticMeta) applyAdminMetaLocally(optimisticMeta);
        await fetchLocationData();
        if (optimisticMeta) applyAdminMetaLocally(optimisticMeta);
        renderAdminMetas(document.getElementById('gg-admin-search')?.value || '');
        if (currentPanoid) refreshDisplay();
    }

    async function saveAdminMeta() {
        const existingMeta = getSelectedAdminMeta();
        if (!existingMeta) {
            await showToolAlert('No Meta Selected', 'Select a meta first.');
            return;
        }

        // Validate before anything touches the disk (the image import below writes a file).
        const form = readAdminMetaForm();
        if (!form.title || !form.description) {
            await showToolAlert('Missing Details', 'Please fill in Title and Description.');
            return;
        }

        // Captured now: reopening the details view (below) resets the pending import.
        const landscapeImport = isLandscapeScope(form.scope) ? landscapeCenterState.admin : null;
        const landscapeCenters = buildLandscapeCenters(landscapeImport, form.scope);

        const isUserOwned = isUserMeta(existingMeta.id);
        const saveBtn = document.getElementById('gg-admin-save-btn');
        const finishUi = beginMutationUi({
            scope: document.getElementById('gg-meta-admin-modal'),
            button: saveBtn,
            busyText: 'Saving...',
            statusText: `Saving meta ${existingMeta.id}...`
        });
        if (!finishUi) return;

        // Imports a remote image to disk: only done once the busy state blocks a second save.
        let updatedMeta;
        try {
            updatedMeta = await buildAdminMeta(existingMeta, form);
        } catch (err) {
            console.error(err);
            await showToolAlert('Save Failed', err.message || String(err));
            updateStatus('Save Failed');
            finishUi();
            return;
        }

        if (isUserOwned && normalizeScope(updatedMeta.scope) !== normalizeScope(existingMeta.scope)) {
            await waitForScopeGeocoding(updatedMeta.scope);
        }

        const snapshot = createLocalDataSnapshot();
        const previousImagePath = String(existingMeta.imageUrl || '').trim();
        const newImagePath = String(updatedMeta.imageUrl || '').trim();
        let previousImageStillUsed = true; // Safe default: never delete unless proven unused.
        let metaPersisted = false; // user_metas.json already holds the edited meta

        try {
            const savedMetaId = existingMeta.id;
            applyAdminMetaLocally(updatedMeta);

            // Scope changed: the location(s) the meta is linked to here must get the
            // fields of the new scope (region / city / road) instead of keeping the old ones.
            let relinkPanoid = null;
            const scopeChanged = isUserOwned &&
                normalizeScope(existingMeta.scope) !== normalizeScope(updatedMeta.scope);
            if (scopeChanged) {
                const panoid = syncPanoidForUserAction('update meta scope');
                if (panoid && panoid !== MISSING_PANOID_PLACEHOLDER &&
                    applyLocalScopeRelink(panoid, savedMetaId, existingMeta.scope, updatedMeta.scope)) {
                    relinkPanoid = panoid;
                }
            }

            // Landscape center: set/replace it for 100km/10km/1km, drop it for any other scope.
            const hadCenterEntry = hasLandscapeCenterEntry(userLocationMap, savedMetaId);
            const removeCenter = isUserOwned && !landscapeCenters &&
                !isLandscapeScope(updatedMeta.scope) && hadCenterEntry;
            if (landscapeCenters) {
                applyLocalLandscapeCenters(savedMetaId, landscapeCenters);
            } else if (removeCenter) {
                applyLocalLandscapeCenterRemoval(savedMetaId);
            }

            renderAdminMetas(document.getElementById('gg-admin-search')?.value || '');
            openAdminMetaDetails(savedMetaId);
            if (currentPanoid) refreshDisplay();
            updateStatus('Meta saved. Syncing...');

            if (isUserOwned) {
                await updateLocalJsonFileIfChanged(
                    USER_METAS_FILE,
                    normalizeMetaList,
                    metas => {
                        let found = false;
                        const updatedMetas = metas.map(meta => {
                            if (meta.id !== existingMeta.id) return meta;
                            found = true;
                            return updatedMeta;
                        });
                        if (!found) throw new Error(`Meta not found in ${USER_METAS_FILE}: ${existingMeta.id}`);
                        // Checked against the file's fresh content (which already holds
                        // the new image): is another meta still using the old one?
                        previousImageStillUsed = updatedMetas.some(meta => String(meta.imageUrl || '').trim() === previousImagePath);
                        return updatedMetas;
                    },
                    `Edit meta ${existingMeta.id} via BetterMetas`
                );
                metaPersisted = true;

                if (relinkPanoid) {
                    await updateLocalJsonFileIfChanged(
                        USER_LOCATIONS_FILE,
                        normalizeLocationMap,
                        locations => {
                            relinkMetaForScopeChange(locations, relinkPanoid, existingMeta.id, existingMeta.scope, updatedMeta.scope);
                            return locations;
                        },
                        `Update location of meta ${existingMeta.id} for scope ${updatedMeta.scope} via BetterMetas`
                    );
                }

                if (landscapeCenters || removeCenter) {
                    await updateLocalJsonFileIfChanged(
                        USER_LOCATIONS_FILE,
                        normalizeLocationMap,
                        locations => {
                            if (landscapeCenters) {
                                setLandscapeCenterEntries(locations, existingMeta.id, landscapeCenters);
                            } else {
                                removeLandscapeCenterEntry(locations, existingMeta.id);
                            }
                            return locations;
                        },
                        `${landscapeCenters ? 'Set' : 'Remove'} landscape center of meta ${existingMeta.id} via BetterMetas`
                    );
                }
            } else {
                throw new Error(`Unknown meta ${existingMeta.id}`);
            }

            // Image replaced (or removed): drop the old imported file once nothing uses it.
            if (previousImagePath && previousImagePath !== newImagePath && !previousImageStillUsed) {
                await removeLocalImage(previousImagePath);
            }

            updateStatus('Meta saved!');
            refreshAfterAdminMutation({ optimisticMeta: updatedMeta }).catch(err => {
                console.warn('[BetterMetas] Admin data refresh after save failed:', err);
            });
            setTimeout(() => {
                finishUi({ buttonText: 'Save Meta' });
            }, SAVE_COMPLETE_RESET_MS);
        } catch (err) {
            console.error(err);
            restoreLocalDataSnapshot(snapshot);
            // A freshly imported image is dropped again unless a saved meta uses it.
            if (!metaPersisted && newImagePath !== previousImagePath) await removeImageIfUnused(newImagePath);
            landscapeCenterState.admin = landscapeImport; // keep the import so the user can retry
            refreshLandscapeImportUi('admin');
            await showToolAlert('Save Failed', err.message || String(err));
            updateStatus('Save Failed');
            finishUi();
        }
    }

    async function deleteAdminMeta(actionButton = null) {
        const existingMeta = getSelectedAdminMeta();
        if (!existingMeta) {
            await showToolAlert('No Meta Selected', 'Select a meta first.');
            return;
        }

        const locationCount = countAdminMetaLocations(existingMeta.id);
        const confirmed = await showToolConfirm(
            'Delete Meta',
            `This will delete "${existingMeta.title || existingMeta.id}" and unlink it from ${locationCount} location${locationCount === 1 ? '' : 's'}.`,
            {
                confirmText: 'Delete Meta',
                cancelText: 'Cancel',
                danger: true
            }
        );
        if (!confirmed) return;

        const isUserOwned = isUserMeta(existingMeta.id);
        const actionBtn = actionButton || document.getElementById('gg-admin-delete-btn');

        const deletedImagePath = String(existingMeta.imageUrl || '').trim();
        let deletedImageStillUsed = true; // Safe default: never delete unless proven unused.

        await runMutation({
            ui: {
                scope: document.getElementById('gg-meta-admin-modal'),
                button: actionBtn,
                busyText: 'Deleting...',
                statusText: `Deleting meta ${existingMeta.id}...`
            },
            failTitle: 'Delete Failed',
            run: async () => {
                const deletedMetaId = existingMeta.id;
                applyAdminDeleteLocally(deletedMetaId);
                showAdminMainView();
                renderAdminMetas(document.getElementById('gg-admin-search')?.value || '');
                updateStatus('Deleted. Syncing...');

                await updateLocalJsonFileIfChanged(
                    USER_LOCATIONS_FILE,
                    normalizeLocationMap,
                    locations => {
                        removeMetaIdFromLocationEntries(locations, deletedMetaId);
                        return locations;
                    },
                    `Remove user locations for ${deletedMetaId} via BetterMetas`
                );

                if (isUserOwned) {
                    await updateLocalJsonFile(
                        USER_METAS_FILE,
                        normalizeMetaList,
                        metas => {
                            const updatedMetas = metas.filter(meta => meta.id !== deletedMetaId);
                            if (updatedMetas.length === metas.length) {
                                throw new Error(`Meta not found in ${USER_METAS_FILE}: ${deletedMetaId}`);
                            }
                            // Checked against the file's fresh content: is another meta
                            // still using the same image?
                            deletedImageStillUsed = updatedMetas.some(meta => String(meta.imageUrl || '').trim() === deletedImagePath);
                            return updatedMetas;
                        },
                        `Delete meta ${deletedMetaId} via BetterMetas`
                    );
                } else {
                    throw new Error(`Unknown meta ${deletedMetaId}`);
                }

                // Remove the imported image (data/<country>/<file>) once nothing uses it.
                if (!deletedImageStillUsed) await removeLocalImage(deletedImagePath);

                refreshAfterAdminMutation().catch(err => {
                    console.warn('[BetterMetas] Admin data refresh after delete failed:', err);
                });
                updateStatus('Meta deleted!');
            }
        });
    }

    function updateHUD(metas, predicted = []) {
        const container = document.getElementById('gg-meta-container');
        if (!container) return;
        const exactMetas = metas || [];
        const predictedMetas = predicted || [];
        const renderKey = JSON.stringify([
            currentPanoid,
            metaRenderVersion,
            exactMetas.map(meta => meta.id),
            predictedMetas.map(meta => meta.id)
        ]);
        if (renderKey === lastHudRenderKey) return;
        resetHudImageLoading(container);

        if (exactMetas.length === 0 && predictedMetas.length === 0) {
            container.innerHTML = '<div class="gg-muted-empty-state">No active hints for this location.</div>';
            lastHudRenderKey = renderKey;
            return;
        }

        const renderMeta = (m, isPredicted = false) => {
             const titleText = m.title || m.id;
             const titleAttr = `class="gg-clickable-meta-title" data-meta-id="${escapeHtml(m.id)}" title="Click to Edit Meta"`;

             return `
            <div class="gg-meta-row ${isPredicted ? 'gg-meta-row-predicted' : ''}">
                <div class="gg-meta-item-title">
                    <span ${titleAttr}>${escapeHtml(titleText)}</span>
                </div>
                ${renderMetaImage(m.imageUrl, true)}
                <div class="gg-meta-description">${formatMetaDescription(m.description)}</div>
                <div class="gg-meta-tags"><span class="gg-tag-static gg-scope-static">${escapeHtml(getScopeLabel(normalizeScope(m.scope)))}</span>${renderStaticTags(m.tags)}</div>
            </div>
            `;
        };

        const exactHtml = exactMetas.map(m => renderMeta(m, false)).join('');
        const predictedHtml = predictedMetas.map(m => renderMeta(m, true)).join('');

        container.innerHTML = exactHtml + predictedHtml;
        startHudImageLoading(container);

        lastHudRenderKey = renderKey;
    }


    function openMetaEditorFromTitle(metaId) {
        const meta = getMetaById(metaId);
        if (!meta) {
            return showToolAlert('Meta Not Found', 'This meta could not be found in the loaded BetterMetas data.');
        }

        hidePreviewPopup();
        showAdminModal();
        openAdminMetaDetails(metaId);
        requestAnimationFrame(() => document.getElementById('gg-admin-meta-title')?.focus());
        return Promise.resolve();
    }


    function refreshDisplay() {
        if (!currentPanoid) return;

        // Ensure metasData is loaded
        if (!metasData || metasData.length === 0) {
            debugLog('[BetterMetas] metasData not loaded yet, skipping display refresh');
            return;
        }

        debugLog(`[BetterMetas] refreshDisplay for ID: "${currentPanoid}"`);

        // Check for an exact match in the user's location data.
        const metaIds = Array.from(getLinkedMetaIdsForPanoid(userLocationMap, currentPanoid));

        // Helper to check scope
        const isScopeActive = (m) => {
            return activeScopes.has(normalizeScope(m.scope));
        };

        // Helper to check tags: if no tag is selected, everything passes.
        // Otherwise a meta must share at least one tag with the selection;
        // metas without tags only pass when no tag is selected.
        const isTagActive = (m) => {
            if (activeTags.size === 0) return true;
            const metaTags = Array.isArray(m.tags) ? m.tags : [];
            return metaTags.some(tag => activeTags.has(tag));
        };

        // Get exact metas - respect the active scope + tag filters, same as
        // predicted metas. A linked meta whose scope/tags no longer match the
        // active filter (e.g. edited from countrywide to region) should
        // disappear just like it would if it had never been linked.
        // A segment meta linked to this panoid is no exception: it only shows when the
        // location is on one of its roads and inside its rectangle (evaluateProximityMetas).
        const proximityMetas = evaluateProximityMetas();
        const proximityIds = new Set(proximityMetas.map(m => m.id));
        const exactMetas = sortMetasForHud(metaIds.map(id => {
            const found = getMetaById(id);
            if (!found) console.warn('[BetterMetas] Could not find exact meta data for ID:', id);
            return found;
        }).filter(Boolean)
            .filter(m => normalizeScope(m.scope) !== 'segment' || proximityIds.has(m.id))
            .filter(isScopeActive).filter(isTagActive));

        // Get predicted/nearby metas
        const predictedMetas = sortMetasForHud(proximityMetas
            .filter(pm => !metaIds.includes(pm.id))
            .filter(isScopeActive)
            .filter(isTagActive));

        debugLog(`[BetterMetas] Found ${exactMetas.length} exact and ${predictedMetas.length} predicted metas (Filtered).`);

        if (exactMetas.length > 0 || predictedMetas.length > 0) {
            updateHUD(exactMetas, predictedMetas);
        } else {
            updateHUD(null);
        }
    }

    function updateStatus(msg) {
        const el = document.getElementById('gg-status');
        if (el) el.textContent = msg;
    }

    function isValidPanoid(panoid) {
        return !!(panoid && typeof panoid === 'string' && panoid.length > 5);
    }

    function getStreetViewPanoid() {
        try {
            if (svInstance && typeof svInstance.getPano === 'function') {
                const panoid = svInstance.getPano();
                if (isValidPanoid(panoid)) return panoid;
            }
        } catch (err) {
            console.warn('[BetterMetas] Could not read active StreetView panoid:', err);
        }

        return null;
    }

    function readPanoidFromStreetView(instance, reason = 'streetview sync') {
        try {
            if (!instance || typeof instance.getPano !== 'function') return null;
            if (streetViewListenerInstance && instance !== streetViewListenerInstance) return null;
            const panoid = instance.getPano();
            if (!isValidPanoid(panoid)) return null;
            svInstance = instance;
            debugLog(`[BetterMetas] StreetView panoid from ${reason}:`, panoid);
            checkLocation(panoid);
            return panoid;
        } catch (err) {
            console.warn(`[BetterMetas] Could not sync StreetView panoid from ${reason}:`, err);
            return null;
        }
    }

    function registerStreetViewInstance(instance, reason = 'StreetView instance') {
        if (!instance) return;

        if (streetViewListenerInstance !== instance) {
            streetViewListenerHandles.forEach(handle => {
                try {
                    win.google?.maps?.event?.removeListener?.(handle);
                } catch (err) {
                    console.warn('[BetterMetas] Could not release an old StreetView listener:', err);
                }
            });
            streetViewListenerHandles = [];
            streetViewListenerInstance = instance;
        }
        svInstance = instance;

        if (streetViewListenerHandles.length === 0 && win.google?.maps?.event) {
            streetViewListenerHandles.push(win.google.maps.event.addListener(instance, 'pano_changed', () => {
                readPanoidFromStreetView(instance, 'pano_changed');
            }));

            streetViewListenerHandles.push(win.google.maps.event.addListener(instance, 'status_changed', () => {
                if (instance !== streetViewListenerInstance) return;
                svInstance = instance;
                extractLocationData();
                setTimeout(() => readPanoidFromStreetView(instance, 'status_changed'), 0);
            }));
        }

        readPanoidFromStreetView(instance, reason);
        setTimeout(() => readPanoidFromStreetView(instance, `${reason} delayed`), 100);
        setTimeout(() => readPanoidFromStreetView(instance, `${reason} settled`), STREETVIEW_RETRY_DELAY_MS);
    }

    function syncPanoidForUserAction(reason = 'user action') {
        const visiblePanoid = getStreetViewPanoid();
        const queuedPanoid = isValidPanoid(nextPanoid) ? nextPanoid : null;
        const activePanoid = visiblePanoid || queuedPanoid || currentPanoid;
        debugLog(`[BetterMetas] Panoids for ${reason}: visible=${visiblePanoid}, queued=${queuedPanoid}, active=${activePanoid}`);

        if (!isValidPanoid(activePanoid)) return null;

        if (visiblePanoid && queuedPanoid && visiblePanoid !== queuedPanoid) {
            debugLog(`[BetterMetas] Ignoring queued panoid for ${reason}; visible panoid wins: ${visiblePanoid} (queued ${queuedPanoid})`);
        }

        if (activePanoid !== currentPanoid) {
            debugLog(`[BetterMetas] Syncing active panoid for ${reason}: ${activePanoid} (was ${currentPanoid || 'none'})`);
            currentPanoid = activePanoid;
            nextPanoid = null;
            updateStatus(`ID: ${currentPanoid.substring(0,12)}...`);
            extractLocationData();
            refreshDisplay();
        }

        return currentPanoid;
    }

    // --- Logic ---
    function getHaversineDistance(lat1, lon1, lat2, lon2) {
        const R = 6371; // km
        const dLat = (lat2 - lat1) * Math.PI / 180;
        const dLon = (lon2 - lon1) * Math.PI / 180;
        const a = Math.sin(dLat / 2) * Math.sin(dLat / 2) +
                  Math.cos(lat1 * Math.PI / 180) * Math.cos(lat2 * Math.PI / 180) *
                  Math.sin(dLon / 2) * Math.sin(dLon / 2);
        const c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));
        return R * c;
    }

    const SCOPE_RADIUS_KM = { '1km': 1, '10km': 10, '100km': 100 };

    // Radius of the distance scopes. Every other scope (countrywide, region, city,
    // road, segment, unique) matches by name / geometry only, so its radius is 0.
    function getDistanceForScope(scope) {
        return SCOPE_RADIUS_KM[normalizeScope(scope)] || 0;
    }

    const COUNTRY_ALIAS_MAP = {
        "france": (lat, lng) => {
            // Reunion Check
            if (lat < -19 && lat > -22 && lng > 54 && lng < 57) return "Reunion";
            return "France";
        },
        "china": (lat, lng) => {
            // Hong Kong / Macau Check
            if (lat > 22 && lat < 23 && lng > 113.8 && lng < 114.5) return "Hong Kong";
            if (lat > 22 && lat < 22.3 && lng > 113.5 && lng < 113.6) return "Macau";
            return "China";
        },
        "usa": "United States of America",
        "united states": "United States of America",
        "united states of america": "United States of America",
        "uk": "United Kingdom",
        "united kingdom": "United Kingdom",
        "uae": "United Arab Emirates",
        "united arab emirates": "United Arab Emirates",
        "virgin islands, u.s.": "US Virgin Islands",
        "u.s. virgin islands": "US Virgin Islands",
        "us virgin islands": "US Virgin Islands"
    };

    function normalizeCountry(name, lat, lng) {
        if (!name) return "Unknown";
        let target = name;
        const aliasKey = String(name).trim().toLowerCase();
        if (COUNTRY_ALIAS_MAP[aliasKey]) {
            const mapping = COUNTRY_ALIAS_MAP[aliasKey];
            if (typeof mapping === 'function') {
                target = mapping(parseFloat(lat), parseFloat(lng));
            } else {
                target = mapping;
            }
        }
        return target;
    }

    function stripDiacritics(value) {
        return String(value || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '');
    }

    function normalizeNameForMatch(value) {
        return stripDiacritics(String(value || '')).toLowerCase().trim();
    }

    /**
     * Strict name matching for location names (accent/case-insensitive exact match).
     * No generic-word filtering: the stored name must match the detected name exactly
     * (after normalization). Empty names never match.
     */
    function isSameName(a, b) {
        if (!a || !b) return false;
        return normalizeNameForMatch(a) === normalizeNameForMatch(b);
    }

    /**
     * Finds the metas relevant to the current location: distance scopes by haversine
     * distance, name scopes (country / region / city / road) by exact normalized name,
     * segments by road and rectangle.
     */
    function evaluateProximityMetas() {
        const curLat = normalizeCoordinate(currentLocationData.lat);
        const curLng = normalizeCoordinate(currentLocationData.lng);
        if (curLat === null || curLng === null) return [];

        const curCountry = normalizeCountry(currentLocationData.country, curLat, curLng);
        const curNomCountry = normalizeCountry(currentLocationData.nominatimCountry, curLat, curLng);
        const curRegion = currentLocationData.region;
        const curCity = currentLocationData.city;

        const curRoads = getRoadScopeNames();
        const curRoadKeys = getRoadCandidateKeys(currentLocationData.roadSources);

        // Names are normalized once here and once per data change in the index
        // (see rebuildProximityIndexes), not on every comparison.
        const curRegionKey = normalizeNameForMatch(curRegion);
        const curCityKey = normalizeNameForMatch(curCity);
        const curRoadNameKeys = curRoads.map(normalizeNameForMatch).filter(Boolean);

        const matchedMetaIds = new Set();
        const matches = [];
        if (proximityIndexDirty) rebuildProximityIndexes();
        const proximityCacheKey = JSON.stringify([
            proximityIndexVersion,
            curLat,
            curLng,
            curCountry,
            curNomCountry,
            curRegion || '',
            curCity || '',
            curRoads,
            curRoadKeys
        ]);
        if (proximityCacheKey === lastProximityCacheKey) return lastProximityMatches;

        // Helper: Check meta match against location
        const checkMatch = (scope, entry) => {
             scope = normalizeScope(scope);

             // 1. Distance Match
             const distLimit = getDistanceForScope(scope);
             if (distLimit > 0) {
                 if (entry.lat !== null && entry.lng !== null) {
                     return getHaversineDistance(curLat, curLng, entry.lat, entry.lng) <= distLimit;
                 }
                 return false;
             }

             // 2. Name Match (Region/City/Road)
             // Requires Country match to avoid ambiguity (except Countrywide)
             const countryMatch = (entry.country === curCountry || entry.country === curNomCountry);
             if (!countryMatch) return false;

             if (scope === 'countrywide') return true;

             if (scope === 'region') {
                 return !!curRegionKey && entry.regionKey === curRegionKey;
             }

             if (scope === 'city') {
                 if (!curCityKey || entry.cityKey !== curCityKey) return false;
                 // Same city name in another region is a different city. The
                 // region is only ignored when either side has no region data.
                 if (entry.regionKey && curRegionKey && entry.regionKey !== curRegionKey) return false;
                 return true;
             }

             if (scope === 'road') {
                 // Check if ANY entry road matches ANY current road
                 return curRoadNameKeys.some(key => entry.roadKeys.includes(key));
             }

             return false;
        };

        // Location values are normalized once per data change, not on every HUD refresh.
        indexedLocationEntries.forEach(entry => {
            entry.metaIds.forEach(id => {
                 if (matchedMetaIds.has(id)) return; // Already matched
                 const meta = getMetaById(id);
                 if (!meta) return;

                 if (checkMatch(meta.scope, entry)) {
                     matchedMetaIds.add(id);
                     matches.push(meta);
                 }
            });
        });

        // Segments: on one of the roads of the stretch (name or ref) and inside its rectangle.
        if (curRoadKeys.length > 0) {
            indexedSegments.forEach(seg => {
                if (matchedMetaIds.has(seg.metaId)) return;
                if (seg.country !== curCountry && seg.country !== curNomCountry) return;
                if (!seg.roads.some(road => curRoadKeys.includes(road))) return;
                const meta = getMetaById(seg.metaId);
                if (!meta || normalizeScope(meta.scope) !== 'segment') return;
                if (isInsideSegment(curLat, curLng, seg.points)) {
                    matchedMetaIds.add(seg.metaId);
                    matches.push(meta);
                }
            });
        }

        lastProximityCacheKey = proximityCacheKey;
        lastProximityMatches = matches;
        return matches;
    }

    function isRoundResult() {
        return document.querySelector('[alt="Correct location"]') !== null;
    }

    function updateVisibility(resultActive = isRoundResult()) {
        const hud = document.getElementById('gg-meta-hud');
        if (!hud) return;

        hud.classList.toggle('gg-visible', resultActive);
    }

    function checkLocation(panoid, options = {}) {
        if (!panoid || typeof panoid !== 'string' || panoid.length <= 5) return;

        // Lock Mechanism:
        // If on result screen, queue updates instead of applying immediately
        // to prevent UI jitter when reviewing previous rounds.
        const onResultScreen = isRoundResult();
        const shouldHoldForResult = onResultScreen && !userDismissed && !options.bypassResultLock;
        if (currentPanoid && currentPanoid !== panoid && shouldHoldForResult) {
            if (nextPanoid !== panoid) nextPanoidQueuedAt = Date.now();
            nextPanoid = panoid;
            return;
        }

        const changed = (panoid !== currentPanoid);
        currentPanoid = panoid;
        nextPanoid = null;
        nextPanoidQueuedAt = 0;

        // StreetView reports the same panoid several times per move (delayed
        // reads, status events): nothing to do unless it really changed. Display
        // refreshes for new data (DB load, geocoding) are triggered by their owners.
        if (!changed) return;

        debugLog('[BetterMetas] New Location detected:', panoid);
        updateStatus(`ID: ${panoid.substring(0,12)}...`);

        // Trigger Location Data Extraction Immediately
        extractLocationData();
        refreshDisplay();
    }

    const GEOCODE_DEDUP_MS = 10000;

    // Geocoding answers arrive late: they only apply if the displayed location is
    // still the one they were requested for.
    function isCurrentLocation(latStr, lngStr) {
        return currentLocationData.lat === latStr && currentLocationData.lng === lngStr;
    }

    // Rough country guess from a StreetView description ("Street, City, Country").
    // It can be wrong (a region, a zip code): the geocoders replace it.
    function guessCountryFromDescription(desc) {
        if (!desc.includes(',')) return desc;

        const parts = desc.split(',');
        let country = parts[parts.length - 1].trim();
        // Skip a trailing zip code.
        if (/^\d+$/.test(country) && parts.length > 1) {
            country = parts[parts.length - 2].trim();
        }
        return country;
    }

    function parseGoogleGeocode(results) {
        let country = null;
        let region = null;
        let city = null;
        let cityFallback = null;
        const roadSource = { names: [], refs: [] };

        results[0].address_components.forEach(comp => {
            if (comp.types.includes('country')) country = comp.long_name;
            if (comp.types.includes('administrative_area_level_1')) region = comp.long_name;
            if (comp.types.includes('locality') || comp.types.includes('postal_town')) {
                if (!city) city = comp.long_name; // Prefer locality
            } else if (comp.types.includes('administrative_area_level_2')) {
                if (!cityFallback) cityFallback = comp.long_name;
            }
            if (comp.types.includes('route')) addGoogleRouteComponent(roadSource, comp);
        });

        // Other results can expose the same road under another name/ref
        results.slice(1, 5).forEach(result => {
            if (!result.types || !result.types.includes('route')) return;
            (result.address_components || []).forEach(comp => {
                if (comp.types.includes('route')) addGoogleRouteComponent(roadSource, comp);
            });
        });

        return { country, region, city: city || cityFallback, roadSource };
    }

    function applyGoogleGeocode(parsed, latStr, lngStr, lat, lng) {
        if (!isCurrentLocation(latStr, lngStr)) return;

        currentLocationData.googleCountry = parsed.country;
        // Primary country selection (Google preferred)
        if (parsed.country) {
            currentLocationData.country = normalizeCountry(parsed.country, lat, lng);
        }

        currentLocationData.placeSources = currentLocationData.placeSources || newPlaceSources();
        currentLocationData.placeSources.google = { region: parsed.region, city: parsed.city };
        applyPlaceNames();
        if (parsed.roadSource.names.length || parsed.roadSource.refs.length) {
            currentLocationData.roadSources = currentLocationData.roadSources || newRoadSources();
            currentLocationData.roadSources.google = parsed.roadSource;
            currentLocationData.road = chooseRoad(currentLocationData.roadSources);
        }

        updateLocationUI();
        refreshDisplay();
    }

    // Google Geocoding (dominant for the country).
    function geocodeWithGoogle(latStr, lngStr, lat, lng) {
        sharedGeocoder ||= new win.google.maps.Geocoder();
        sharedGeocoder.geocode({ location: { lat, lng } }, (results, status) => {
            if (status === 'OK' && results[0]) {
                applyGoogleGeocode(parseGoogleGeocode(results), latStr, lngStr, lat, lng);
            } else {
                console.warn('[BetterMetas] Google geocode failed:', status);
            }
            markGeocodeDone('google', latStr, lngStr);
        });
    }

    // `fallbackCountry` is the description-based guess, `loc` the StreetView location.
    function parseNominatimGeocode(data, fallbackCountry, lat, lng, loc) {
        const a = data.address;
        const country = normalizeCountry(a.country || fallbackCountry, lat, lng);
        const region = a.state || a.region || a.province || null;
        const city = a.city || a.municipality || a.town || a.village || null;

        // Road Logic: names and refs of the road (no suburb/hamlet/village,
        // which are places, not roads). OSM "ref" tags are real refs.
        const roadSource = { names: [], refs: [] };
        const splitTag = v => String(v || '').split(';').map(x => x.trim()).filter(Boolean);
        [a.road, a.pedestrian, a.highway, a.street].forEach(v => roadSource.names.push(...splitTag(v)));
        if (data.class === 'highway' || data.category === 'highway') {
            const nd = data.namedetails || {};
            const ex = data.extratags || {};
            [nd.name, nd.official_name, nd.alt_name].forEach(v => roadSource.names.push(...splitTag(v)));
            [nd.ref, ex.ref, ex.int_ref].forEach(v => roadSource.refs.push(...splitTag(v)));
        }
        let road = chooseRoad({ google: { names: [], refs: [] }, nominatim: roadSource });

        // Fallback: If still no road, use shortDescription if it looks like a road
        const shortDescription = loc.shortDescription;
        if (!road && shortDescription && shortDescription !== loc.description && shortDescription !== country &&
            shortDescription !== region && shortDescription !== city) {
            road = shortDescription;
        }

        return { address: data.display_name, country, region, city, roadSource, road };
    }

    function applyNominatimGeocode(parsed, latStr, lngStr) {
        if (isCurrentLocation(latStr, lngStr)) {
            currentLocationData.nominatimCountry = parsed.country;
            currentLocationData.address = parsed.address; // Prefer Nominatim address

            // Fallback for Country if Google gave none. The country seeded from
            // the description is only a guess (it can be a region: "Napo"),
            // so Nominatim's replaces it.
            if (!currentLocationData.googleCountry) {
                currentLocationData.country = parsed.country;
            }

            currentLocationData.placeSources = currentLocationData.placeSources || newPlaceSources();
            currentLocationData.placeSources.nominatim = { region: parsed.region, city: parsed.city };
            applyPlaceNames();
            if (parsed.road) {
                const { roadSource } = parsed;
                if (!roadSource.names.length && !roadSource.refs.length) roadSource.names.push(parsed.road);
                currentLocationData.roadSources = currentLocationData.roadSources || newRoadSources();
                currentLocationData.roadSources.nominatim = roadSource;
                currentLocationData.road = chooseRoad(currentLocationData.roadSources);
            }
        }

        updateLocationUI();
        refreshDisplay();
    }

    // Nominatim Geocoding (detail/fallback).
    function geocodeWithNominatim(latStr, lngStr, lat, lng, fallbackCountry, loc) {
        const geocodeKey = `${latStr},${lngStr}`;
        const url = `https://nominatim.openstreetmap.org/reverse?format=json&lat=${lat}&lon=${lng}&accept-language=en&extratags=1&namedetails=1`;
        if (activeNominatimController && activeNominatimKey !== geocodeKey) {
            activeNominatimController.abort();
        }
        const controller = new AbortController();
        activeNominatimController = controller;
        activeNominatimKey = geocodeKey;

        fetch(url, { signal: controller.signal })
            .then(response => response.json())
            .then(data => {
                if (data && data.address) {
                    applyNominatimGeocode(parseNominatimGeocode(data, fallbackCountry, lat, lng, loc), latStr, lngStr);
                }
            })
            .catch(error => {
                if (error?.name !== 'AbortError') {
                    console.error('[BetterMetas] Nominatim geocode failed:', error);
                }
            })
            .finally(() => {
                markGeocodeDone('nominatim', latStr, lngStr);
                if (activeNominatimController === controller) {
                    activeNominatimController = null;
                    activeNominatimKey = null;
                }
            });
    }

    function extractLocationData(attempt = 0, extractionId = null) {
        const maxAttempts = 10;
        if (extractionId === null) {
            extractionId = ++locationExtractionSequence;
        }
        if (extractionId !== locationExtractionSequence) return;

        if (!svInstance) {
            debugLog(`[BetterMetas] extractLocationData: No svInstance available yet (Attempt ${attempt+1}/${maxAttempts}).`);
            if (attempt < maxAttempts) {
                setTimeout(() => extractLocationData(attempt + 1, extractionId), STREETVIEW_RETRY_DELAY_MS);
            }
            return;
        }

        if (attempt === 0) debugLog('[BetterMetas] extractLocationData: Triggered.');

        // Give it a moment for data to populate in the instance if it's fresh
        setTimeout(() => {
            if (extractionId !== locationExtractionSequence) return;
            try {
                const loc = typeof svInstance.getLocation === 'function' ? svInstance.getLocation() : null;
                const latLng = loc && loc.latLng;
                const lat = latLng ? (typeof latLng.lat === 'function' ? latLng.lat() : latLng.lat) : NaN;
                const lng = latLng ? (typeof latLng.lng === 'function' ? latLng.lng() : latLng.lng) : NaN;

                // No coordinates yet: never fall back to (0, 0), try again shortly.
                if (!Number.isFinite(lat) || !Number.isFinite(lng)) {
                    debugLog(`[BetterMetas] svInstance.getLocation() returned no coordinates (Attempt ${attempt+1}/${maxAttempts}).`);
                    if (attempt < maxAttempts) {
                        extractLocationData(attempt + 1, extractionId);
                    }
                    return;
                }

                const desc = loc.description || loc.shortDescription || 'Unknown Location';
                debugLog(`[BetterMetas] Location Found: ${desc} (${lat}, ${lng})`);

                const country = guessCountryFromDescription(desc);
                const latStr = lat.toFixed(5);
                const lngStr = lng.toFixed(5);

                // Check if we already have this location data to prevent overwriting with nulls during race conditions
                if (currentLocationData && isCurrentLocation(latStr, lngStr)) {
                    // Location hasn't changed. If we already have a Road, don't wipe it out!
                    if (currentLocationData.road) {
                        debugLog('[BetterMetas] Road already exists for this location, skipping reset/re-geocode.');
                        refreshDisplay();
                        return;
                    }

                    // No road yet: carry over the existing country/address and let the
                    // geocoders below fetch region and road again.
                    currentLocationData.address = currentLocationData.address || desc;
                    currentLocationData.country = currentLocationData.country || country;
                } else {
                    // New location, reset
                    currentLocationData = {
                        address: desc,
                        country: country,
                        region: null,
                        city: null,
                        road: null,
                        roadSources: newRoadSources(),
                        placeSources: newPlaceSources(),
                        geocodeDone: { google: false, nominatim: false },
                        lat: latStr,
                        lng: lngStr
                    };
                }

                updateLocationUI();

                // Immediate refresh with basic info (Lat/Lng is enough for radius checks)
                refreshDisplay();

                const geocodeKey = `${latStr},${lngStr}`;
                if (recentlyGeocodedLocations.has(geocodeKey)) {
                    debugLog('[BetterMetas] Geocoding already running for this location.');
                    return;
                }
                recentlyGeocodedLocations.add(geocodeKey);
                setTimeout(() => recentlyGeocodedLocations.delete(geocodeKey), GEOCODE_DEDUP_MS);
                currentLocationData.geocodeDone = { google: false, nominatim: false };

                geocodeWithGoogle(latStr, lngStr, lat, lng);
                geocodeWithNominatim(latStr, lngStr, lat, lng, country, loc);
            } catch (e) {
                console.warn('[BetterMetas] Error accessing location data:', e);
            }
        }, STREETVIEW_RETRY_DELAY_MS);
    }

    function updateLocationUI() {
        const box = document.getElementById('gg-location-info');
        debugLog('[BetterMetas] updateLocationUI called. Box:', box, 'Data:', currentLocationData);
        if (!box) return;

        // Respect configuration
        if (!SHOW_LOCATION_HUD) {
            box.style.display = 'none';
            return;
        }

        const { address, country, region, road, lat, lng } = currentLocationData;
        const roadLabel = Array.isArray(road) ? road.join(', ') : road;

        if (!lat || !lng) {
            debugLog('[BetterMetas] updateLocationUI: Missing lat/lng, hiding box.');
            box.style.display = 'none';
            return;
        }

        box.innerHTML = `
            <div class="gg-loc-row">
                <div class="gg-loc-label">Address:</div>
                <div class="gg-loc-val">${escapeHtml(address || 'N/A')}</div>
            </div>
             <div class="gg-loc-row">
                <div class="gg-loc-label">Country:</div>
                <div class="gg-loc-val gg-loc-val-country">${escapeHtml(country || 'N/A')}</div>
            </div>
            ${region ? `
            <div class="gg-loc-row">
                <div class="gg-loc-label">Region:</div>
                <div class="gg-loc-val">${escapeHtml(region)}</div>
            </div>` : ''}
            ${currentLocationData.city ? `
            <div class="gg-loc-row">
                <div class="gg-loc-label">City:</div>
                <div class="gg-loc-val">${escapeHtml(currentLocationData.city)}</div>
            </div>` : ''}
            ${roadLabel ? `
            <div class="gg-loc-row">
                <div class="gg-loc-label">Road:</div>
                <div class="gg-loc-val">${escapeHtml(roadLabel)}</div>
            </div>` : ''}
        `;
        box.style.display = 'block';
    }




    // --- Local dev-server writes ---
    // All saves are written straight to the local dev server (see
    // local-server.js): no token, no network commit involved.
    // The server exposes a PUT route per data file that overwrites it on disk.
    function requestLocalWrite(method, file, rawBody) {
        return new Promise((resolve, reject) => {
            GM_xmlhttpRequest({
                method,
                url: getRawFileUrl(file),
                headers: { 'Content-Type': 'application/json' },
                data: rawBody,
                timeout: LOCAL_WRITE_TIMEOUT_MS,
                onload: resolve,
                onerror: () => reject(new Error(`Local server ${method} ${file} request failed`)),
                ontimeout: () => reject(new Error(`Local server ${method} ${file} request timed out`))
            });
        });
    }

    async function putLocalJsonFile(file, content) {
        // Send content pre-formatted (indented, unicode-escaped) so the file
        // on disk stays human-readable instead of collapsing to one line.
        const response = await requestLocalWrite('PUT', file, stringifyJsonContent(content));
        if (response.status < 200 || response.status >= 300) {
            throw new Error(`Local server PUT ${file} HTTP ${response.status}: ${response.responseText || response.statusText || 'unknown error'}`);
        }
    }

    let localWriteQueue = Promise.resolve();

    function withLocalWriteQueue(operation) {
        const run = localWriteQueue.catch(() => {}).then(operation);
        localWriteQueue = run.catch(() => {});
        return run;
    }

    async function updateLocalJsonFileWithOptions(file, normalizeContent, updateContent, message, skipUnchanged) {
        return withLocalWriteQueue(async () => {
            const raw = await fetchRawJsonWithRetry(() => getRawFileUrl(file), file, value => value, null, { allowMissing: true });
            const content = normalizeContent(raw);
            // Normalizing silently drops anything that does not have the expected
            // shape (e.g. an object where a list is expected, after a hand edit):
            // refuse to write that back over the file.
            if (raw !== null && Array.isArray(raw) !== Array.isArray(content)) {
                throw new Error(`${file} does not have the expected format; fix the file before saving from BetterMetas.`);
            }
            const before = skipUnchanged ? stringifyJsonContent(content) : null;
            const updatedContent = updateContent(content) || content;

            if (skipUnchanged && before === stringifyJsonContent(updatedContent)) {
                return { skipped: true };
            }

            console.log(`[BetterMetas] Writing ${file} locally: ${message}`);
            await putLocalJsonFile(file, updatedContent);
            return { skipped: false };
        });
    }

    function updateLocalJsonFile(file, normalizeContent, updateContent, message) {
        return updateLocalJsonFileWithOptions(file, normalizeContent, updateContent, message, false);
    }

    function updateLocalJsonFileIfChanged(file, normalizeContent, updateContent, message) {
        return updateLocalJsonFileWithOptions(file, normalizeContent, updateContent, message, true);
    }

    function wait(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }

    function requestRawText(url, label) {
        return new Promise((resolve, reject) => {
            // Cache-bust: the local dev server always serves the same URL for
            // a given file, so browsers/GM_xmlhttpRequest can happily return a
            // stale cached body (e.g. a just-deleted meta reappearing) unless
            // we make every read look like a distinct request.
            const bustedUrl = `${url}${url.includes('?') ? '&' : '?'}_=${Date.now()}`;
            GM_xmlhttpRequest({
                method: "GET",
                url: bustedUrl,
                headers: {
                    'Cache-Control': 'no-cache, no-store, must-revalidate',
                    'Pragma': 'no-cache'
                },
                timeout: DATA_FETCH_TIMEOUT_MS,
                onload: resolve,
                onerror: () => reject(new Error(`${label} request failed`)),
                ontimeout: () => reject(new Error(`${label} request timed out`))
            });
        });
    }

    async function fetchRawJsonWithRetry(urlFactory, label, normalize, defaultValue, options = {}) {
        let lastError = null;

        for (let attempt = 1; attempt <= DATA_FETCH_MAX_ATTEMPTS; attempt++) {
            try {
                const response = await requestRawText(urlFactory(), label);
                if (response.status === 200) {
                    return normalize(JSON.parse(response.responseText));
                }

                if (options.allowMissing && (response.status === 404 || response.status === 204)) {
                    return defaultValue;
                }

                throw new Error(`${label} HTTP ${response.status}: ${response.statusText || 'unknown error'}`);
            } catch (err) {
                lastError = err;
                if (attempt < DATA_FETCH_MAX_ATTEMPTS) {
                    console.warn(`[BetterMetas] ${label} load failed (attempt ${attempt}/${DATA_FETCH_MAX_ATTEMPTS}), retrying:`, err);
                    await wait(DATA_FETCH_RETRY_DELAY_MS * attempt);
                }
            }
        }

        // Only a real "file does not exist" (404/204, handled above) may fall back to
        // the default. Any other failure (server down, timeout, invalid JSON) must
        // throw: callers write the result back to disk, and an empty fallback would
        // overwrite the whole data file with just the new entry.
        throw lastError || new Error(`${label} load failed`);
    }

    async function loadDataSource(options) {
        const data = await fetchRawJsonWithRetry(
            () => getRawFileUrl(options.file),
            options.logName,
            options.normalize,
            options.defaultValue,
            { allowMissing: options.allowMissing }
        );
        debugLog(`[BetterMetas] Loaded ${options.count(data)} ${options.description}.`);
        return data;
    }

    const locationCount = (data) => Object.keys(data).length;
    const metaCount = (data) => data.length;
    const DATA_SOURCES = {
        userLocations: { file: USER_LOCATIONS_FILE, logName: 'user_locations.json', normalize: normalizeLocationMap, defaultValue: {}, allowMissing: true, count: locationCount, description: 'user location mappings' },
        userMetas: { file: USER_METAS_FILE, logName: 'user_metas.json', normalize: normalizeMetaList, defaultValue: [], allowMissing: true, count: metaCount, description: 'user metas' },
    };

    // --- Data Fetching ---
    async function fetchLocationData() {
        debugLog('[BetterMetas] Fetching data...');
        updateStatus(metasData.length > 0 ? 'Refreshing DB...' : 'Loading DB...');
        const loadId = ++dataLoadSequence;

        try {
            const [loadedUserLocationMap, loadedUserMetas] = await Promise.all([
                loadDataSource(DATA_SOURCES.userLocations),
                loadDataSource(DATA_SOURCES.userMetas)
            ]);

            if (loadId !== dataLoadSequence) {
                debugLog('[BetterMetas] Ignoring stale DB load result.');
                return;
            }

            const snapshot = {
                userLocationMap: loadedUserLocationMap,
                userMetas: loadedUserMetas
            };
            const applied = applyDataSnapshot(snapshot, { prunePending: true, alreadyNormalized: true });
            saveDataSnapshotCache(snapshot);

            const pendingLocCount = Object.keys(applied.pending.locations).length;
            debugLog(`[BetterMetas] DB Ready: ${Object.keys(userLocationMap).length} locs, ${metasData.length} metas. Pending local merge: ${applied.pending.metas.length} metas, ${pendingLocCount} locs.`);

            syncPanoidForUserAction('DB ready');

            if (currentPanoid) {
                 updateStatus(`ID: ${currentPanoid.substring(0,12)}...`);
                 refreshDisplay();
            } else {
                 updateStatus(`DB Ready (${metasData.length} metas)`);
            }
        } catch (err) {
            if (loadId !== dataLoadSequence) return;
            useFallback(err && err.message ? err.message : 'Data Load Error');
        }
    }

    function useFallback(reason) {
        console.warn(`[BetterMetas] Could not load data. Reason: ${reason}`);
        if (metasData.length > 0) {
            updateStatus(`Using cached DB (${metasData.length} metas)`);
            refreshDisplay();
            return;
        }

        updateStatus(`Offline (${reason})`);
    }



    // --- Google Maps Hooks ---
    function watchConfigurableProperty(target, prop, onSet) {
        if (!target) return false;

        const descriptor = Object.getOwnPropertyDescriptor(target, prop);
        if (descriptor && descriptor.configurable === false) return false;

        let currentValue = descriptor && descriptor.get ? descriptor.get.call(target) : target[prop];
        Object.defineProperty(target, prop, {
            configurable: true,
            enumerable: descriptor ? descriptor.enumerable : true,
            get() {
                return descriptor && descriptor.get ? descriptor.get.call(target) : currentValue;
            },
            set(value) {
                if (descriptor && descriptor.set) {
                    descriptor.set.call(target, value);
                } else {
                    currentValue = value;
                }
                onSet(value);
            }
        });

        if (currentValue) onSet(currentValue);
        return true;
    }

    function queueHookInstall(delay = 0) {
        setTimeout(() => {
            installNestedGoogleWatchers();
            installHooks();
        }, delay);
    }

    function installNestedGoogleWatchers() {
        const googleObject = win.google;
        if (!googleObject || typeof googleObject !== 'object') return;

        if (watchedGoogleObject !== googleObject) {
            watchedGoogleObject = googleObject;
            watchConfigurableProperty(googleObject, 'maps', () => {
                installNestedGoogleWatchers();
                queueHookInstall();
            });
        }

        const mapsObject = googleObject.maps;
        if (!mapsObject || typeof mapsObject !== 'object') return;

        if (watchedMapsObject !== mapsObject) {
            watchedMapsObject = mapsObject;
            watchConfigurableProperty(mapsObject, 'StreetViewPanorama', () => {
                queueHookInstall();
            });
        }
    }

    function installGoogleHookWatcher() {
        if (googleWatcherInstalled) return;
        googleWatcherInstalled = true;

        watchConfigurableProperty(win, 'google', () => {
            installNestedGoogleWatchers();
            queueHookInstall();
        });

        installNestedGoogleWatchers();
        queueHookInstall();
    }

    function installHooks() {
        if (hooksInstalled) return true;

        // Check for Maps API
        if (!win.google || !win.google.maps || !win.google.maps.StreetViewPanorama) {
            return false;
        }

        debugLog('[BetterMetas] Google Maps API found. Installing hooks...');

        // 1. Hook StreetViewPanorama Constructor
        const OriginalStreetViewPanorama = win.google.maps.StreetViewPanorama;
        if (OriginalStreetViewPanorama.__betterMetasHooked) {
            hooksInstalled = true;
            return true;
        }

        win.google.maps.StreetViewPanorama = function(node, opts) {
            const instance = new OriginalStreetViewPanorama(node, opts);

            registerStreetViewInstance(instance, 'constructor');
            if (opts && isValidPanoid(opts.pano)) {
                checkLocation(opts.pano);
            }

            return instance;
        };
        win.google.maps.StreetViewPanorama.__betterMetasHooked = true;

        // Copy statics
        win.google.maps.StreetViewPanorama.prototype = OriginalStreetViewPanorama.prototype;
        for (let prop in OriginalStreetViewPanorama) {
            if (OriginalStreetViewPanorama.hasOwnProperty(prop)) {
                win.google.maps.StreetViewPanorama[prop] = OriginalStreetViewPanorama[prop];
            }
        }

        // 2. Hook setPano (for SPA updates)
        const originalSetPano = win.google.maps.StreetViewPanorama.prototype.setPano;
        if (typeof originalSetPano === 'function' && !originalSetPano.__betterMetasHooked) {
            win.google.maps.StreetViewPanorama.prototype.setPano = function(pano) {
                registerStreetViewInstance(this, 'setPano');
                const result = originalSetPano.apply(this, arguments);
                if (isValidPanoid(pano)) checkLocation(pano);
                setTimeout(() => readPanoidFromStreetView(this, 'setPano applied'), 0);
                return result;
            };
            win.google.maps.StreetViewPanorama.prototype.setPano.__betterMetasHooked = true;
        }

        const originalSetPosition = win.google.maps.StreetViewPanorama.prototype.setPosition;
        if (typeof originalSetPosition === 'function' && !originalSetPosition.__betterMetasHooked) {
            win.google.maps.StreetViewPanorama.prototype.setPosition = function() {
                registerStreetViewInstance(this, 'setPosition');
                const result = originalSetPosition.apply(this, arguments);
                setTimeout(() => readPanoidFromStreetView(this, 'setPosition applied'), 0);
                setTimeout(() => readPanoidFromStreetView(this, 'setPosition settled'), 300);
                return result;
            };
            win.google.maps.StreetViewPanorama.prototype.setPosition.__betterMetasHooked = true;
        }

        hooksInstalled = true;
        debugLog('[BetterMetas] Hooks installed successfully.');
        return true;
    }



    function startObserver() {
         installGoogleHookWatcher();

         // UI Poller
         const runVisibilityPoll = () => {
             if (document.hidden) return;
             const resultActive = isRoundResult();
             updateVisibility(resultActive);

             // Release immediately after an intentional dismissal. As a final
             // fallback, trust a stable StreetView pano even if GeoGuessr leaves
             // a stale result element mounted in the DOM.
             const visiblePanoid = getStreetViewPanoid();
             const queuedPanoidConfirmed = visiblePanoid === nextPanoid;
             const queueExpired = nextPanoidQueuedAt > 0
                 && Date.now() - nextPanoidQueuedAt >= QUEUED_PANO_FORCE_MS;
             if (nextPanoid && (!resultActive || userDismissed || (queuedPanoidConfirmed && queueExpired))) {
                 debugLog('[BetterMetas] Applying queued panoid:', nextPanoid);
                 checkLocation(nextPanoid, { bypassResultLock: true });
             }

             // The result screen is gone: re-arm the lock for the next result screen
             // (otherwise it would only ever work for the first round).
             if (!resultActive) userDismissed = false;
         };
         setInterval(runVisibilityPoll, VISIBILITY_POLL_INTERVAL_MS);
         document.addEventListener('visibilitychange', () => {
             if (!document.hidden) runVisibilityPoll();
         });

         // Fallback for the property watchers above (installGoogleHookWatcher), which
         // normally catch google.maps the moment it appears: a slow poll with backoff,
         // instead of a 25 ms loop that never ends on pages without Google Maps.
         let hookPollDelay = HOOK_POLL_MIN_DELAY_MS;
         const pollForHooks = () => {
            if (installHooks()) return;
            hookPollDelay = Math.min(hookPollDelay * 2, HOOK_POLL_MAX_DELAY_MS);
            setTimeout(pollForHooks, hookPollDelay);
         };
         setTimeout(pollForHooks, hookPollDelay);

         // Input Capture for Instant Hide
         document.addEventListener('keydown', (e) => {
             if (e.code === 'Space' || e.key === ' ') {
                 // Only hide if currently visible (on result screen)
                 // And ensure we aren't typing in an input
                 const activeTag = document.activeElement?.tagName?.toLowerCase() || '';
                 if (activeTag === 'input' || activeTag === 'textarea') return;

                 if (isRoundResult()) {
                     userDismissed = true;
                     const hud = document.getElementById('gg-meta-hud');
                     if (hud) {
                         // Instant hide via class removal (transitions out)
                         hud.classList.remove('gg-visible');
                     }
                 }
             }
         }, true);

         // Next Button Click Capture (Heuristic)
         document.addEventListener('click', (e) => {
             // Look for buttons that might be "Next" or "Play Again"
             // This is a best-effort heuristic based on common button texts or classes
             const target = getEventElementTarget(e);
             const button = target ? target.closest('button') : null;
             if (!button) return;

             // Check if we are on result screen
             if (isRoundResult()) {
                  // If we click ANY button on result screen that isn't inside our HUD or modals, hide HUD
                  // Exclude: HUD and BetterMetas modals/dialogs
                  if (!button.closest('#gg-meta-hud') &&
                      !button.closest('#gg-settings-modal') &&
                      !button.closest('#gg-meta-modal') &&
                      !button.closest('#gg-meta-admin-modal') &&
                      !button.closest('#gg-dialog-modal')) {
                       userDismissed = true;

                       // Close HUD
                       const hud = document.getElementById('gg-meta-hud');
                       if (hud && hud.classList.contains('gg-visible')) {
                           hud.classList.remove('gg-visible');
                       }

                       // Close Modals
                       hideAllModals();
                  }
             }
         }, true); // Capture phase to catch it early

         debugLog('[BetterMetas] Observer started.');
    }

    // --- Initialization ---
    function initUI() {
        if (uiInitialized) return true;
        if (!document.body) return false;

        uiInitialized = true;
        debugLog('[BetterMetas] Initializing UI...');
        addStyles();
        createHUD();
        applyCachedDataSnapshot();
        fetchLocationData();
        return true;
    }

    function scheduleUIInit() {
        if (initUI()) return;

        // The script runs at document-start: wait for the DOM, once.
        document.addEventListener('DOMContentLoaded', initUI, { once: true });
    }

    function init() {
        debugLog('[BetterMetas] Initializing...');
        startObserver();
        scheduleUIInit();
    }

    init();

})();
