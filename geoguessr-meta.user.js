// ==UserScript==
// @name         BetterMetas
// @namespace    http://tampermonkey.net/
// @version      0.11
// @description  Displays crowdsourced metas and hints for Geoguessr locations.
// @author       Lukas Hzb
// @updateURL    https://github.com/lukas-hzb/better_metas/raw/refs/heads/main_v4/geoguessr-meta.user.js
// @downloadURL  https://github.com/lukas-hzb/better_metas/raw/refs/heads/main_v4/geoguessr-meta.user.js
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
    const DEFAULT_HUD_WIDTH = '320px';
    const DEFAULT_HUD_HEIGHT = '75.6vh';
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
            snapshot.road = currentLocationData.road || null;
        }

        return snapshot;
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

    function getCombinedLocationEntry(panoid) {
        return userLocationMap[panoid] || null;
    }

    function forEachCombinedLocationEntry(callback) {
        Object.entries(userLocationMap).forEach(([panoid, entry]) => callback(panoid, entry));
    }

    function getCombinedLocationCount() {
        return Object.keys(userLocationMap).length;
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
        return isFuzzyNameMatch(a, b);
    }

    // Does this location entry have EXACTLY the shape required by `scope` for the
    // current location? The shape is:
    //   countrywide / 100km / 10km / 1km / unique -> region, city, road all empty
    //   region -> same region, no city, no road
    //   city   -> same region + same city, no road
    //   road   -> a shared road name, no region, no city
    // Because the shape is exact, an entry created for one scope is never reused
    // (and therefore never "upgraded" with extra fields) by a meta of another scope.
    function entryFitsScope(entry, scope) {
        if (!entry || typeof entry !== 'object' || Array.isArray(entry)) return false;
        const normalizedScope = normalizeScope(scope);
        const entryRoads = getNormalizedRoadNames(entry.road);
        const hasRoad = entryRoads.length > 0;

        if (normalizedScope === 'region') {
            return isSameNullableName(entry.region, currentLocationData.region) &&
                !entry.city && !hasRoad;
        }
        if (normalizedScope === 'city') {
            return isSameNullableName(entry.region, currentLocationData.region) &&
                isSameNullableName(entry.city, currentLocationData.city) && !hasRoad;
        }
        if (normalizedScope === 'road') {
            const curRoads = getNormalizedRoadNames(currentLocationData.road);
            return !entry.region && !entry.city && hasRoad && curRoads.length > 0 &&
                curRoads.some(cr => entryRoads.some(er => isFuzzyNameMatch(cr, er)));
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
    const SCOPED_KEY_SUFFIX_RE = /^(countrywide|region|city|road|100km|10km|1km|unique)(_\d+)?$/;

    function isOwnLocationKey(key, panoid) {
        if (key === panoid) return true;
        return key.startsWith(panoid + '__') && SCOPED_KEY_SUFFIX_RE.test(key.slice(panoid.length + 2));
    }

    function getOwnLocationKeys(locations, panoid) {
        if (!locations || !panoid) return [];
        return Object.keys(locations).filter(key => isOwnLocationKey(key, panoid));
    }

    // Every meta id linked "here": in the entry of this panoid or in any of the
    // "<panoid>__<scope>" entries created for it.
    function getLinkedMetaIdsForPanoid(locations, panoid) {
        const ids = new Set();
        getOwnLocationKeys(locations, panoid).forEach(key => {
            getLocationMetaIds(locations[key]).forEach(id => ids.add(id));
        });
        return ids;
    }

    // Picks the key where a meta of `scope` must be stored when no matching entry
    // exists elsewhere: reuse an entry of this panoid that has the right shape,
    // otherwise create a NEW entry ("<panoid>" if free, else "<panoid>__<scope>").
    function resolveKeyForNewLink(locations, panoid, scope) {
        const normalizedScope = normalizeScope(scope);
        const ownKey = getOwnLocationKeys(locations, panoid)
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
                    targetKey = findMatchingLocationKey(locations, scope) ||
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
                if ('road' in scopedSnapshot && !entry.road) entry.road = scopedSnapshot.road;
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

    function rebuildProximityIndexes() {
        indexedLocationEntries = [];
        forEachCombinedLocationEntry((panoid, entry) => {
            const lat = normalizeCoordinate(entry.lat);
            const lng = normalizeCoordinate(entry.lng);
            const country = normalizeCountry(entry.nominatimCountry || entry.country, lat, lng);
            indexedLocationEntries.push({
                metaIds: getLocationMetaIds(entry),
                lat,
                lng,
                country,
                region: entry.region,
                city: entry.city,
                roads: getNormalizedRoadNames(entry.road)
            });
        });
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

    function readStoredValue(key, defaultValue = null) {
        if (typeof GM_getValue === 'function') {
            return GM_getValue(key, defaultValue);
        }
        return localStorage.getItem(key) ?? defaultValue;
    }

    function writeStoredValue(key, value) {
        if (typeof GM_setValue === 'function') {
            GM_setValue(key, value);
            return;
        }
        localStorage.setItem(key, value);
    }

    function clearStoredValue(key) {
        if (typeof GM_setValue === 'function') {
            GM_setValue(key, null);
        }
        localStorage.removeItem(key);
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
            return normalizeDataSnapshot(cached);
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
        console.log(`[BetterMetas] Loaded cached DB: ${getCombinedLocationCount()} locs, ${metasData.length} metas.`);
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
    let adminSortMode = 'title';
    let activeMutationCount = 0;
    let backgroundRefreshTimer = null;

    const ALL_SCOPES = ['countrywide', 'region', 'city', 'road', '100km', '10km', '1km', 'unique'];
    const LINKED_META_SCOPE_ORDER = ['unique', '1km', '10km', 'road', 'city', '100km', 'region', 'countrywide'];
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

    function escapeHtml(value) {
        return String(value ?? '').replace(/[&<>"']/g, (char) => ({
            '&': '&amp;',
            '<': '&lt;',
            '>': '&gt;',
            '"': '&quot;',
            "'": '&#39;'
        }[char]));
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
                            html += `<${delimiter.tag}>${format(source.slice(contentStart, end))}</${delimiter.tag}>`;
                            i = end + delimiter.marker.length;
                            continue;
                        }
                    }
                }
                html += escapeHtml(source[i]);
                i += 1;
            }
            return html;
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
    const imageBlobCache = new Map(); // url -> Promise<Blob|null>
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
        if (imageBlobCache.has(url)) return imageBlobCache.get(url);

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

    // Downloads `url` and saves it to data/<countrySlug>/<name>. Returns the
    // relative path to store in the meta's imageUrl.
    async function importRemoteImage(url, countrySlug) {
        const blob = await fetchImageBlob(url);
        if (!blob) throw new Error('Could not download the image');

        const folder = slugifyForMetaId(countrySlug) || 'unknown';
        let fileName = 'image';
        try {
            fileName = decodeURIComponent(new URL(url).pathname.split('/').filter(Boolean).pop() || 'image');
        } catch (err) {
            // Keep the default name.
        }
        fileName = fileName.replace(/[<>:"/\\|?*\x00-\x1f]/g, '_').replace(/[. ]+$/, '') || 'image';
        if (!/\.(png|jpe?g|webp|gif|avif)$/i.test(fileName)) fileName += IMAGE_EXT_BY_TYPE[blob.type] || '.png';

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
            const storedScopes = JSON.parse(localStorage.getItem(ACTIVE_SCOPES_STORAGE_KEY) || 'null');
            if (Array.isArray(storedScopes)) {
                const knownScopes = storedScopes
                    .map(scope => normalizeScope(scope, null))
                    .filter(Boolean);
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
            const storedTags = JSON.parse(localStorage.getItem(ACTIVE_TAGS_STORAGE_KEY) || 'null');
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
    const STYLES = `
        #gg-meta-hud {
            --gg-meta-divider-gap: 12px;
            --gg-meta-content-status-gap: 8px;

            position: fixed;
            top: 0.5rem; /* Below the top bar */
            left: 0.5rem; /* Aligned to left */
            right: auto;
            transform: none;

            width: ${DEFAULT_HUD_WIDTH};

            /* Window Dimensions */
            height: ${DEFAULT_HUD_HEIGHT};
            max-height: 80vh;
            display: flex;
            flex-direction: column;

            background:
                radial-gradient(circle at 12% -12%, rgba(121, 80, 229, 0.12), transparent 42%),
                radial-gradient(circle at 100% 112%, rgba(0, 162, 254, 0.07), transparent 44%),
                rgba(4, 3, 14, 0.86);
            color: #fff;
            padding: 12px 16px;
            border-radius: 16px;

            z-index: 99999;
            font-family: inherit !important;
            font-weight: 700;

            border: 1px solid rgba(175, 165, 225, 0.16);
            /* display: flex controlled via opacity now */
            display: flex;
            flex-direction: column;

            /* Initial State: Hidden */
            opacity: 0;
            pointer-events: none;
            transform: translateY(10px); /* Slide up effect */
            transition: opacity 0.3s cubic-bezier(0.2, 0, 0, 1), transform 0.3s cubic-bezier(0.2, 0, 0, 1);

            box-shadow: inset 0 1px 0 rgba(255,255,255,0.05), 0 8px 24px rgba(0,0,0,0.2);
            text-shadow: 0 1px 4px rgba(0,0,0,0.9);

            /* Custom Scrollbar for sleek look */
            scrollbar-width: thin;
            scrollbar-color: rgba(255,255,255,0.3) transparent;
        }

        #gg-meta-hud.gg-visible {
            opacity: 1;
            pointer-events: auto;
            transform: translateY(0);
        }

        .gg-normal-controls {
            display: flex;
            align-items: center;
        }

        .gg-resize-grip {
            position: absolute;
            right: 4px;
            bottom: 4px;
            z-index: 6;
            width: 18px;
            height: 18px;
            display: flex;
            align-items: flex-end;
            justify-content: flex-end;
            padding: 4px;
            box-sizing: content-box;
            color: rgba(255, 255, 255, 0.45);
            cursor: nwse-resize;
            touch-action: none;
            transition: color 0.15s;
        }

        .gg-resize-grip:hover {
            color: rgba(255, 255, 255, 0.85);
        }

        .gg-resize-grip svg {
            display: block;
            pointer-events: none;
        }

        #gg-meta-add-btn,
        #gg-meta-admin-btn,
        #gg-settings-btn {
            background: rgba(255, 255, 255, 0.2);
            color: #fff;
            border: 1px solid rgba(255, 255, 255, 0.1);
            border-radius: 20px;
            cursor: pointer;
            font-size: 0.75rem;
            font-weight: 600;
            line-height: 1;
            padding: calc(4px - var(--gg-text-optical-shift)) 12px calc(4px + var(--gg-text-optical-shift));
            display: flex;
            align-items: center;
            justify-content: center;
            transition: background 0.2s, color 0.2s, border-color 0.2s;
        }

        #gg-meta-admin-btn,
        #gg-settings-btn {
            padding: 4px 8px;
        }

        #gg-meta-admin-btn svg,
        #gg-settings-btn svg,
        .gg-modal-back-btn svg {
            display: block;
            flex-shrink: 0;
        }

        #gg-meta-add-btn:hover,
        #gg-meta-admin-btn:hover,
        #gg-settings-btn:hover {
            background: rgba(255, 255, 255, 0.4);
            color: #fff;
        }

        /* Main HUD controls stay visually quiet so the metas remain dominant. */
        #gg-meta-admin-btn:hover,
        #gg-meta-add-btn:hover,
        #gg-settings-btn:hover {
            background: rgba(255, 255, 255, 0.3);
            border-color: rgba(255, 255, 255, 0.22);
        }

        #gg-meta-admin-btn:focus-visible,
        #gg-meta-add-btn:focus-visible,
        #gg-settings-btn:focus-visible {
            outline: none;
        }

        #gg-meta-admin-btn:focus-visible,
        #gg-meta-add-btn:focus-visible,
        #gg-settings-btn:focus-visible {
            box-shadow: 0 0 0 2px rgba(255, 255, 255, 0.24);
        }

        #gg-meta-admin-btn:active,
        #gg-meta-add-btn:active,
        #gg-settings-btn:active {
            transform: translateY(1px);
        }

        #gg-meta-hud * {
            font-family: inherit !important;
            font-weight: inherit;
        }
        /* Hover effect removed */
        .gg-meta-title {
            font-weight: 800;
            color: #fff; /* White title like compass directions */
            margin-bottom: var(--gg-meta-divider-gap);
            display: flex;
            justify-content: space-between;
            align-items: center;
            font-size: 0.95rem;
            /* text-transform: uppercase; Removed to allow BetterMetas mixed case */
            letter-spacing: 0.05em;
            border-bottom: 1px solid rgba(255,255,255,0.1);
            padding-bottom: var(--gg-meta-divider-gap);
            cursor: move;
            touch-action: none;
        }

        #gg-meta-hud.gg-dragging {
            transition: none;
        }
        .gg-meta-content {
            font-size: 0.9rem;
            min-height: 40px;
            flex: 1;
            overflow-y: auto;
            margin-bottom: var(--gg-meta-content-status-gap); /* Spacing above status */
        }
        #gg-meta-container {
            scrollbar-width: none;
            -ms-overflow-style: none;
        }
        #gg-meta-container::-webkit-scrollbar {
            display: none;
            width: 0;
            height: 0;
        }
        .gg-meta-tag, .gg-tag-pill {
            display: inline-flex;
            align-items: center;
            justify-content: center;
            background: rgba(255, 255, 255, 0.2);
            color: #fff;
            padding: 2px 8px;
            border-radius: 12px;
            font-size: 0.75rem;
            margin-right: 4px;
            margin-bottom: 4px;
            font-weight: 600;
            line-height: 1;
        }

        .gg-tag-pill {
            cursor: pointer;
            background: rgba(255, 255, 255, 0.055);
            border: 1px solid rgba(255, 255, 255, 0.12);
            color: rgba(255, 255, 255, 0.58);
            transition: background 0.2s, border-color 0.2s, color 0.2s, box-shadow 0.2s;
        }

        .gg-tag-pill:hover {
            background: rgba(255, 255, 255, 0.1);
            border-color: rgba(255, 255, 255, 0.24);
            color: rgba(255, 255, 255, 0.82);
        }

        .gg-tag-pill.gg-tag-selected {
            background: var(--gg-tag-grey-active);
            color: #fff;
            border-color: rgba(255, 255, 255, 0.48);
            box-shadow: inset 0 1px 0 rgba(255,255,255,0.08), 0 2px 4px rgba(0,0,0,0.24);
        }

        .gg-tag-pill.gg-tag-selected:hover {
            background: rgba(255, 255, 255, 0.24);
            color: #fff;
        }

        .gg-scope-pill {
            background: rgba(255, 255, 255, 0.055);
            border-color: rgba(255, 255, 255, 0.12);
            color: rgba(255, 255, 255, 0.58);
        }

        .gg-scope-pill:hover {
            background: rgba(255, 255, 255, 0.1);
            border-color: rgba(255, 255, 255, 0.24);
            color: rgba(255, 255, 255, 0.82);
        }

        .gg-scope-pill.gg-tag-selected {
            background: rgba(96, 165, 250, 0.24);
            border-color: rgba(147, 197, 253, 0.62);
            color: #e8f3ff;
            box-shadow: inset 0 1px 0 rgba(255,255,255,0.08), 0 2px 4px rgba(0,0,0,0.24);
        }

        .gg-scope-pill.gg-tag-selected:hover {
            background: rgba(96, 165, 250, 0.3);
            color: #fff;
        }

        .gg-tag-static {
            display: inline-flex;
            align-items: center;
            justify-content: center;
            background: var(--gg-tag-grey);
            color: #fff;
            padding: 1px 6px;
            border-radius: 12px;
            font-size: 0.65rem;
            margin-right: 6px;
            font-weight: 600;
            border: 1px solid rgba(255, 255, 255, 0.1);
            cursor: default;
            white-space: nowrap;
            line-height: 1;
        }

        .gg-meta-tags {
            display: flex;
            flex-wrap: wrap;
            gap: 6px;
            margin-top: 4px;
            margin-left: 1px;
        }

        .gg-meta-tags .gg-tag-static {
            margin-right: 0;
        }

        .gg-meta-row {
            margin-bottom: var(--gg-meta-divider-gap);
            padding-bottom: var(--gg-meta-divider-gap);
            border-bottom: 1px solid rgba(255,255,255,0.1);
        }

        .gg-meta-row-predicted {
            border-left: 2px solid rgba(255,255,255,0.2);
            padding-left: 10px;
            margin-left: -12px;
        }

        .gg-meta-item-title {
            display: flex;
            align-items: center;
            flex-wrap: wrap;
            column-gap: 8px;
            row-gap: 4px;
            font-size: 1.1rem;
            font-weight: 800;
            color: #fff;
            margin-bottom: 6px;
            line-height: 1.3;
        }

        .gg-clickable-meta-title {
            cursor: pointer;
        }

        .gg-empty-state {
            color: #ccc;
            font-style: italic;
        }

        .gg-muted-empty-state {
            opacity: 0.6;
            font-style: italic;
        }

        #gg-meta-hud .gg-meta-description {
            font-size: 0.75rem;
            color: rgba(255, 255, 255, 0.8);
            margin-bottom: 8px;
            line-height: 1.4;
            font-weight: 400 !important;
            font-family: inherit;
            white-space: pre-line; /* keep line breaks from the description */
        }
        #gg-meta-hud .gg-meta-description strong,
        #gg-meta-preview-popup .gg-meta-description strong {
            font-weight: 700 !important;
            color: #fff;
        }
        #gg-meta-hud .gg-meta-description em,
        #gg-meta-preview-popup .gg-meta-description em {
            font-style: italic;
        }
        .gg-meta-image {
            max-width: 100%;
            height: auto;
            max-height: 25vh;
            border-radius: 8px;
            margin-bottom: 8px;
            display: block;
        }
        .gg-meta-image[data-gg-src] {
            width: 100%;
            min-height: 1px;
        }
        #gg-meta-hud .gg-meta-image,
        #gg-existing-metas .gg-meta-image {
            cursor: zoom-in;
        }
        #gg-image-lightbox {
            position: fixed;
            inset: 0;
            z-index: 100010;
            background: rgba(0, 0, 0, 0.85);
            overflow: hidden;
            cursor: grab;
            user-select: none;
        }
        #gg-image-lightbox.gg-dragging { cursor: grabbing; }
        #gg-image-lightbox img {
            position: absolute;
            top: 50%;
            left: 50%;
            max-width: 92vw;
            max-height: 92vh;
            margin: 0;
            border-radius: 4px;
            transform-origin: center center;
            -webkit-user-drag: none;
        }
        #gg-image-lightbox .gg-lightbox-hint {
            position: absolute;
            bottom: 12px;
            left: 50%;
            transform: translateX(-50%);
            color: #ccc;
            font-size: 12px;
            pointer-events: none;
        }
        .gg-meta-row:last-child {
            border-bottom: none;
            margin-bottom: 0;
            padding-bottom: 0;
        }

        /* Location Info Box */
        #gg-location-info {
            background: rgba(255, 255, 255, 0.1);
            border-radius: 8px;
            padding: 8px;
            margin-bottom: 12px;
            font-size: 0.8rem;
            border: 1px solid rgba(255,255,255,0.1);
        }
        .gg-loc-row {
            display: flex;
            align-items: flex-start;
            margin-bottom: 4px;
        }
        .gg-loc-row:last-child { margin-bottom: 0; }
        .gg-loc-label {
            color: rgba(255,255,255,0.5);
            width: 70px;
            flex-shrink: 0;
            font-weight: 600;
        }
        .gg-loc-val {
            color: #fff;
            font-weight: 500;
            word-break: break-word;
        }
        .gg-loc-val-country {
            color: var(--gg-primary-green);
        }
        .gg-loc-coords {
            font-family: monospace;
            color: #ffd700;
        }

        #gg-settings-btn,
        #gg-meta-admin-btn {
            margin-right: 8px;
        }
        .gg-status-msg {
            font-size: 0.75em;
            color: rgba(255, 255, 255, 0.5);
            margin-top: var(--gg-meta-content-status-gap);
            font-style: normal;
            text-align: right;
            cursor: pointer;
        }

        /* Modal Spacing System */
        :root {
            --modal-spacing-xs: 4px;
            --modal-spacing-sm: 8px;
            --modal-spacing-md: 12px;
            --modal-spacing-lg: 24px;
            --modal-related-gap: var(--modal-spacing-sm);
            --modal-section-gap: var(--modal-spacing-md);
            --gg-text-optical-shift: 0.25px;
            --modal-radius: 16px;
            --modal-window-width: 550px;
            --modal-btn-radius: 30px;
            --modal-btn-height: 42px;
            --modal-btn-font-size: 0.8rem;
            --modal-control-bg: rgba(0, 0, 0, 0.3);
            --modal-control-bg-active: rgba(0, 0, 0, 0.4);
            --modal-control-border: rgba(100, 90, 150, 0.4);
            --modal-control-radius: 8px;
            --gg-primary-green: #97e851;
            --gg-primary-border: #479440;
            --gg-primary-gradient: linear-gradient(#97e851, #479440);
            --gg-edit-yellow: #f4c542;
            --gg-edit-yellow-dark: #a97912;
            --gg-edit-gradient: linear-gradient(180deg, #f4c542 0%, #d9a91f 100%);
            --gg-danger-red: #ef4444;
            --gg-danger-red-soft: rgba(239, 68, 68, 0.14);
            --gg-tag-grey: rgba(255, 255, 255, 0.18);
            --gg-tag-grey-active: rgba(255, 255, 255, 0.19);
            --gg-scope-blue: #60a5fa;
            --gg-scope-blue-soft: rgba(96, 165, 250, 0.14);
            --gg-context-neutral: #a89de0;
            --gg-context-normal: #97e851;
            --gg-context-edit: #f4c542;
            --gg-context-pat: #38bdf8;
            --gg-context-danger: #ef4444;
            --gg-primary-shadow: 0 0.275rem 1.125rem rgba(0, 0, 0, 0.25),
                inset 0 0.0625rem 0 rgba(255, 255, 255, 0.2),
                inset 0 -0.125rem 0 rgba(0, 0, 0, 0.3);
        }

        /* Modal Base Styles - GeoGuessr Native Style */
        #gg-meta-modal,
        #gg-settings-modal .gg-modal-container,
        #gg-meta-admin-modal,
        #gg-dialog-modal {
            position: fixed;
            top: 50%;
            left: 50%;
            transform: translate(-50%, -50%);
            --gg-context-rgb: 168, 157, 224;
            --gg-context-accent: var(--gg-context-neutral);
            background:
                radial-gradient(circle at 12% -8%, rgba(var(--gg-context-rgb), 0.18), transparent 36%),
                radial-gradient(circle at 96% 108%, rgba(var(--gg-context-rgb), 0.08), transparent 42%),
                linear-gradient(180deg, rgba(37, 32, 96, 0.98) 0%, rgba(22, 20, 57, 0.99) 100%);
            border: 1px solid rgba(var(--gg-context-rgb), 0.38);
            border-radius: var(--modal-radius);
            color: white;
            font-family: inherit;
            font-weight: 700;
            max-height: 85vh;
            overflow-y: auto;
            scrollbar-width: thin;
            scrollbar-color: rgba(255,255,255,0.3) transparent;
            box-shadow:
                inset 0 1px 0 rgba(255,255,255,0.06),
                inset 0 0 34px rgba(var(--gg-context-rgb), 0.06),
                0 10px 34px rgba(0, 0, 0, 0.52);
            text-align: center;
            padding: var(--modal-spacing-lg);
            transition: border-color 0.25s, box-shadow 0.25s, background 0.25s;
        }

        .gg-context-normal {
            --gg-context-rgb: 151, 232, 81;
            --gg-context-accent: var(--gg-context-normal);
        }

        .gg-context-edit {
            --gg-context-rgb: 244, 197, 66;
            --gg-context-accent: var(--gg-context-edit);
        }

        .gg-context-pat {
            --gg-context-rgb: 56, 189, 248;
            --gg-context-accent: var(--gg-context-pat);
        }

        .gg-context-danger {
            --gg-context-rgb: 239, 68, 68;
            --gg-context-accent: var(--gg-context-danger);
        }

        .gg-context-neutral {
            --gg-context-rgb: 168, 157, 224;
            --gg-context-accent: var(--gg-context-neutral);
        }

        #gg-meta-modal {
            z-index: 100000;
            width: min(var(--modal-window-width), calc(100vw - 32px));
            box-sizing: border-box;
            transition: all 0.3s ease-in-out;
        }

        #gg-meta-admin-modal {
            z-index: 100000;
            width: min(var(--modal-window-width), calc(100vw - 32px));
            box-sizing: border-box;
            text-align: left;
        }

        #gg-meta-admin-modal .gg-modal-header,
        #gg-meta-admin-modal .gg-form-label,
        #gg-meta-admin-modal .gg-form-hint {
            text-align: center;
        }

        #gg-dialog-modal {
            z-index: 100003;
            width: 360px;
            display: none;
            box-sizing: border-box;
        }

        .gg-dialog-message {
            color: rgba(255, 255, 255, 0.82);
            font-size: 0.86rem;
            font-weight: 500;
            line-height: 1.45;
            margin-bottom: var(--modal-section-gap);
            white-space: pre-wrap;
        }

        .gg-dialog-actions {
            display: flex;
            flex-wrap: wrap;
            gap: var(--modal-related-gap);
            margin-top: var(--modal-section-gap);
        }

        .gg-dialog-actions .gg-btn-primary,
        .gg-dialog-actions .gg-btn-secondary,
        .gg-dialog-actions .gg-btn-danger {
            margin-top: 0;
            flex: 1;
        }

        .gg-dialog-actions .gg-btn-primary:only-child,
        .gg-dialog-actions .gg-btn-secondary:only-child {
            flex: 0 0 100%;
        }

        .gg-dialog-actions #gg-dialog-edit {
            flex: 0 0 100%;
            min-width: 0;
        }

        .gg-dialog-actions.gg-meta-action-buttons {
            flex-direction: column;
        }

        .gg-dialog-actions.gg-meta-action-buttons .gg-btn-primary,
        .gg-dialog-actions.gg-meta-action-buttons .gg-btn-secondary,
        .gg-dialog-actions.gg-meta-action-buttons .gg-btn-danger {
            flex: 0 0 var(--modal-btn-height);
            width: 100%;
            height: var(--modal-btn-height);
            min-height: var(--modal-btn-height);
            max-height: var(--modal-btn-height);
        }

        .gg-dialog-actions.gg-meta-action-buttons #gg-dialog-edit {
            flex-basis: var(--modal-btn-height);
        }

        .gg-dialog-actions .gg-meta-action-divider {
            flex: 0 0 1px;
            width: 100%;
            margin: 2px 0;
            background: linear-gradient(
                90deg,
                transparent 0%,
                rgba(255, 255, 255, 0.08) 18%,
                rgba(255, 255, 255, 0.22) 50%,
                rgba(255, 255, 255, 0.08) 82%,
                transparent 100%
            );
        }

        #gg-dialog-edit .gg-dialog-edit-label {
            display: block;
            max-width: 100%;
            min-width: 0;
            overflow: hidden;
            text-overflow: ellipsis;
            white-space: nowrap;
        }

        .gg-modal-subview {
            transition: opacity 0.3s ease-in-out, transform 0.3s ease-in-out;
            opacity: 1;
            transform: translateX(0);
        }

        .gg-modal-subview.gg-hidden {
            display: none;
            opacity: 0;
            transform: translateX(20px);
        }

        #gg-settings-modal .gg-modal-container {
            z-index: 100001;
            width: min(var(--modal-window-width), calc(100vw - 32px));
            box-sizing: border-box;
        }

        /* Modal Header */
        .gg-modal-header {
            font-size: 1.1rem;
            font-weight: 800;
            color: #fff;
            margin-bottom: var(--modal-spacing-lg);
            text-align: center;
            letter-spacing: 0.02em;
        }

        .gg-context-surface .gg-modal-header::after {
            content: '';
            display: block;
            width: 36px;
            height: 2px;
            margin: 10px auto 0;
            border-radius: 999px;
            background: var(--gg-context-accent);
            box-shadow: 0 0 12px rgba(var(--gg-context-rgb), 0.5);
            opacity: 0.78;
        }

        .gg-modal-section-title {
            font-size: 0.8rem;
            font-weight: 700;
            color: rgba(255, 255, 255, 0.58);
            text-transform: uppercase;
            letter-spacing: 0.06em;
            margin: var(--modal-spacing-lg) 0 var(--modal-section-gap) 0;
            text-align: center;
        }

        /* Form Elements */
        .gg-form-group {
            margin-bottom: var(--modal-section-gap);
        }

        .gg-form-group-lg {
            margin-bottom: var(--modal-section-gap);
        }

        .gg-form-label {
            display: block;
            margin-bottom: var(--modal-related-gap);
            font-size: 0.75rem;
            color: rgba(255, 255, 255, 0.5);
            font-weight: 600;
            text-align: center;
        }

        .gg-form-input {
            width: 100%;
            padding: var(--modal-related-gap) var(--modal-section-gap);
            background: var(--modal-control-bg);
            border: 1px solid var(--modal-control-border);
            color: white;
            border-radius: var(--modal-control-radius);
            box-sizing: border-box;
            font-family: inherit;
            font-size: 0.95rem;
            font-weight: 400;
            text-align: center;
            transition: border-color 0.2s, background 0.2s;
        }

        .gg-form-input::placeholder {
            color: rgba(255, 255, 255, 0.4);
        }

        .gg-form-input:focus {
            outline: none;
            background: var(--modal-control-bg-active);
            border-color: rgba(var(--gg-context-rgb), 0.68);
            box-shadow: 0 0 0 2px rgba(var(--gg-context-rgb), 0.1);
        }

        textarea.gg-form-input {
            resize: vertical;
            min-height: 42px;
            text-align: center; /* Center horizontally like other inputs */
            /* Vertical centering handled by padding inherited from .gg-form-input */
        }

        #meta-desc,
        #gg-admin-meta-desc {
            text-align: left;
        }

        .gg-form-hint {
            font-size: 0.7rem;
            color: rgba(255, 255, 255, 0.4);
            margin-top: var(--modal-related-gap);
            font-weight: 400;
            text-align: center;
        }

        .gg-hidden-control {
            display: none;
        }

        .gg-pill-grid {
            display: flex;
            flex-wrap: wrap;
            justify-content: center;
            gap: 4px;
            margin-top: var(--modal-related-gap);
            text-align: center;
        }

        .gg-pill-grid .gg-tag-pill {
            margin: 0;
        }

        /* Buttons - GeoGuessr Green Style */
        .gg-btn-primary {
            --gg-button-hover-scale: 1.02;
            --gg-button-active-scale: 0.99;
            background: var(--gg-primary-gradient);
            color: #fff;
            border: none;
            padding: var(--modal-related-gap) 0;
            padding-bottom: calc(var(--modal-related-gap) + 0.125rem);
            border-radius: var(--modal-btn-radius);
            cursor: pointer;
            width: 100%;
            font-weight: 800;
            font-size: var(--modal-btn-font-size);
            font-style: italic;
            line-height: 1;
            text-transform: uppercase;
            letter-spacing: 0.03em;
            margin-top: var(--modal-section-gap);
            transition: transform 0.15s, background 0.15s;
            box-shadow: var(--gg-primary-shadow);
            text-shadow: 0 0.0625rem 0.125rem #171235;
            will-change: transform;
            box-sizing: border-box;
            height: var(--modal-btn-height); /* Fixed height for consistency */
            display: flex;
            align-items: center;
            justify-content: center;
            user-select: none;
            -webkit-user-select: none;
            -webkit-tap-highlight-color: transparent;
            appearance: none;
            -webkit-appearance: none;
        }

        .gg-btn-primary:focus,
        .gg-btn-secondary:focus,
        .gg-btn-danger:focus {
            outline: none;
        }

        .gg-btn-primary:focus-visible {
            outline: none;
            box-shadow: 0 0 0 2px rgba(140, 212, 90, 0.35), 0 4px 12px rgba(0, 0, 0, 0.25);
        }

        .gg-btn-primary:hover {
            transform: scale(var(--gg-button-hover-scale));
        }

        .gg-btn-primary:active {
            transform: scale(var(--gg-button-active-scale));
        }

        /* Editing and management actions */
        .gg-btn-primary.gg-btn-edit {
            background: var(--gg-edit-gradient);
            border-color: var(--gg-edit-yellow-dark);
            color: #fff;
        }

        .gg-btn-primary.gg-btn-edit:focus-visible {
            box-shadow: 0 0 0 2px rgba(244, 197, 66, 0.35), 0 4px 12px rgba(0, 0, 0, 0.25);
        }

        .gg-btn-primary.gg-btn-edit:hover {
            background: linear-gradient(180deg, #ffd766 0%, #e8b733 100%);
            color: #fff;
        }

        .gg-btn-primary:disabled,
        .gg-btn-secondary:disabled,
        .gg-btn-danger:disabled,
        .gg-btn-link-meta:disabled,
        #gg-meta-add-btn:disabled,
        #gg-meta-admin-btn:disabled,
        #gg-settings-btn:disabled {
            opacity: 0.58;
            cursor: wait;
            transform: none;
            pointer-events: none;
        }

        .gg-operation-busy .gg-tag-pill,
        .gg-operation-busy .gg-admin-location-item,
        .gg-operation-busy .gg-meta-list-item {
            pointer-events: none;
        }

        .gg-btn-secondary {
            background: var(--modal-control-bg);
            color: rgba(255, 255, 255, 0.7);
            border: 1px solid var(--modal-control-border);
            padding: var(--modal-related-gap) 0;
            cursor: pointer;
            margin-top: var(--modal-section-gap);
            width: 100%;
            font-size: var(--modal-btn-font-size);
            font-weight: 700;
            line-height: 1;
            border-radius: var(--modal-btn-radius); /* Match primary button */
            transition: background 0.2s, color 0.2s;
            box-sizing: border-box;
            height: var(--modal-btn-height); /* Fixed height for consistency */
            display: flex;
            align-items: center;
            justify-content: center;
            text-transform: uppercase; /* Match layout style */
            letter-spacing: 0.03em;
            user-select: none;
            -webkit-user-select: none;
            -webkit-tap-highlight-color: transparent;
            appearance: none;
            -webkit-appearance: none;
        }

        .gg-btn-secondary:focus-visible {
            outline: none;
            box-shadow: 0 0 0 2px rgba(150, 140, 200, 0.35);
        }

        .gg-btn-secondary:hover {
            background: var(--modal-control-bg-active);
            color: #fff;
        }

        .gg-btn-danger {
            background: transparent;
            color: var(--gg-danger-red);
            border: none;
            padding: var(--modal-related-gap) 0;
            border-radius: var(--modal-btn-radius); /* Match primary button */
            cursor: pointer;
            width: 100%;
            font-size: var(--modal-btn-font-size);
            font-weight: 700;
            line-height: 1;
            text-transform: uppercase;
            letter-spacing: 0.04em;
            transition: background 0.2s, color 0.2s;
            box-sizing: border-box;
            box-shadow: inset 0 0 0 2px var(--gg-danger-red);
            height: var(--modal-btn-height); /* Fixed height for consistency */
            display: flex;
            align-items: center;
            justify-content: center;
            user-select: none;
            -webkit-user-select: none;
            -webkit-tap-highlight-color: transparent;
            appearance: none;
            -webkit-appearance: none;
        }

        .gg-btn-danger:focus-visible {
            outline: none;
            box-shadow: inset 0 0 0 2px var(--gg-danger-red), inset 0 0 0 4px rgba(239, 68, 68, 0.3);
        }

        .gg-btn-danger:hover {
            background: var(--gg-danger-red-soft);
            box-shadow: inset 0 0 0 2px var(--gg-danger-red);
        }

        #gg-save-settings {
            margin-top: 0;
        }

        #meta-details-btn {
            margin-top: 0;
        }

        /* Divider */
        .gg-modal-divider {
            border: 0;
            height: 1px;
            background: linear-gradient(
                90deg,
                transparent 0%,
                rgba(255, 255, 255, 0.06) 18%,
                rgba(var(--gg-context-rgb), 0.28) 50%,
                rgba(255, 255, 255, 0.06) 82%,
                transparent 100%
            );
            margin: var(--modal-section-gap) 0;
        }

        .gg-modal-divider + .gg-btn-primary,
        .gg-modal-divider + .gg-btn-secondary,
        .gg-modal-divider + .gg-btn-danger,
        .gg-modal-divider + .gg-selection-actions,
        .gg-modal-divider + .gg-admin-actions {
            margin-top: 0;
        }

        /* Existing Metas List */
        #gg-existing-metas {
            height: 150px;
            overflow-y: auto;
            scrollbar-width: thin;
            scrollbar-color: rgba(255,255,255,0.2) transparent;
            width: 100%;
            background: var(--modal-control-bg);
            border: 1px solid var(--modal-control-border);
            border-radius: var(--modal-control-radius);
            box-sizing: border-box;
            margin-top: var(--modal-related-gap);
        }

        .gg-meta-list-item {
            display: flex;
            justify-content: space-between;
            align-items: center;
            padding: var(--modal-related-gap) var(--modal-section-gap);
            border-bottom: 1px solid rgba(255,255,255,0.06);
        }

        .gg-list-load-more {
            width: 100%;
            min-height: 36px;
            border: 0;
            border-top: 1px solid rgba(255,255,255,0.06);
            background: transparent;
            color: rgba(255,255,255,0.58);
            cursor: pointer;
            font: inherit;
            font-size: 11px;
            overflow-anchor: none;
        }

        .gg-list-load-more:hover,
        .gg-list-load-more:focus-visible {
            color: #fff;
            background: rgba(255,255,255,0.05);
            outline: none;
        }

        .gg-meta-list-main {
            display: flex;
            align-items: baseline;
            gap: 4px;
            flex: 1;
            overflow: hidden;
            min-height: 100%;
        }

        .gg-meta-list-item:last-child {
            border-bottom: none;
        }

        .gg-list-empty-state {
            padding: var(--modal-related-gap) 0;
        }

        .gg-meta-list-title {
            font-size: 0.8rem;
            font-weight: 600;
            color: #fff;
            white-space: nowrap;
            line-height: 1;
            overflow: hidden;
            text-overflow: ellipsis;
            padding: 0 4px;
            flex-shrink: 0;
        }

        .gg-meta-list-tags {
            display: flex;
            align-items: baseline;
            gap: 4px;
            overflow-x: auto;
            scrollbar-width: none;
            height: 100%;
            flex: 1;
            font-size: 0.65rem;
            color: rgba(255,255,255,0.4);
            margin-top: 2px;
        }

        .gg-meta-list-tags .gg-tag-static {
            margin-right: 0;
        }

        .gg-meta-list-tags .gg-scope-static {
            margin-right: 4px;
        }

        .gg-scope-static {
            background: rgba(96, 165, 250, 0.24);
            border-color: rgba(147, 197, 253, 0.62);
            color: #e8f3ff;
            box-shadow: inset 0 1px 0 rgba(255,255,255,0.08), 0 2px 4px rgba(0,0,0,0.24);
        }

        .gg-modal-header-with-back {
            position: relative;
            display: block;
        }

        .gg-modal-back-btn {
            background: none;
            border: none;
            color: rgba(255,255,255,0.5);
            cursor: pointer;
            position: absolute;
            left: 0;
            top: 0;
            transform: none;
            display: flex;
            align-items: center;
            padding: 0;
        }

        .gg-admin-meta-list {
            height: 260px;
            overflow-y: auto;
            scrollbar-width: thin;
            scrollbar-color: rgba(255,255,255,0.2) transparent;
            width: 100%;
            background: var(--modal-control-bg);
            border: 1px solid var(--modal-control-border);
            border-radius: var(--modal-control-radius);
            box-sizing: border-box;
            margin-top: var(--modal-related-gap);
        }

        .gg-admin-meta-item {
            cursor: default;
            gap: var(--modal-related-gap);
            transition: background 0.2s;
        }

        .gg-admin-meta-item .gg-meta-list-main {
            min-width: 0;
            padding-right: var(--modal-related-gap);
        }

        .gg-admin-meta-item .gg-meta-list-title {
            flex: 0 1 auto;
            min-width: 0;
        }

        .gg-admin-meta-item .gg-meta-list-tags {
            flex: 0 1 auto;
            min-width: 0;
            max-width: none;
            overflow: hidden;
        }

        .gg-admin-controls {
            margin-bottom: 8px;
        }

        .gg-admin-sort-control {
            display: flex;
            align-items: center;
            justify-content: center;
            gap: 2px;
            margin-top: 6px;
        }

        .gg-admin-sort-control .gg-form-label {
            margin: 0;
            color: rgba(255, 255, 255, 0.45);
            font-size: 0.72rem;
            letter-spacing: 0.02em;
            white-space: nowrap;
        }

        .gg-admin-sort-select-wrap {
            position: relative;
            display: inline-flex;
            align-items: center;
        }

        .gg-admin-sort-select-wrap::after {
            content: '';
            position: absolute;
            right: 10px;
            top: calc(50% - 4px);
            width: 6px;
            height: 6px;
            border-right: 1.5px solid rgba(255, 255, 255, 0.65);
            border-bottom: 1.5px solid rgba(255, 255, 255, 0.65);
            pointer-events: none;
            transform: rotate(45deg);
            transition: border-color 0.2s;
        }

        .gg-admin-sort-select {
            width: auto;
            padding: 3px 22px 3px 4px;
            background: transparent;
            border: 0;
            border-radius: var(--modal-control-radius);
            cursor: pointer;
            color: rgba(255, 255, 255, 0.9);
            font-size: 0.8rem;
            text-align: left;
            appearance: none;
            -webkit-appearance: none;
        }

        .gg-admin-sort-select:focus,
        .gg-admin-sort-select:focus-visible {
            outline: none;
            background: transparent;
            border: 0;
            box-shadow: none;
        }

        .gg-admin-sort-select-wrap:focus-within::after {
            border-color: rgba(200, 190, 255, 0.95);
        }

        .gg-admin-details-grid {
            display: block;
        }

        .gg-admin-details-grid .gg-form-group {
            margin-bottom: var(--modal-section-gap);
        }

        #gg-settings-modal .gg-settings-danger-group {
            --gg-context-rgb: 239, 68, 68;
            --gg-context-accent: var(--gg-context-danger);
        }

        #meta-details-view > .gg-form-group:not(:last-of-type),
        .gg-admin-details-grid > .gg-form-group:not(:last-child) {
            position: relative;
            padding-bottom: var(--modal-section-gap);
        }

        #meta-details-view > .gg-form-group:not(:last-of-type)::after,
        .gg-admin-details-grid > .gg-form-group:not(:last-child)::after {
            content: '';
            position: absolute;
            right: 0;
            bottom: 0;
            left: 0;
            height: 1px;
            background: linear-gradient(
                90deg,
                transparent 0%,
                rgba(255, 255, 255, 0.06) 18%,
                rgba(var(--gg-context-rgb), 0.24) 50%,
                rgba(255, 255, 255, 0.06) 82%,
                transparent 100%
            );
        }

        .gg-admin-actions {
            display: flex;
            flex-direction: column;
            gap: var(--modal-related-gap);
            margin-top: var(--modal-section-gap);
        }

        .gg-admin-actions .gg-btn-primary,
        .gg-admin-actions .gg-btn-secondary,
        .gg-admin-actions .gg-btn-danger {
            margin-top: 0;
        }

        .gg-admin-linked-locations {
            width: 100%;
            box-sizing: border-box;
        }

        .gg-admin-location-item {
            width: 100%;
            display: flex;
            align-items: center;
            gap: var(--modal-related-gap);
        }

        .gg-admin-location-open {
            flex: 1;
            min-width: 0;
            display: flex;
            align-items: center;
            gap: var(--modal-related-gap);
            border: none;
            background: transparent;
            color: rgba(255,255,255,0.88);
            cursor: pointer;
            font: inherit;
            font-size: 0.75rem;
            font-weight: 600;
            line-height: 1.25;
            text-align: left;
            padding: var(--modal-related-gap) var(--modal-section-gap);
            border-radius: var(--modal-control-radius);
            transition: background 0.15s;
        }

        .gg-admin-location-open:hover,
        .gg-admin-location-open:focus-visible {
            background: rgba(255,255,255,0.05);
            outline: none;
        }

        .gg-admin-location-pin,
        .gg-admin-location-external {
            width: 14px;
            height: 14px;
            flex: 0 0 14px;
            opacity: 0.42;
            transition: opacity 0.15s;
        }

        .gg-admin-location-label {
            flex: 1;
            min-width: 0;
        }

        .gg-admin-location-external {
            opacity: 0.28;
        }

        .gg-admin-location-open:hover .gg-admin-location-pin,
        .gg-admin-location-open:hover .gg-admin-location-external,
        .gg-admin-location-open:focus-visible .gg-admin-location-pin,
        .gg-admin-location-open:focus-visible .gg-admin-location-external {
            opacity: 0.85;
        }

        .gg-admin-location-remove {
            flex: 0 0 auto;
            width: 22px;
            height: 22px;
            display: flex;
            align-items: center;
            justify-content: center;
            border: 1px solid var(--gg-danger-red);
            background: transparent;
            color: var(--gg-danger-red);
            border-radius: var(--modal-control-radius);
            cursor: pointer;
            padding: 0;
            transition: background 0.15s, color 0.15s;
        }

        .gg-admin-location-remove:hover,
        .gg-admin-location-remove:focus-visible {
            background: var(--gg-danger-red-soft);
            outline: none;
        }

        .gg-admin-location-remove svg {
            width: 12px;
            height: 12px;
        }

        .gg-selection-actions {
            display: flex;
            flex-direction: column;
            gap: var(--modal-related-gap);
            margin-top: 0;
        }

        #gg-link-selected-btn {
            width: 100%;
            margin-top: 0;
            margin-bottom: 0;
        }

        #gg-link-selected-btn:disabled {
            cursor: not-allowed;
            pointer-events: auto;
            box-shadow: none;
        }

        .gg-btn-link-meta {
            --gg-button-hover-scale: 1.05;
            --gg-button-active-scale: 0.975;
            display: inline-flex;
            align-items: center;
            justify-content: center;
            background: var(--gg-primary-gradient);
            color: #fff;
            border: none;
            padding: 4px 10px calc(4px + 0.125rem);
            border-radius: 12px;
            cursor: pointer;
            font-size: 0.7rem;
            font-weight: 800;
            font-style: italic;
            line-height: 1;
            text-transform: uppercase;
            letter-spacing: 0.03em;
            transition: transform 0.15s, background 0.15s;
            box-shadow: var(--gg-primary-shadow);
            text-shadow: 0 0.0625rem 0.125rem #171235;
            will-change: transform;
            flex-shrink: 0;
            user-select: none;
            -webkit-user-select: none;
        }

        .gg-btn-link-meta:focus {
            outline: none;
        }

        .gg-btn-link-meta:focus-visible {
            outline: none;
            box-shadow: 0 0 0 2px rgba(140, 212, 90, 0.35), 0 2px 6px rgba(0, 0, 0, 0.25);
        }

        .gg-btn-link-meta:hover {
            transform: scale(var(--gg-button-hover-scale));
        }

        .gg-btn-link-meta:active {
            transform: scale(var(--gg-button-active-scale));
        }

        .gg-btn-link-meta.gg-tag-selected {
            background: var(--gg-primary-green);
            border-color: var(--gg-primary-border);
        }

        .gg-btn-link-meta.gg-btn-admin-edit {
            background: var(--gg-edit-gradient);
            border-color: var(--gg-edit-yellow-dark);
            color: #fff;
        }

        .gg-btn-link-meta.gg-btn-admin-edit:focus-visible {
            box-shadow: 0 0 0 2px rgba(244, 197, 66, 0.35), 0 2px 6px rgba(0, 0, 0, 0.25);
        }

        .gg-btn-link-meta.gg-btn-admin-edit:hover {
            background: linear-gradient(180deg, #ffd766 0%, #e8b733 100%);
        }

        .gg-meta-link-toggle {
            display: inline-flex;
            align-items: center;
            justify-content: center;
            flex-shrink: 0;
            width: 28px;
            height: 28px;
            cursor: pointer;
        }

        .gg-meta-link-checkbox {
            width: 18px;
            height: 18px;
            margin: 0;
            accent-color: var(--gg-primary-green);
            cursor: pointer;
        }

        .gg-meta-linked-indicator {
            display: inline-flex;
            align-items: center;
            justify-content: center;
            min-width: 58px;
            padding: 4px 10px;
            border: 1px solid rgba(140, 212, 90, 0.5);
            border-radius: 12px;
            background: rgba(140, 212, 90, 0.16);
            color: #bdf29a;
            font-size: 0.7rem;
            font-weight: 800;
            font-style: italic;
            line-height: 1;
            text-transform: uppercase;
            letter-spacing: 0.03em;
            flex-shrink: 0;
            user-select: none;
            -webkit-user-select: none;
        }

        /* JSON Output */
        #gg-json-output {
            margin-top: var(--modal-section-gap);
            background: var(--modal-control-bg-active);
            padding: var(--modal-related-gap);
            border-radius: var(--modal-control-radius);
            font-family: monospace;
            font-size: 0.7rem;
            color: #6f6;
            white-space: pre-wrap;
            display: none;
            word-break: break-all;
        }

        /* Spinner */
        .gg-spinner {
            display: inline-block;
            width: 12px;
            height: 12px;
            border: 2px solid rgba(255,255,255,0.3);
            border-radius: 50%;
            border-top-color: #fff;
            animation: gg-spin 1s ease-in-out infinite;
            margin-right: 8px;
            flex-shrink: 0;
        }

        @keyframes gg-spin {
            to { transform: rotate(360deg); }
        }

        /* Hide reaction wheel when HUD is active */
        body.gg-hud-active button.styles_hudButton__kzfFK.styles_sizeSmall__O7Bw_.styles_roundBoth__hcuEN {
            display: none !important;
        }

        /* Backdrop */
        #gg-modal-backdrop {
            position: fixed;
            top: 0;
            left: 0;
            width: 100%;
            height: 100%;
            background: rgba(0, 0, 0, 0.4);
            backdrop-filter: blur(8px);
            -webkit-backdrop-filter: blur(8px);
            z-index: 99999;
            display: none;
            opacity: 0;
            transition: opacity 0.3s;
        }

        #gg-modal-backdrop.gg-visible {
            display: block;
            opacity: 1;
        }

        .gg-modal-background-blurred {
            filter: blur(4px);
            pointer-events: none;
        }

        /* Preview Popup */
        #gg-meta-preview-popup {
            position: fixed;
            width: 280px;
            background: rgba(0, 0, 0, 0.95);
            border: 1px solid rgba(255, 255, 255, 0.2);
            border-radius: 12px;
            padding: 12px;
            z-index: 100002; /* Above modal */
            pointer-events: none; /* Don't interfere with mouse */
            opacity: 0;
            transform: translateX(-10px);
            transition: opacity 0.2s, transform 0.2s;
            box-shadow: 0 4px 16px rgba(0,0,0,0.5);
            display: flex;
            flex-direction: column;
            color: #fff; /* Ensure text is white */
        }

        #gg-meta-preview-popup.gg-visible {
            opacity: 1;
            transform: translateX(0);
        }

        #gg-meta-preview-popup.gg-image-url-preview {
            padding: 6px;
        }

        #gg-meta-preview-popup .gg-meta-image {
            width: 100%;
            height: 140px; /* Fixed height */
            object-fit: cover;
            border-radius: 6px;
            margin-bottom: 8px;
            background: rgba(255,255,255,0.1); /* Placeholder bg */
        }

        #gg-meta-preview-popup.gg-image-url-preview .gg-meta-image {
            height: auto;
            max-height: min(420px, calc(100vh - 48px));
            object-fit: contain;
            margin-bottom: 0;
        }

        #gg-meta-preview-popup .gg-meta-item-title {
            font-size: 0.95rem;
            margin-bottom: 4px;
            font-weight: 800;
            color: #fff;
        }

        #gg-meta-preview-popup .gg-meta-description {
            font-size: 0.75rem;
            color: rgba(255, 255, 255, 0.9); /* Explicit color */
            margin-bottom: 6px;
            line-height: 1.4;
            max-height: 80px;
            overflow: hidden;
            display: -webkit-box;
            -webkit-line-clamp: 4;
            -webkit-box-orient: vertical;
            white-space: pre-line; /* keep line breaks from the description */
        }

        #gg-meta-preview-popup .gg-meta-description:last-child {
            margin-bottom: 0;
        }

        #gg-meta-preview-popup .gg-meta-tags {
            gap: 4px;
            margin-left: 0;
        }

        #gg-meta-preview-popup .gg-meta-tags .gg-tag-static {
            font-size: 0.6rem;
            padding: 1px 4px;
            margin: 0;
        }

        /* Triangle Pointer (Right side) - Rotated Square Method */
        #gg-meta-preview-popup::after {
            content: "";
            position: absolute;
            top: 50%;
            right: -7px; /* Half of width protrudes */
            margin-top: -6px;
            width: 12px;
            height: 12px;
            background: rgba(0, 0, 0, 0.95);
            border-top: 1px solid rgba(255, 255, 255, 0.2);
            border-right: 1px solid rgba(255, 255, 255, 0.2);
            transform: rotate(45deg);
        }
    `;

    function addStyles() {
        const style = document.createElement('style');
        style.innerText = STYLES;
        (document.head || document.documentElement).appendChild(style);
    }

    function getSavedHudSize() {
        try {
            const savedSize = JSON.parse(localStorage.getItem(HUD_SIZE_STORAGE_KEY) || 'null');
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
            console.warn('[Geoguessr Meta] Invalid saved HUD size:', err);
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
            const savedPosition = JSON.parse(localStorage.getItem(HUD_POSITION_STORAGE_KEY) || 'null');
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
        localStorage.setItem(HUD_POSITION_STORAGE_KEY, JSON.stringify({
            left: Math.round(rect.left),
            top: Math.round(rect.top)
        }));
    }

    function getAdminMetaSource(metaId) {
        return userMetaIds.has(metaId) ? 'user' : 'unknown';
    }

    function getAdminMetaSourceLabel(source) {
        return source === 'user' ? 'User' : 'Unknown';
    }

    function getAdminMetaLocationCounts(metaId) {
        const userPanoids = new Set();

        Object.entries(userLocationMap || {}).forEach(([panoid, entry]) => {
            if (getLocationMetaIds(entry).includes(metaId)) userPanoids.add(panoid);
        });

        return { user: userPanoids.size, total: userPanoids.size };
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

    function setAdminScopeSelection(scope) {
        const normalizedScope = normalizeScope(scope);
        const scopeContainer = document.getElementById('gg-admin-scope-presets');
        const scopeInput = document.getElementById('gg-admin-meta-scope');
        if (!scopeContainer || !scopeInput) return;

        scopeInput.value = normalizedScope;
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
        forEachCombinedLocationEntry((panoid, rawEntry) => {
            const entry = normalizeLocationEntry(rawEntry);
            if (!entry || !getLocationMetaIds(entry).includes(metaId)) return;
            linkedLocations.push({
                panoid,
                ...entry,
                displayCountry: entry.country || entry.nominatimCountry || ''
            });
        });
        return linkedLocations.sort((a, b) => compareAdminText(formatAdminLocationLabel(a), formatAdminLocationLabel(b)));
    }

    function formatAdminLocationLabel(location) {
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
            </div>
        `).join('');

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
                unlinkMetaFromAdminLocation(metaId, btn.dataset.panoid);
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

    function cloneJson(value) {
        return JSON.parse(JSON.stringify(value));
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
            pendingLocalChanges: cloneJson(loadPendingLocalChanges())
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

    async function getAdminMetaFromForm(existingMeta) {
        const readValue = id => (document.getElementById(id)?.value || '').trim();
        const updatedMeta = {
            ...existingMeta,
            title: readValue('gg-admin-meta-title'),
            description: readValue('gg-admin-meta-desc'),
            imageUrl: await resolveImageForSave(readValue('gg-admin-meta-image'), getCountrySlugForMeta(existingMeta)),
            scope: normalizeScope(readValue('gg-admin-meta-scope')),
            tags: normalizeTags(readValue('gg-admin-meta-tags'))
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
            return normalizePendingLocalChanges(JSON.parse(localStorage.getItem(PENDING_LOCAL_CHANGES_STORAGE_KEY) || 'null'));
        } catch (err) {
            console.warn('[BetterMetas] Invalid pending local changes:', err);
            return getEmptyPendingLocalChanges();
        }
    }

    function savePendingLocalChanges(pending) {
        const normalized = normalizePendingLocalChanges(pending);
        if (normalized.metas.length === 0 && Object.keys(normalized.locations).length === 0) {
            localStorage.removeItem(PENDING_LOCAL_CHANGES_STORAGE_KEY);
            return;
        }

        localStorage.setItem(PENDING_LOCAL_CHANGES_STORAGE_KEY, JSON.stringify(normalized));
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
            const pendingMetaIds = getLocationMetaIds(pending.locations[panoid]).filter(id => !rawMetaIdsForLocation.has(id));

            if (pendingMetaIds.length > 0) {
                const pendingEntry = Array.isArray(pending.locations[panoid])
                    ? { metas: pendingMetaIds }
                    : { ...pending.locations[panoid], metas: pendingMetaIds };
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
        console.log('[BetterMetas] Applied local location links:', {
            panoid,
            metaIds,
            usedKeys: Object.fromEntries(usedKeys),
            linkedMetaIds: Array.from(getLinkedMetaIdsForPanoid(userLocationMap, panoid))
        });
        refreshDisplay();
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
        console.log('[BetterMetas] Applied local location unlinks:', {
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
        console.log('[BetterMetas] Applied local saved meta:', {
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

    function showMetaTitleActionDialog({ title = '', action = '', canEdit = false } = {}) {
        const dialog = document.getElementById('gg-dialog-modal');
        const backdrop = document.getElementById('gg-modal-backdrop');
        if (!dialog) return Promise.resolve(null);

        const actionLabel = action === 'unlink' ? 'Unlink' : 'Link';
        const actionClass = action === 'unlink' ? 'gg-btn-danger' : 'gg-btn-primary';
        const metaTitle = String(title || '').trim();
        const maxEditTitleLength = 46;
        const truncatedMetaTitle = metaTitle.length > maxEditTitleLength
            ? `${metaTitle.slice(0, maxEditTitleLength - 3).trimEnd()}...`
            : metaTitle;
        const editLabel = truncatedMetaTitle ? `Edit "${truncatedMetaTitle}"` : 'Edit Meta';
        const editTitle = metaTitle ? `Edit "${metaTitle}"` : 'Edit Meta';
        const backdropWasVisible = Boolean(backdrop && backdrop.classList.contains('gg-visible'));
        const backgroundModals = getVisibleModalElementsForDialogBlur();
        setUiContext(dialog, action === 'unlink' ? 'danger' : (action === 'link' ? 'normal' : 'edit'));

        dialog.innerHTML = `
            <div class="gg-modal-header">Meta Actions</div>
            <div class="gg-dialog-actions gg-meta-action-buttons">
                ${canEdit ? `<button class="gg-btn-primary gg-btn-edit" id="gg-dialog-edit" title="${escapeHtml(editTitle)}"><span class="gg-dialog-edit-label">${escapeHtml(editLabel)}</span></button>` : ''}
                ${canEdit && action ? '<hr class="gg-modal-divider gg-meta-action-divider">' : ''}
                ${action ? `<button class="${actionClass}" id="gg-dialog-toggle">${escapeHtml(actionLabel)}</button>` : ''}
                <button class="gg-btn-secondary" id="gg-dialog-cancel">Cancel</button>
            </div>
        `;

        showBackdrop();
        backgroundModals.forEach(modal => modal.classList.add('gg-modal-background-blurred'));
        dialog.style.display = 'block';

        return new Promise(resolve => {
            const close = (result) => {
                backdrop?.removeEventListener('click', onBackdropClick);
                dialog.style.display = 'none';
                dialog.innerHTML = '';
                backgroundModals.forEach(modal => modal.classList.remove('gg-modal-background-blurred'));
                if (!backdropWasVisible) hideBackdrop();
                resolve(result);
            };

            // Clicking outside the menu closes it (same as cancelling). The
            // global backdrop handler ignores clicks while a dialog is open,
            // so this menu has to handle it itself. Stop propagation so the
            // global handler can never also close the modals underneath.
            const onBackdropClick = (event) => {
                if (event.target !== backdrop) return;
                event.stopImmediatePropagation();
                close(null);
            };
            backdrop?.addEventListener('click', onBackdropClick);

            const cancelBtn = dialog.querySelector('#gg-dialog-cancel');
            const editBtn = dialog.querySelector('#gg-dialog-edit');
            const toggleBtn = dialog.querySelector('#gg-dialog-toggle');

            cancelBtn.addEventListener('click', () => close(null), { once: true });
            if (editBtn) editBtn.addEventListener('click', () => close('edit'), { once: true });
            if (toggleBtn) toggleBtn.addEventListener('click', () => close(action), { once: true });

            requestAnimationFrame(() => (toggleBtn || editBtn || cancelBtn).focus());
        });
    }

    // --- UI Construction ---
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

            <div id="gg-meta-container" class="gg-meta-content">
                <div class="gg-empty-state">Waiting for location...</div>
            </div>
            <div id="gg-status" class="gg-status-msg" title="Click to retry finding location">Waiting for location...</div>
        `;
        document.body.appendChild(hud);

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
                localStorage.setItem(HUD_SIZE_STORAGE_KEY, JSON.stringify(size));
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

        // Stop propagation for Settings inputs
        const settInputs = settingsModal.querySelectorAll('input');
        settInputs.forEach(input => {
            input.addEventListener('keydown', (e) => e.stopPropagation());
            input.addEventListener('keypress', (e) => e.stopPropagation());
            input.addEventListener('keyup', (e) => e.stopPropagation());
        });
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
                                <option value="title">Title</option>
                                <option value="scope">Scope</option>
                                <option value="tags">Tags</option>
                                <option value="newest">Recently Updated</option>
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

        adminModal.querySelectorAll('input, textarea').forEach(input => {
            input.addEventListener('keydown', (e) => e.stopPropagation());
            input.addEventListener('keypress', (e) => e.stopPropagation());
            input.addEventListener('keyup', (e) => e.stopPropagation());
        });

        adminModal.querySelector('#gg-admin-scope-presets').addEventListener('click', (e) => {
            const target = getEventElementTarget(e);
            if (!target || !target.classList.contains('gg-tag-pill')) return;

            adminModal.querySelectorAll('#gg-admin-scope-presets .gg-tag-pill').forEach(pill => {
                pill.classList.toggle('gg-tag-selected', pill === target);
            });
            document.getElementById('gg-admin-meta-scope').value = target.dataset.value || '';
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

        // Stop propagation for inputs to prevent game shortcuts
        const inputs = modal.querySelectorAll('input, textarea');
        inputs.forEach(input => {
            input.addEventListener('keydown', (e) => e.stopPropagation());
            input.addEventListener('keypress', (e) => e.stopPropagation());
            input.addEventListener('keyup', (e) => e.stopPropagation());
        });

        document.body.appendChild(modal);

        // Event Listeners
        document.getElementById('gg-meta-admin-btn').addEventListener('click', async () => {
            selectedAdminMetaId = null;
            adminSortMode = 'title';
            const searchInput = document.getElementById('gg-admin-search');
            searchInput.value = '';
            updateAdminSortButtons();
            showAdminMainView();
            renderAdminMetas();
            hidePreviewPopup();
            showAdminModal();
            requestAnimationFrame(() => searchInput.focus());
        });

        document.getElementById('gg-meta-add-btn').addEventListener('click', async () => {
            syncPanoidForUserAction('open add modal');

            // Try to recover Panoid if missing (e.g. script loaded late on result screen)
            if (!currentPanoid) {
                updateStatus('Finding location...');
                await tryRecoverPanoid();
            }

            // Allow opening even without active location for testing, but warn
            if (!currentPanoid) {
                console.log('No active location found even after recovery attempt.');
                // Optional: Alert user?
            }
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

        document.getElementById('gg-settings-btn').addEventListener('click', () => {
            // Render Scope Filter
            const scopeContainer = document.getElementById('gg-settings-scope-filter');
            scopeContainer.innerHTML = renderScopePills(ALL_SCOPES, activeScopes);

            // Add listeners
            scopeContainer.querySelectorAll('.gg-tag-pill').forEach(pill => {
                pill.addEventListener('click', (e) => {
                    const target = getEventElementTarget(e);
                    if (!target) return;
                    // Only toggle UI state, do NOT save yet
                    target.classList.toggle('gg-tag-selected');
                });
            });

            // Render Tag Filter
            const tagContainer = document.getElementById('gg-settings-tag-filter');
            tagContainer.innerHTML = renderTagFilterPills(TAG_PRESETS, activeTags);

            tagContainer.querySelectorAll('.gg-tag-pill').forEach(pill => {
                pill.addEventListener('click', (e) => {
                    const target = getEventElementTarget(e);
                    if (!target) return;
                    // Only toggle UI state, do NOT save yet
                    target.classList.toggle('gg-tag-selected');
                });
            });

            hidePreviewPopup();
            showSettingsModal();
        });

        document.getElementById('gg-save-settings').addEventListener('click', () => {
             // Save Scopes from UI state
             const scopeContainer = document.getElementById('gg-settings-scope-filter');
             const selectedFromUI = Array.from(scopeContainer.querySelectorAll('.gg-tag-pill.gg-tag-selected'))
                                         .map(el => el.dataset.value);

             activeScopes = new Set(selectedFromUI);
             localStorage.setItem(ACTIVE_SCOPES_STORAGE_KEY, JSON.stringify(Array.from(activeScopes)));

             // Save Tags from UI state
             const tagContainer = document.getElementById('gg-settings-tag-filter');
             const selectedTagsFromUI = Array.from(tagContainer.querySelectorAll('.gg-tag-pill.gg-tag-selected'))
                                         .map(el => el.dataset.value);

             activeTags = new Set(selectedTagsFromUI);
             localStorage.setItem(ACTIVE_TAGS_STORAGE_KEY, JSON.stringify(Array.from(activeTags)));

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
            adminSortMode = e.target.value || 'title';
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
        const selectedOption = sortSelect.selectedOptions[0];
        if (!selectedOption) return;

        const context = document.createElement('canvas').getContext('2d');
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

    function sortAdminMetaEntries(entries) {
        const scopeOrder = new Map(ALL_SCOPES.map((scope, index) => [scope, index]));
        return entries.sort((a, b) => {
            const metaA = a.meta;
            const metaB = b.meta;
            if (adminSortMode === 'scope') {
                const scopeA = scopeOrder.get(normalizeScope(metaA.scope)) ?? Number.MAX_SAFE_INTEGER;
                const scopeB = scopeOrder.get(normalizeScope(metaB.scope)) ?? Number.MAX_SAFE_INTEGER;
                return scopeA - scopeB
                    || compareAdminTitle(metaA, metaB);
            }

            if (adminSortMode === 'tags') {
                return compareAdminText((metaA.tags || []).join(', '), (metaB.tags || []).join(', '))
                    || compareAdminTitle(metaA, metaB);
            }

            if (adminSortMode === 'newest') {
                return getAdminMetaUpdatedSortValue(metaB, b.index) - getAdminMetaUpdatedSortValue(metaA, a.index)
                    || compareAdminTitle(metaA, metaB);
            }

            return compareAdminTitle(metaA, metaB);
        });
    }

    function getMetaSearchTerms(searchTerm) {
        return searchTerm.toLowerCase().split(/[;,]/).map(term => term.trim()).filter(Boolean);
    }

    function matchesMetaSearch(meta, terms, extraValues = []) {
        if (terms.length === 0) return true;
        const indexedContent = ensureMetaSearchIndex().get(meta.id) || '';
        const searchableContent = extraValues.length
            ? `${indexedContent} ${extraValues.filter(Boolean).join(' ').toLowerCase()}`
            : indexedContent;
        return terms.every(term => searchableContent.includes(term));
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

        const filtered = metasData.map((meta, index) => ({ meta, index })).filter(entry => {
            const meta = entry.meta;
            const source = getAdminMetaSourceLabel(getAdminMetaSource(meta.id));
            return matchesMetaSearch(meta, terms, [
                meta.id || '',
                source,
                meta.scope || '',
            ]);
        });

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

        const finishUi = beginMutationUi({
            scope: adminModal,
            button: btn,
            busyText: isLinked ? 'Unlinking...' : 'Linking...',
            statusText: isLinked ? 'Removing meta...' : 'Linking meta...'
        });
        if (!finishUi) return;

        const snapshot = createLocalDataSnapshot();

        try {
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
                    if (getAdminMetaSource(metaId) !== 'user') {
                        throw new Error(`Unknown meta source for ${metaId}`);
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
        } catch (e) {
            console.error(e);
            restoreLocalDataSnapshot(snapshot);
            await showToolAlert(isLinked ? 'Unlink Failed' : 'Link Failed', e.message);
            updateStatus(isLinked ? 'Unlink Failed' : 'Link Failed');
        } finally {
            finishUi();
        }

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
        const finishUi = beginMutationUi({
            scope: document.getElementById('gg-meta-modal'),
            button: linkBtn,
            busyText: 'Linking...',
            statusText: `Linking ${metaIds.length} metas...`
        });
        if (!finishUi) return;

        const snapshot = createLocalDataSnapshot();
        let linkedSuccessfully = false;

        try {
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
            linkedSuccessfully = true;
            scheduleBackgroundDataRefresh();
        } catch (e) {
            console.error(e);
            restoreLocalDataSnapshot(snapshot);
            await showToolAlert('Link Failed', e.message);
            updateStatus('Link Failed');
        } finally {
            finishUi();
            if (linkedSuccessfully) {
                selectedMetaIds.clear();
                updateLinkSelectedBtn();
                renderExistingMetas(document.getElementById('meta-search')?.value || '');
            }
        }
    }

    async function unlinkMultipleMetas(metaIds) {
        const panoid = syncPanoidForUserAction('unlink metas');
        if (!panoid || panoid === MISSING_PANOID_PLACEHOLDER) {
            await showToolAlert('No Location Detected', 'Please try on a game result screen.');
            return;
        }

        const linkedUserMetaIds = getLinkedMetaIdsForPanoid(userLocationMap, panoid);
        const removableMetaIds = metaIds.filter(id => linkedUserMetaIds.has(id));
        if (removableMetaIds.length === 0) {
            await showToolAlert('Cannot Unlink Meta', 'This meta is not linked through your BetterMetas data and cannot be unlinked here.');
            return;
        }

        const finishUi = beginMutationUi({
            scope: document.getElementById('gg-meta-hud'),
            busyText: 'Unlinking...',
            statusText: `Removing ${removableMetaIds.length} meta${removableMetaIds.length === 1 ? '' : 's'}...`
        });
        if (!finishUi) return;

        const snapshot = createLocalDataSnapshot();

        try {
            applyLocalLocationUnlinks(panoid, removableMetaIds);
            updateStatus('Unlinked. Syncing...');

            await updateLocalJsonFile(
                USER_LOCATIONS_FILE,
                normalizeLocationMap,
                locations => {
                    removeMetaIdsFromPanoidLocations(locations, panoid, removableMetaIds);
                    return locations;
                },
                `Unlink ${removableMetaIds.length} metas from ${panoid} via BetterMetas`
            );

            updateStatus('Unlinked!');
            scheduleBackgroundDataRefresh();
        } catch (e) {
            console.error(e);
            restoreLocalDataSnapshot(snapshot);
            await showToolAlert('Unlink Failed', e.message);
            updateStatus('Unlink Failed');
        } finally {
            finishUi();
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

        const finishUi = beginMutationUi({
            scope: document.getElementById('gg-meta-admin-modal'),
            busyText: 'Unlinking...',
            statusText: `Unlinking ${panoid}...`
        });
        if (!finishUi) return;

        const snapshot = createLocalDataSnapshot();

        try {
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
        } catch (e) {
            console.error(e);
            restoreLocalDataSnapshot(snapshot);
            await showToolAlert('Unlink Failed', e.message);
            updateStatus('Unlink Failed');
        } finally {
            finishUi();
        }

        updateAdminLinkButton();
    }

    async function generateJSON() {
        const title = document.getElementById('meta-title').value;
        const desc = document.getElementById('meta-desc').value;
        const tagsStr = document.getElementById('meta-tags').value;
        const tags = normalizeTags(tagsStr);
        const rawImageValue = document.getElementById('meta-image').value;
        const scope = normalizeScope(document.getElementById('meta-scope').value);

        if (!title || !desc) {
            await showToolAlert('Missing Details', 'Please fill in Title and Description.');
            return;
        }

        const panoid = syncPanoidForUserAction('save meta') || MISSING_PANOID_PLACEHOLDER;
        if (panoid === MISSING_PANOID_PLACEHOLDER) {
            await showToolAlert('No Location Detected', 'Please try again on a game result screen.');
            return;
        }

        // An image import needs the country (folder name); wait for geocoding.
        const needsImageImport = rawImageValue.trim() && !isLocalImagePath(rawImageValue);
        const detectedCountryFolder = needsImageImport ? await waitForDetectedCountryFolder() : null;

        // Generate unique meta ID
        const metaId = generateMetaId();
        const imageUrl = await resolveImageForSave(rawImageValue, detectedCountryFolder || getCountryFolderForLocation(getCurrentLocationSnapshot()) || getCountrySlugForMeta({ id: metaId }));
        // Metas created here are always linked to a location right away, and
        // that location entry stores lat/lng/country/nominatimCountry plus the
        // scope-relevant field (region/city/road) based on the meta's scope
        // (see ensureLocationEntry/getLocationSnapshotForScope). Don't duplicate
        // those fields onto the meta itself - user_locations.json is the
        // single source of truth for them.

        const newMeta = {
            id: metaId,
            title: title,
            description: desc,
            imageUrl: imageUrl,
            scope: scope,
            tags: tags,
            updatedAt: new Date().toISOString()
        };

        // Kept around as a readable backup blob if the local save fails.
        const submission = {
            action: "add_meta",
            panoid: panoid,
            meta: newMeta
        };

        const btn = document.getElementById('meta-generate-btn');
        const output = document.getElementById('gg-json-output');

        const finishUi = beginMutationUi({
            scope: document.getElementById('gg-meta-modal'),
            button: btn,
            busyText: 'Saving...',
            statusText: 'Saving meta...'
        });
        if (!finishUi) return;

        output.style.display = 'none';
        const snapshot = createLocalDataSnapshot();

        try {
            applyLocalSavedMeta(newMeta, panoid);
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

            updateStatus('Saving user_locations.json...');
            await updateLocalJsonFile(
                USER_LOCATIONS_FILE,
                normalizeLocationMap,
                locations => {
                    addMetaIdsToLocationMap(locations, panoid, [newMeta.id], newMeta.scope);
                    return locations;
                },
                `Link ${panoid} to ${newMeta.id} via BetterMetas`
            );

            updateStatus('Saved!');
            scheduleBackgroundDataRefresh();
            setTimeout(() => finishUi({ buttonText: META_SAVE_BUTTON_LABEL }), SAVE_COMPLETE_RESET_MS);

        } catch (err) {
            console.error('Save error:', err);
            restoreLocalDataSnapshot(snapshot);
            showMetaModal();
            output.textContent = `Error saving locally:\n${err.message}\n\nBackup JSON:\n${stringifyJsonContent(submission)}`;
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

        const updatedMeta = await getAdminMetaFromForm(existingMeta);
        if (!updatedMeta.title || !updatedMeta.description) {
            await showToolAlert('Missing Details', 'Please fill in Title and Description.');
            return;
        }

        const source = getAdminMetaSource(existingMeta.id);
        const saveBtn = document.getElementById('gg-admin-save-btn');
        const finishUi = beginMutationUi({
            scope: document.getElementById('gg-meta-admin-modal'),
            button: saveBtn,
            busyText: 'Saving...',
            statusText: `Saving meta ${existingMeta.id}...`
        });
        if (!finishUi) return;

        const snapshot = createLocalDataSnapshot();
        const previousImagePath = String(existingMeta.imageUrl || '').trim();
        const newImagePath = String(updatedMeta.imageUrl || '').trim();
        let previousImageStillUsed = true; // Safe default: never delete unless proven unused.

        try {
            const savedMetaId = existingMeta.id;
            applyAdminMetaLocally(updatedMeta);

            // Scope changed: the location(s) the meta is linked to here must get the
            // fields of the new scope (region / city / road) instead of keeping the old ones.
            let relinkPanoid = null;
            const scopeChanged = source === 'user' &&
                normalizeScope(existingMeta.scope) !== normalizeScope(updatedMeta.scope);
            if (scopeChanged) {
                const panoid = syncPanoidForUserAction('update meta scope');
                if (panoid && panoid !== MISSING_PANOID_PLACEHOLDER &&
                    applyLocalScopeRelink(panoid, savedMetaId, existingMeta.scope, updatedMeta.scope)) {
                    relinkPanoid = panoid;
                }
            }

            renderAdminMetas(document.getElementById('gg-admin-search')?.value || '');
            openAdminMetaDetails(savedMetaId);
            if (currentPanoid) refreshDisplay();
            updateStatus('Meta saved. Syncing...');

            if (source === 'user') {
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
            } else {
                throw new Error(`Unknown meta source for ${existingMeta.id}`);
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

        const counts = getAdminMetaLocationCounts(existingMeta.id);
        const confirmed = await showToolConfirm(
            'Delete Meta',
            `This will delete "${existingMeta.title || existingMeta.id}" and unlink it from ${counts.total} location${counts.total === 1 ? '' : 's'}.`,
            {
                confirmText: 'Delete Meta',
                cancelText: 'Cancel',
                danger: true
            }
        );
        if (!confirmed) return;

        const source = getAdminMetaSource(existingMeta.id);
        const actionBtn = actionButton || document.getElementById('gg-admin-delete-btn');
        const finishUi = beginMutationUi({
            scope: document.getElementById('gg-meta-admin-modal'),
            button: actionBtn,
            busyText: 'Deleting...',
            statusText: `Deleting meta ${existingMeta.id}...`
        });
        if (!finishUi) return;

        const snapshot = createLocalDataSnapshot();
        const deletedImagePath = String(existingMeta.imageUrl || '').trim();
        let deletedImageStillUsed = true; // Safe default: never delete unless proven unused.

        try {
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

            if (source === 'user') {
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
                throw new Error(`Unknown meta source for ${deletedMetaId}`);
            }

            // Remove the imported image (data/<country>/<file>) once nothing uses it.
            if (!deletedImageStillUsed) await removeLocalImage(deletedImagePath);

            refreshAfterAdminMutation().catch(err => {
                console.warn('[BetterMetas] Admin data refresh after delete failed:', err);
            });
            updateStatus('Meta deleted!');
        } catch (err) {
            console.error(err);
            restoreLocalDataSnapshot(snapshot);
            await showToolAlert('Delete Failed', err.message || String(err));
            updateStatus('Delete Failed');
        } finally {
            finishUi();
        }
    }

    function updateHUD(metas, predicted = []) {
        const container = document.getElementById('gg-meta-container');
        if (!container) return;
        const exactMetas = metas || [];
        const predictedMetas = predicted || [];
        const canEditMetas = true;
        const userLinkedMetaIds = getLinkedMetaIdsForPanoid(userLocationMap, currentPanoid);
        const renderKey = JSON.stringify([
            currentPanoid,
            metaRenderVersion,
            canEditMetas,
            exactMetas.map(meta => meta.id),
            predictedMetas.map(meta => meta.id),
            exactMetas.filter(meta => userLinkedMetaIds.has(meta.id)).map(meta => meta.id)
        ]);
        if (renderKey === lastHudRenderKey) return;
        resetHudImageLoading(container);

        if (exactMetas.length === 0 && predictedMetas.length === 0) {
            container.innerHTML = '<div class="gg-muted-empty-state">No active hints for this location.</div>';
            lastHudRenderKey = renderKey;
            return;
        }

        const renderMeta = (m, isPredicted = false) => {
             const isUserLinked = userLinkedMetaIds.has(m.id);
             const titleAction = isPredicted ? 'link' : (isUserLinked ? 'unlink' : '');
             const titleText = m.title || m.id;
             const titleTooltip = canEditMetas
                 ? 'Click to Edit Meta'
                 : (titleAction === 'link' ? 'Click to Link to this Location' : 'Click to Unlink from this Location');
             const titleAttr = (titleAction || canEditMetas)
                 ? `class="gg-clickable-meta-title" data-meta-id="${escapeHtml(m.id)}" data-meta-title="${escapeHtml(titleText)}" data-action="${escapeHtml(titleAction)}" title="${escapeHtml(titleTooltip)}"`
                 : '';

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

        container.querySelectorAll('.gg-clickable-meta-title').forEach(titleEl => {
            titleEl.addEventListener('click', () => {
                win.handleMetaTitleClick(titleEl.dataset.metaId, titleEl.dataset.metaTitle || '', titleEl.dataset.action || '');
            });
        });
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

    win.handleMetaTitleClick = async function(metaId, title, action = '') {
        await openMetaEditorFromTitle(metaId);
    };


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
        const exactMetas = sortLinkedMetasByPrecision(metaIds.map(id => {
            const found = getMetaById(id);
            if (!found) console.warn('[BetterMetas] Could not find exact meta data for ID:', id);
            return found;
        }).filter(Boolean).filter(isScopeActive).filter(isTagActive));

        // Get predicted/nearby metas
        const predictedMetas = evaluateProximityMetas()
            .filter(pm => !metaIds.includes(pm.id))
            .filter(isScopeActive)
            .filter(isTagActive);

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
		console.log(visiblePanoid, queuedPanoid, activePanoid, isValidPanoid(activePanoid));

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

    async function tryRecoverPanoid() {
        return syncPanoidForUserAction('panoid recovery');
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

    function getDistanceForScope(scope) {
        const s = normalizeScope(scope);
        if (s === '1km') return 1;
        if (s === '10km') return 10;
        if (s === '100km') return 100;

        // Named scopes should match by NAME, not generic radius
        if (s === 'region') return 0;
        if (s === 'city') return 0;
        if (s === 'road') return 0; // Strict Name Match Only (User request: no radius for road/region)
        if (s === 'unique') return 0; // 0m tolerance

        if (s === 'countrywide') return 0; // Strict Country Check Only
        return 0;
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

    /**
     * Strict name matching for location names (accent/case-insensitive exact match).
     * No generic-word filtering: the stored name must match the detected name exactly
     * (after normalization).
     */
    function stripDiacritics(value) {
        return String(value || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '');
    }

    function normalizeNameForMatch(value) {
        return stripDiacritics(String(value || '')).toLowerCase().trim();
    }

    function isFuzzyNameMatch(a, b) {
        if (!a || !b) return false;
        return normalizeNameForMatch(a) === normalizeNameForMatch(b);
    }

    /**
     * Finds relevant metas for current location based on active scopes.
     * Checks both exact distance matches and fuzzy name matches (Region/Road).
     */
    function evaluateProximityMetas() {
        const curLat = normalizeCoordinate(currentLocationData.lat);
        const curLng = normalizeCoordinate(currentLocationData.lng);
        const curCountry = normalizeCountry(currentLocationData.country, curLat, curLng);
        const curNomCountry = normalizeCountry(currentLocationData.nominatimCountry, curLat, curLng);
        const curRegion = currentLocationData.region;
        const curCity = currentLocationData.city;

        const curRoads = getNormalizedRoadNames(currentLocationData.road);

        if (curLat === null || curLng === null) return [];

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
            curRoads
        ]);
        if (proximityCacheKey === lastProximityCacheKey) return lastProximityMatches;

        // Helper: Check meta match against location
        const checkMatch = (scope, entryLat, entryLng, entryCountry, entryRegion, entryCity, entryRoads) => {
             scope = normalizeScope(scope);

             // 1. Distance Match
             const distLimit = getDistanceForScope(scope);
             if (distLimit > 0) {
                 if (entryLat !== null && entryLng !== null) {
                     const d = getHaversineDistance(curLat, curLng, entryLat, entryLng);
                     if (d <= distLimit) return true;
                 }
                 return false;
             }

             // 2. Name Match (Region/City/Road)
             // Requires Country match to avoid ambiguity (except Countrywide)
             const countryMatch = (entryCountry === curCountry || entryCountry === curNomCountry);
             if (!countryMatch) return false;

             if (scope === 'countrywide') return true;

             if (scope === 'region') {
                 return isFuzzyNameMatch(entryRegion, curRegion);
             }

             if (scope === 'city') {
                 if (!isFuzzyNameMatch(entryCity, curCity)) return false;
                 // Same city name in another region is a different city. The
                 // region is only ignored when either side has no region data.
                 if (entryRegion && curRegion && !isFuzzyNameMatch(entryRegion, curRegion)) return false;
                 return true;
             }

             if (scope === 'road') {
                 // Check if ANY entry road matches ANY current road
                 if (!entryRoads || entryRoads.length === 0) return false;
                 if (curRoads.length === 0) return false;

                 return curRoads.some(cr => entryRoads.some(er => isFuzzyNameMatch(cr, er)));
             }

             return false;
        };

        // Location values are normalized once per data change, not on every HUD refresh.
        indexedLocationEntries.forEach(entry => {
            entry.metaIds.forEach(id => {
                 if (matchedMetaIds.has(id)) return; // Already matched
                 const meta = getMetaById(id);
                 if (!meta) return;

                 if (checkMatch(meta.scope, entry.lat, entry.lng, entry.country, entry.region, entry.city, entry.roads)) {
                     matchedMetaIds.add(id);
                     matches.push(meta);
                 }
            });
        });

        lastProximityCacheKey = proximityCacheKey;
        lastProximityMatches = matches;
        return matches;
    }

    function isRoundResult() {
        const selector = document.querySelectorAll('[alt="Correct location"]');
        return selector.length > 0;
    }

    function updateVisibility(resultActive = isRoundResult()) {
		const hud = document.getElementById('gg-meta-hud');
        if (!hud) return;

        if (resultActive) {
            hud.classList.add('gg-visible');
            return;
        }
		
		hud.classList.remove('gg-visible');
        return;
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

        if (changed) {
            debugLog('[BetterMetas] New Location detected:', panoid);
            updateStatus(`ID: ${panoid.substring(0,12)}...`);

            // Trigger Location Data Extraction Immediately
            extractLocationData();
        }

        // Trigger Display Refresh (this handles checking if data is loaded)
        refreshDisplay();
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
                // Check if we can get location data
                let loc = null;
                if (typeof svInstance.getLocation === 'function') {
                    loc = svInstance.getLocation();
                }

                if (loc) {
                    const desc = loc.description || loc.shortDescription || "Unknown Location";
                    const latLng = loc.latLng;
                    const lat = latLng ? (typeof latLng.lat === 'function' ? latLng.lat() : latLng.lat) : 0;
                    const lng = latLng ? (typeof latLng.lng === 'function' ? latLng.lng() : latLng.lng) : 0;

                    debugLog(`[BetterMetas] Location Found: ${desc} (${lat}, ${lng})`);

                    // Simple heuristic for "Country" from address (last part after comma)
                    let country = "Unknown";
                    if (desc && desc.includes(',')) {
                        const parts = desc.split(',');
                        country = parts[parts.length - 1].trim();
                        // Filter out zip codes if mixed in (basic check)
                        if (/^\d+$/.test(country) && parts.length > 1) {
                            country = parts[parts.length - 2].trim();
                        }
                    } else {
                        country = desc; // Fallback
                    }

                    // Check if we already have this location data to prevent overwriting with nulls during race conditions
                    const newLatStr = lat.toFixed(5);
                    const newLngStr = lng.toFixed(5);

                    if (currentLocationData &&
                        currentLocationData.lat === newLatStr &&
                        currentLocationData.lng === newLngStr) {

                        // Location hasn't changed.
                        // If we already have a Road, don't wipe it out!
                        if (currentLocationData.road) {
                            debugLog('[BetterMetas] Road already exists for this location, skipping reset/re-geocode.');
                            // Ensure HUD is refreshed just in case
                            if (currentPanoid) checkLocation(currentPanoid);
                            return;
                        }

                        // If we don't have a road, we might want to let it proceed to geocoding...
                        // But we should carry over existing country/region/address if valid
                        currentLocationData.address = currentLocationData.address || desc;
                        currentLocationData.country = currentLocationData.country || country;
                        // Region and Road are null, so let them be re-fetched below

                    } else {
                        // New location, reset
                        currentLocationData = {
                            address: desc,
                            country: country,
                            region: null,
                            city: null,
                            road: null,
                            lat: newLatStr,
                            lng: newLngStr
                        };
                    }

                    updateLocationUI();

                    // Immediate trigger with basic info (Lat/Lng is enough for radius checks)
                    if (currentPanoid) checkLocation(currentPanoid);

                    // Dual Geocoding Strategy
                    const latVal = parseFloat(lat);
                    const lngVal = parseFloat(lng);
                    const geocodeKey = `${newLatStr},${newLngStr}`;
                    if (recentlyGeocodedLocations.has(geocodeKey)) {
                        debugLog('[BetterMetas] Geocoding already running for this location.');
                        return;
                    }
                    recentlyGeocodedLocations.add(geocodeKey);
                    setTimeout(() => recentlyGeocodedLocations.delete(geocodeKey), 10000);

                    // 1. Google Geocoding (Dominant for country)
                    sharedGeocoder ||= new win.google.maps.Geocoder();
                    sharedGeocoder.geocode({ location: { lat: latVal, lng: lngVal } }, (results, status) => {
                        if (status === "OK" && results[0]) {
                            const res = results[0];
                            const addrComp = res.address_components;

                            let gCountry = null;
                            let gRegion = null;
                            let gCity = null;
                            let gRoad = null;

                            addrComp.forEach(comp => {
                                if (comp.types.includes("country")) gCountry = comp.long_name;
                                if (comp.types.includes("administrative_area_level_1")) gRegion = comp.long_name;
                                if (comp.types.includes("locality") || comp.types.includes("administrative_area_level_2")) {
                                    if (!gCity) gCity = comp.long_name; // Prefer locality
                                }
                                if (comp.types.includes("route")) gRoad = comp.long_name;
                            });

                            if (currentLocationData.lat === newLatStr && currentLocationData.lng === newLngStr) {
                                currentLocationData.googleCountry = gCountry;
                                // Primary country selection (Google preferred)
                                if (gCountry) {
                                    currentLocationData.country = normalizeCountry(gCountry, lat, lng);
                                }

                                if (gRegion && !currentLocationData.region) currentLocationData.region = gRegion;
                                if (gCity && !currentLocationData.city) currentLocationData.city = gCity;
                                if (gRoad && !currentLocationData.road) currentLocationData.road = gRoad;

                                updateLocationUI();
                                if (currentPanoid) checkLocation(currentPanoid);
                            }
                        } else {
                            console.warn('[BetterMetas] Google geocode failed:', status);
                        }
                    });

                    // 2. Nominatim Geocoding (Detail/Fallback)
                    const nominatimUrl = `https://nominatim.openstreetmap.org/reverse?format=json&lat=${latVal}&lon=${lngVal}&accept-language=en`;
                    if (activeNominatimController && activeNominatimKey !== geocodeKey) {
                        activeNominatimController.abort();
                    }
                    const nominatimController = typeof AbortController === 'function' ? new AbortController() : null;
                    activeNominatimController = nominatimController;
                    activeNominatimKey = geocodeKey;
                    fetch(nominatimUrl, {
                        headers: { 'User-Agent': 'GeoguessrBetterMetas/1.0' },
                        signal: nominatimController?.signal
                    })
                    .then(response => response.json())
                    .then(data => {
                        if (data && data.address) {
                            const a = data.address;
                            const address = data.display_name;
                            let nCountry = a.country || country;
                            let realNomCountry = normalizeCountry(nCountry, lat, lng);
                            let region = a.state || a.region || a.province || a.county || a.district || null;
                            let city = a.city || a.town || a.village || a.hamlet || a.municipality || null;

                            // Road Logic
                            let road = null;
                            const roadName = a.road || a.pedestrian || a.highway || a.street || a.suburb || a.hamlet || a.village || null;
                            if (roadName) {
                                if (roadName.includes(';')) {
                                    road = roadName.split(';').map(s => s.trim());
                                } else {
                                    road = roadName;
                                }
                            }

                            // Fallback: If still no road, use shortDescription if it looks like a road
                            if (!road && loc.shortDescription && loc.shortDescription !== loc.description && loc.shortDescription !== realNomCountry) {
                                if (loc.shortDescription !== region && loc.shortDescription !== city) {
                                    road = loc.shortDescription;
                                }
                            }

                            // Update Location Data (if still relevant)
                            if (currentLocationData.lat === newLatStr && currentLocationData.lng === newLngStr) {
                                currentLocationData.nominatimCountry = realNomCountry;
                                currentLocationData.address = address; // Prefer Nominatim address

                                // Fallback for Country if Google failed
                                if (!currentLocationData.country) {
                                    currentLocationData.country = realNomCountry;
                                }

                                if (region && !currentLocationData.region) currentLocationData.region = region;
                                if (city && !currentLocationData.city) currentLocationData.city = city;
                                if (road && !currentLocationData.road) currentLocationData.road = road;
                            }

                            updateLocationUI();
                            if (currentPanoid) checkLocation(currentPanoid);
                        }
                    })
                    .catch(error => {
                        if (error?.name !== 'AbortError') {
                            console.error('[BetterMetas] Nominatim geocode failed:', error);
                        }
                    })
                    .finally(() => {
                        if (activeNominatimController === nominatimController) {
                            activeNominatimController = null;
                            activeNominatimKey = null;
                        }
                    });
                } else {
                    debugLog(`[BetterMetas] svInstance.getLocation() returned null/empty (Attempt ${attempt+1}/${maxAttempts}).`);
                    if (attempt < maxAttempts) {
                        extractLocationData(attempt + 1, extractionId);
                    }
                }
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
    // local-server.js): no GitHub, no token, no network commit involved.
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

        if (options.allowMissing) {
            console.warn(`[BetterMetas] ${label} unavailable after retries, continuing with empty data:`, lastError);
            return defaultValue;
        }

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
        console.log(`[BetterMetas] Loaded ${options.count(data)} ${options.description}.`);
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
        console.log('[BetterMetas] Fetching data...');
        updateStatus(metasData.length > 0 ? 'Refreshing DB...' : 'Loading DB...');
        const loadId = ++dataLoadSequence;

        try {
            const [loadedUserLocationMap, loadedUserMetas] = await Promise.all([
                loadDataSource(DATA_SOURCES.userLocations),
                loadDataSource(DATA_SOURCES.userMetas)
            ]);

            if (loadId !== dataLoadSequence) {
                console.log('[BetterMetas] Ignoring stale DB load result.');
                return;
            }

            const snapshot = {
                userLocationMap: loadedUserLocationMap,
                userMetas: loadedUserMetas
            };
            const applied = applyDataSnapshot(snapshot, { prunePending: true, alreadyNormalized: true });
            saveDataSnapshotCache(snapshot);

            const locCount = getCombinedLocationCount();
            const userLocCount = Object.keys(userLocationMap).length;
            const pendingLocCount = Object.keys(applied.pending.locations).length;
            console.log(`[BetterMetas] DB Ready: ${locCount} locs (${userLocCount} user), ${metasData.length} metas (${userMetaIds.size} user). Pending local merge: ${applied.pending.metas.length} metas, ${pendingLocCount} locs.`);

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

        console.log('[BetterMetas] Google Maps API found. Installing hooks...');

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
        console.log('[BetterMetas] Hooks installed successfully.');
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
                 console.log('[BetterMetas] Applying queued panoid:', nextPanoid);
                 checkLocation(nextPanoid, { bypassResultLock: true });
             }
         };
         setInterval(runVisibilityPoll, VISIBILITY_POLL_INTERVAL_MS);
         document.addEventListener('visibilitychange', () => {
             if (!document.hidden) runVisibilityPoll();
         });

         // Hook Poller - wait for Google Maps
         const timer = setInterval(() => {
            if (installHooks()) {
                clearInterval(timer);
            }
         }, 25);

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

         console.log('[BetterMetas] Observer started.');
    }

    // --- Initialization ---
    function initUI() {
        if (uiInitialized) return true;
        if (!document.body) return false;

        uiInitialized = true;
        console.log('[Geoguessr Meta] Initializing UI...');
        addStyles();
        createHUD();
        applyCachedDataSnapshot();
        fetchLocationData();
        return true;
    }

    function scheduleUIInit() {
        if (initUI()) return;

        const tryInit = () => {
            if (initUI()) {
                document.removeEventListener('DOMContentLoaded', tryInit);
            }
        };

        document.addEventListener('DOMContentLoaded', tryInit, { once: true });
        const timer = setInterval(() => {
            if (initUI()) clearInterval(timer);
        }, 25);
    }

    function init() {
        console.log('[Geoguessr Meta] Initializing...');
        startObserver();
        scheduleUIInit();
    }

    init();

})();
