// Minimal dev server for BetterMetas local testing.
// Replaces `npx serve .`: serves files from this directory (GET) and lets the
// Tampermonkey script write data/*.json back to disk (PUT).
//
// Usage: node local-server.js [port]   (default port 3000)

const http = require('http');
const fs = require('fs');
const fsp = fs.promises;
const path = require('path');
const crypto = require('crypto');

const PORT = Number(process.argv[2]) || 3000;
const ROOT = __dirname;

const CONTENT_TYPES = {
    '.json': 'application/json; charset=utf-8',
    '.js': 'text/javascript; charset=utf-8',
    '.html': 'text/html; charset=utf-8',
    '.css': 'text/css; charset=utf-8',
    '.png': 'image/png',
    '.jpg': 'image/jpeg',
    '.jpeg': 'image/jpeg',
    '.webp': 'image/webp',
    '.gif': 'image/gif',
    '.avif': 'image/avif'
};

const IMAGE_EXTENSIONS = new Set(['.png', '.jpg', '.jpeg', '.webp', '.gif', '.avif']);
const DATA_DIR = path.join(ROOT, 'data');

const RENAME_RETRIES = 3;
const RENAME_RETRY_DELAY_MS = 50;

function resolveSafePath(urlPath) {
    let decoded;
    try {
        decoded = decodeURIComponent(urlPath.split('?')[0]);
    } catch {
        return null; // malformed percent-encoding
    }
    if (decoded.includes('\0')) return null;
    const normalized = path.normalize(path.join(ROOT, decoded));
    if (normalized !== ROOT && !normalized.startsWith(ROOT + path.sep)) return null;
    return normalized;
}

function isInDataDir(filePath) {
    return filePath.startsWith(DATA_DIR + path.sep);
}

function isImage(filePath) {
    return IMAGE_EXTENSIONS.has(path.extname(filePath).toLowerCase());
}

function readBody(req) {
    return new Promise((resolve, reject) => {
        const chunks = [];
        req.on('data', chunk => chunks.push(chunk));
        req.on('end', () => resolve(Buffer.concat(chunks)));
        req.on('error', reject);
    });
}

function send(res, status, body, contentType) {
    res.writeHead(status, {
        'Content-Type': contentType || 'text/plain; charset=utf-8',
        'Content-Length': Buffer.byteLength(body)
    });
    res.end(body);
}

function sendOk(res) {
    send(res, 200, JSON.stringify({ ok: true }), CONTENT_TYPES['.json']);
}

const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));

// Write to a temp file then rename over the target so readers never see a
// half-written file. On Windows the rename can fail with EPERM/EBUSY while the
// target is being read, so retry a few times.
async function atomicWrite(filePath, data) {
    await fsp.mkdir(path.dirname(filePath), { recursive: true });
    const tmpPath = `${filePath}.tmp-${process.pid}-${crypto.randomBytes(4).toString('hex')}`;
    try {
        await fsp.writeFile(tmpPath, data);
        for (let attempt = 1; ; attempt++) {
            try {
                await fsp.rename(tmpPath, filePath);
                return;
            } catch (err) {
                const retryable = err.code === 'EPERM' || err.code === 'EBUSY';
                if (!retryable || attempt >= RENAME_RETRIES) throw err;
                await sleep(RENAME_RETRY_DELAY_MS);
            }
        }
    } catch (err) {
        await fsp.unlink(tmpPath).catch(() => {});
        throw err;
    }
}

async function handlePut(req, res, filePath) {
    if (!isInDataDir(filePath)) {
        send(res, 403, 'Files can only be written under data/');
        return;
    }

    const body = await readBody(req);

    if (isImage(filePath)) {
        if (body.length === 0) {
            send(res, 400, 'Empty image body');
            return;
        }
    } else {
        try {
            JSON.parse(body.toString('utf8')); // validate before touching disk
        } catch (err) {
            send(res, 400, `Invalid JSON body: ${err.message}`);
            return;
        }
    }

    try {
        await atomicWrite(filePath, body);
        console.log(`[local-server] Wrote ${path.relative(ROOT, filePath)} (${body.length} bytes)`);
        sendOk(res);
    } catch (err) {
        console.error(`[local-server] Failed writing ${filePath}:`, err);
        send(res, 500, `Write failed: ${err.message}`);
    }
}

async function handleDelete(res, filePath) {
    // Only image files under data/ can be deleted (never the JSON data files).
    if (!isInDataDir(filePath) || !isImage(filePath)) {
        send(res, 403, 'Only images under data/ can be deleted');
        return;
    }
    try {
        await fsp.unlink(filePath);
        console.log(`[local-server] Deleted ${path.relative(ROOT, filePath)}`);
        sendOk(res);
    } catch (err) {
        if (err.code === 'ENOENT') {
            send(res, 404, 'Not found');
        } else {
            console.error(`[local-server] Failed deleting ${filePath}:`, err);
            send(res, 500, `Delete failed: ${err.message}`);
        }
    }
}

async function handleGet(res, filePath) {
    let stat;
    try {
        stat = await fsp.stat(filePath);
    } catch (err) {
        send(res, err.code === 'ENOENT' ? 404 : 500, err.code === 'ENOENT' ? 'Not found' : 'Read failed');
        return;
    }
    if (!stat.isFile()) {
        send(res, 404, 'Not found');
        return;
    }

    const contentType = CONTENT_TYPES[path.extname(filePath).toLowerCase()] || 'application/octet-stream';
    // These files are rewritten constantly by admin saves; never let the
    // browser (or Tampermonkey's GM_xmlhttpRequest) cache a GET, or a
    // just-deleted/edited meta can reappear on the next refresh.
    res.writeHead(200, {
        'Content-Type': contentType,
        'Content-Length': stat.size,
        'Cache-Control': 'no-store, no-cache, must-revalidate',
        'Pragma': 'no-cache'
    });

    const stream = fs.createReadStream(filePath);
    stream.on('error', err => {
        console.error(`[local-server] Failed reading ${filePath}:`, err);
        res.destroy(err); // headers already sent, abort the connection
    });
    stream.pipe(res);
}

const server = http.createServer(async (req, res) => {
    try {
        // GM_xmlhttpRequest bypasses CORS, but keep permissive headers for
        // convenience if this is ever hit from a plain browser tab too.
        res.setHeader('Access-Control-Allow-Origin', '*');
        res.setHeader('Access-Control-Allow-Methods', 'GET, PUT, DELETE, OPTIONS');
        res.setHeader('Access-Control-Allow-Headers', 'Content-Type');

        if (req.method === 'OPTIONS') {
            res.writeHead(204);
            res.end();
            return;
        }

        const filePath = resolveSafePath(req.url);
        if (!filePath) {
            send(res, 403, 'Forbidden');
            return;
        }

        switch (req.method) {
            case 'PUT': return await handlePut(req, res, filePath);
            case 'GET': return await handleGet(res, filePath);
            case 'DELETE': return await handleDelete(res, filePath);
            default: send(res, 405, 'Method not allowed');
        }
    } catch (err) {
        console.error('[local-server] Unhandled error:', err);
        if (!res.headersSent) send(res, 500, 'Internal error');
        else res.destroy();
    }
});

server.on('error', err => {
    if (err.code === 'EADDRINUSE') {
        console.error(`[local-server] Port ${PORT} is already in use. Stop the other process or run: node local-server.js <port>`);
    } else {
        console.error('[local-server] Server error:', err);
    }
    process.exit(1);
});

server.listen(PORT, () => {
    console.log(`[local-server] Serving ${ROOT} on http://localhost:${PORT}`);
    console.log('[local-server] GET reads files, PUT overwrites them, DELETE removes images under data/ (used by BetterMetas).');
});
