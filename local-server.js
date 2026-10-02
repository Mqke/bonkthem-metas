// Minimal dev server for BetterMetas local testing.
// Replaces `npx serve .`: serves files from this directory (GET) and lets the
// Tampermonkey script write data/*.json back to disk (PUT).
//
// Usage: node local-server.js [port]   (default port 3000)

const http = require('http');
const fs = require('fs');
const path = require('path');

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

function resolveSafePath(urlPath) {
    const decoded = decodeURIComponent(urlPath.split('?')[0]);
    const normalized = path.normalize(path.join(ROOT, decoded));
    if (normalized !== ROOT && !normalized.startsWith(ROOT + path.sep)) return null;
    return normalized;
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

async function handlePutImage(req, res, filePath) {
    if (!filePath.startsWith(DATA_DIR + path.sep)) {
        send(res, 403, 'Images can only be written under data/');
        return;
    }
    try {
        const body = await readBody(req);
        if (body.length === 0) {
            send(res, 400, 'Empty image body');
            return;
        }
        fs.mkdirSync(path.dirname(filePath), { recursive: true });
        const tmpPath = `${filePath}.tmp-${process.pid}-${Date.now()}`;
        fs.writeFileSync(tmpPath, body);
        fs.renameSync(tmpPath, filePath);
        console.log(`[local-server] Wrote ${path.relative(ROOT, filePath)} (${body.length} bytes)`);
        send(res, 200, JSON.stringify({ ok: true }), CONTENT_TYPES['.json']);
    } catch (err) {
        console.error(`[local-server] Failed writing ${filePath}:`, err);
        send(res, 500, `Write failed: ${err.message}`);
    }
}

async function handlePut(req, res, filePath) {
    if (IMAGE_EXTENSIONS.has(path.extname(filePath).toLowerCase())) {
        await handlePutImage(req, res, filePath);
        return;
    }

    let text;
    try {
        text = (await readBody(req)).toString('utf8');
        JSON.parse(text); // validate before touching disk
    } catch (err) {
        send(res, 400, `Invalid JSON body: ${err.message}`);
        return;
    }

    try {
        fs.mkdirSync(path.dirname(filePath), { recursive: true });
        const tmpPath = `${filePath}.tmp-${process.pid}-${Date.now()}`;
        fs.writeFileSync(tmpPath, text, 'utf8');
        fs.renameSync(tmpPath, filePath);
        console.log(`[local-server] Wrote ${path.relative(ROOT, filePath)} (${text.length} bytes)`);
        send(res, 200, JSON.stringify({ ok: true }), CONTENT_TYPES['.json']);
    } catch (err) {
        console.error(`[local-server] Failed writing ${filePath}:`, err);
        send(res, 500, `Write failed: ${err.message}`);
    }
}

function handleDelete(res, filePath) {
    // Only image files under data/ can be deleted (never the JSON data files).
    if (!filePath.startsWith(DATA_DIR + path.sep) || !IMAGE_EXTENSIONS.has(path.extname(filePath).toLowerCase())) {
        send(res, 403, 'Only images under data/ can be deleted');
        return;
    }
    fs.unlink(filePath, err => {
        if (err) {
            if (err.code === 'ENOENT') {
                send(res, 404, 'Not found');
            } else {
                console.error(`[local-server] Failed deleting ${filePath}:`, err);
                send(res, 500, `Delete failed: ${err.message}`);
            }
            return;
        }
        console.log(`[local-server] Deleted ${path.relative(ROOT, filePath)}`);
        send(res, 200, JSON.stringify({ ok: true }), CONTENT_TYPES['.json']);
    });
}

function handleGet(res, filePath) {
    fs.readFile(filePath, (err, data) => {
        if (err) {
            send(res, err.code === 'ENOENT' ? 404 : 500, 'Not found');
            return;
        }
        const contentType = CONTENT_TYPES[path.extname(filePath)] || 'application/octet-stream';
        // These files are rewritten constantly by admin saves; never let the
        // browser (or Tampermonkey's GM_xmlhttpRequest) cache a GET, or a
        // just-deleted/edited meta can reappear on the next refresh.
        res.writeHead(200, {
            'Content-Type': contentType,
            'Content-Length': data.length,
            'Cache-Control': 'no-store, no-cache, must-revalidate',
            'Pragma': 'no-cache'
        });
        res.end(data);
    });
}

const server = http.createServer(async (req, res) => {
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

    if (req.method === 'PUT') {
        await handlePut(req, res, filePath);
        return;
    }

    if (req.method === 'GET') {
        handleGet(res, filePath);
        return;
    }

    if (req.method === 'DELETE') {
        handleDelete(res, filePath);
        return;
    }

    send(res, 405, 'Method not allowed');
});

server.listen(PORT, () => {
    console.log(`[local-server] Serving ${ROOT} on http://localhost:${PORT}`);
    console.log('[local-server] GET reads files, PUT overwrites them, DELETE removes images under data/ (used by BetterMetas).');
});
