// LAN benchmark server. Serves static UI + 2x2.wasm + 2x2_final.zkey + input.json,
// collects POSTed results into bench/results.json.
//
// Run: npx ts-node bench/server.ts   (default port 8787, override with PORT=)

import { createServer, IncomingMessage, ServerResponse } from "http";
import { createReadStream, existsSync, statSync, appendFileSync, readFileSync } from "fs";
import { resolve, extname, normalize, join } from "path";
import { networkInterfaces } from "os";

const ROOT = resolve(__dirname, "..");
const PUBLIC = resolve(__dirname, "public");
const BUILD = resolve(ROOT, "build");
const WASM = resolve(BUILD, "2x2_js", "2x2.wasm");
const ZKEY = resolve(BUILD, "2x2_final.zkey");
const SNARKJS = resolve(ROOT, "node_modules", "snarkjs", "build", "snarkjs.min.js");
const RESULTS = resolve(__dirname, "results.json");
const PORT = parseInt(process.env.PORT ?? "8787", 10);

const MIME: Record<string, string> = {
    ".html": "text/html; charset=utf-8",
    ".js":   "application/javascript; charset=utf-8",
    ".json": "application/json; charset=utf-8",
    ".css":  "text/css; charset=utf-8",
    ".wasm": "application/wasm",
    ".zkey": "application/octet-stream",
    ".svg":  "image/svg+xml",
};

function send(res: ServerResponse, status: number, body: string, type = "text/plain") {
    res.writeHead(status, { "Content-Type": type, "Access-Control-Allow-Origin": "*" });
    res.end(body);
}

function streamFile(req: IncomingMessage, res: ServerResponse, path: string) {
    if (!existsSync(path)) return send(res, 404, "not found");
    const st = statSync(path);
    const ext = extname(path).toLowerCase();
    res.writeHead(200, {
        "Content-Type": MIME[ext] ?? "application/octet-stream",
        "Content-Length": st.size,
        "Cache-Control": "public, max-age=31536000, immutable",
        "Access-Control-Allow-Origin": "*",
    });
    createReadStream(path).pipe(res);
}

function lanIPs(): string[] {
    const ifs = networkInterfaces();
    const out: string[] = [];
    for (const name of Object.keys(ifs)) {
        for (const a of ifs[name] ?? []) {
            if (a.family === "IPv4" && !a.internal) out.push(a.address);
        }
    }
    return out;
}

async function readBody(req: IncomingMessage): Promise<string> {
    return new Promise((resolve_, reject) => {
        const chunks: Buffer[] = [];
        req.on("data", c => chunks.push(c));
        req.on("end", () => resolve_(Buffer.concat(chunks).toString("utf8")));
        req.on("error", reject);
    });
}

const server = createServer(async (req, res) => {
    const url = new URL(req.url ?? "/", `http://${req.headers.host}`);
    const path = url.pathname;

    if (req.method === "OPTIONS") {
        res.writeHead(204, {
            "Access-Control-Allow-Origin": "*",
            "Access-Control-Allow-Methods": "GET,POST,OPTIONS",
            "Access-Control-Allow-Headers": "Content-Type",
        });
        return res.end();
    }

    if (req.method === "POST" && path === "/result") {
        try {
            const body = await readBody(req);
            const data = JSON.parse(body);
            const record = {
                ts: new Date().toISOString(),
                ip: req.socket.remoteAddress,
                ...data,
            };
            appendFileSync(RESULTS, JSON.stringify(record) + "\n");
            console.log(`result <- ${record.ip} ${record.device ?? ""} mean=${record.meanMs?.toFixed?.(0)}ms`);
            return send(res, 200, JSON.stringify({ ok: true }), "application/json");
        } catch (e: any) {
            return send(res, 400, JSON.stringify({ error: e.message }), "application/json");
        }
    }

    if (req.method === "GET" && path === "/results") {
        if (!existsSync(RESULTS)) return send(res, 200, "[]", "application/json");
        const lines = readFileSync(RESULTS, "utf8").trim().split("\n").filter(Boolean);
        return send(res, 200, "[" + lines.join(",") + "]", "application/json");
    }

    if (req.method !== "GET" && req.method !== "HEAD") return send(res, 405, "method not allowed");

    if (path === "/2x2.wasm") return streamFile(req, res, WASM);
    if (path === "/2x2_final.zkey") return streamFile(req, res, ZKEY);
    if (path === "/snarkjs.min.js") return streamFile(req, res, SNARKJS);

    const rel = path === "/" ? "/index.html" : path;
    const safe = normalize(rel).replace(/^(\.\.[\/\\])+/, "");
    const file = join(PUBLIC, safe);
    if (!file.startsWith(PUBLIC)) return send(res, 403, "forbidden");
    return streamFile(req, res, file);
});

for (const f of [WASM, ZKEY, SNARKJS, join(PUBLIC, "input.json")]) {
    if (!existsSync(f)) console.warn(`WARN: missing ${f}`);
}

server.listen(PORT, "0.0.0.0", () => {
    console.log(`bench server listening on 0.0.0.0:${PORT}`);
    console.log(`local:    http://localhost:${PORT}`);
    for (const ip of lanIPs()) console.log(`lan:      http://${ip}:${PORT}`);
    console.log(`results:  ${RESULTS}`);
});
