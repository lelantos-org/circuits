// Pre-publish artifact check for @lelantos-org/circuits.
//
// Asserts each build artifact in the package `files` whitelist (the 4x6 wasm,
// zkey and vkey) exists, falls within a size band and, for the vkey, parses as
// the expected JSON shape; and that each vector listed in `vectors/index.json`
// matches its pinned SHA-256 and layout digest.
//
// zkey and vkey digests are not pinned: `snarkjs zkey contribute` mixes fresh
// randomness into the supplied entropy (snarkjs `getRandomRng`), so they differ
// on every rebuild.
//
// Prints one `name=sha` line per artifact and a single `circuits-shas` JSON
// line; exits non-zero on any failure.

import { createHash } from "node:crypto";
import { readFile, stat } from "node:fs/promises";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const BUILD = resolve(ROOT, "build");

interface ArtifactCheck {
    name: string;
    path: string;
    minBytes: number;
    maxBytes: number;
    /** Optional shape assertion, run only when the file parses as JSON. */
    json?: (value: unknown) => boolean;
}

/// Size bands detect truncated artifacts without pinning a byte count. zkey
/// size follows the FFT domain and wire count, so the bands must be re-measured
/// when circuit size changes.
const FILES: ArtifactCheck[] = [
    /// 4x6 = `Transact(11, 4, 6)` on ptau-16. Measured: the wasm is about
    /// 3.7 MB and the zkey about 33 MB.
    {
        name: "4x6.wasm",
        path: resolve(BUILD, "4x6.wasm"),
        minBytes: 2_500_000,
        maxBytes: 9_000_000,
    },
    {
        name: "4x6_final.zkey",
        path: resolve(BUILD, "4x6_final.zkey"),
        minBytes: 25_000_000,
        maxBytes: 45_000_000,
    },
    {
        name: "4x6_verification_key.json",
        path: resolve(BUILD, "4x6_verification_key.json"),
        minBytes: 1_000,
        maxBytes: 15_000,
        json: isGroth16Vkey,
    },
];

function isGroth16Vkey(v: unknown): boolean {
    return isRecord(v) && v.protocol === "groth16" && v.curve === "bn128";
}

/// The golden vectors are byte-deterministic, so each is pinned to the SHA-256
/// recorded in `vectors/index.json`.
const VECTORS = resolve(ROOT, "vectors");

function isRecord(v: unknown): v is Record<string, unknown> {
    return typeof v === "object" && v !== null;
}

function errMessage(e: unknown): string {
    return e instanceof Error ? e.message : String(e);
}

/** One entry of `vectors/index.json :: files`. */
interface VectorIndexEntry {
    sha256?: string;
    layoutDigest?: string;
}

const computed: Record<string, string> = {};
const failures: string[] = [];

await checkVectors();

for (const f of FILES) {
    const s = await stat(f.path).catch(() => null);
    if (!s) {
        failures.push(`${f.name}: missing — run \`just package\` to rebuild`);
        continue;
    }
    if (s.size < f.minBytes || s.size > f.maxBytes) {
        failures.push(`${f.name}: size ${s.size}B outside [${f.minBytes}, ${f.maxBytes}]`);
    }
    const bytes = await readFile(f.path);
    if (f.json) {
        try {
            const parsed: unknown = JSON.parse(bytes.toString("utf8"));
            if (!f.json(parsed)) failures.push(`${f.name}: JSON shape check failed`);
        } catch (e) {
            failures.push(`${f.name}: invalid JSON (${errMessage(e)})`);
        }
    }
    computed[f.name] = createHash("sha256").update(bytes).digest("hex");
}

if (failures.length) {
    for (const f of failures) console.error(`✗ ${f}`);
    process.exit(1);
}

for (const [name, sha] of Object.entries(computed)) {
    console.log(`${name}=${sha}`);
}

console.log(
    `circuits-shas=${JSON.stringify({
        version: await pkgVersion(),
        artifacts: computed,
    })}`,
);
console.log("✓ all artifacts present, sized in range, and well-formed");

async function checkVectors(): Promise<void> {
    const indexPath = resolve(VECTORS, "index.json");
    const raw = await readFile(indexPath, "utf8").catch(() => null);
    if (raw === null) {
        failures.push("vectors/index.json: missing — run `just vectors`");
        return;
    }
    let index: unknown;
    try {
        index = JSON.parse(raw);
    } catch (e) {
        failures.push(`vectors/index.json: invalid JSON (${errMessage(e)})`);
        return;
    }
    computed["vectors/index.json"] = createHash("sha256").update(raw).digest("hex");

    const files = isRecord(index) && isRecord(index.files) ? index.files : {};
    for (const [name, rawMeta] of Object.entries(files)) {
        const meta: VectorIndexEntry = isRecord(rawMeta) ? (rawMeta as VectorIndexEntry) : {};
        const body = await readFile(resolve(VECTORS, name), "utf8").catch(() => null);
        if (body === null) {
            failures.push(`vectors/${name}: listed in index.json but missing`);
            continue;
        }
        const sha = createHash("sha256").update(body).digest("hex");
        if (sha !== meta.sha256) {
            failures.push(
                `vectors/${name}: sha256 ${sha} != ${meta.sha256} pinned in index.json — ` +
                    "regenerate with `just vectors`",
            );
        }
        let parsed: unknown;
        try {
            parsed = JSON.parse(body);
        } catch (e) {
            failures.push(`vectors/${name}: invalid JSON (${errMessage(e)})`);
            continue;
        }
        const circuit = isRecord(parsed) && isRecord(parsed.circuit) ? parsed.circuit : {};
        const layout = Array.isArray(circuit.layout) ? circuit.layout : undefined;
        if (circuit.layoutDigest !== meta.layoutDigest) {
            failures.push(
                `vectors/${name}: layoutDigest disagrees with index.json — the PI slot ` +
                    "order changed, which requires a new trusted setup",
            );
        }
        if (circuit.coeffCount !== layout?.length) {
            failures.push(
                `vectors/${name}: coeffCount ${circuit.coeffCount} != ` +
                    `${layout?.length} layout slot names`,
            );
        }
        computed[`vectors/${name}`] = sha;
    }
}

async function pkgVersion(): Promise<string> {
    const pkg: unknown = JSON.parse(await readFile(resolve(ROOT, "package.json"), "utf8"));
    return isRecord(pkg) && typeof pkg.version === "string" ? pkg.version : "unknown";
}
