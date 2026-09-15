// Pre-publish artifact check for @lelantos-org/circuits.
//
// Asserts every published artifact exists, falls within a size band, and, for
// a vkey, parses as the expected JSON shape. Covers the package `files`
// whitelist plus the artifacts published only as GitHub release assets
// (tree_update_batch); `just package` builds both.
//
// The trusted-setup contribution (`snarkjs zkey contribute`) is
// non-deterministic: snarkjs mixes fresh `crypto.randomBytes(64)` into the
// entropy source before applying the user-supplied entropy (see snarkjs
// `getRandomRng`), so zkey and vkey SHA-256 digests differ on every rebuild and
// are not pinned.
//
// Instead, the check prints per-artifact SHA-256 to stdout (one `name=sha` line
// each) plus a `circuits-shas` line that GitHub Actions pipes into
// `$GITHUB_STEP_SUMMARY` and the release notes. It fails only on a missing
// file, an out-of-range size, or a malformed vkey.
//
// stdout is a machine interface: `.github/workflows/publish.yml` greps
// `^<name>=` and `^circuits-shas=`. Keep those two line shapes stable.

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

/// Size bands detect truncated artifacts without pinning a byte count, since
/// each setup run changes the zkey size slightly. zkey size follows the FFT
/// domain and wire count, so the bands must be re-measured when circuit size
/// changes.
const FILES: ArtifactCheck[] = [
    /// 4x6 = `Transact(11, 4, 6)`, the only published transact shape, on ptau-17
    /// at 100,320 constraints (76.5% of the 2^17 domain).
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
        maxBytes: 80_000_000,
    },
    {
        name: "4x6_verification_key.json",
        path: resolve(BUILD, "4x6_verification_key.json"),
        minBytes: 1_000,
        maxBytes: 15_000,
        json: isGroth16Vkey,
    },
];

/** Shared vkey shape assertion for every published verification key. */
function isGroth16Vkey(v: unknown): boolean {
    return isRecord(v) && v.protocol === "groth16" && v.curve === "bn128";
}

/// The golden vectors are byte-deterministic (`scripts/gen-vectors.ts` uses no
/// randomness, timestamps or absolute paths; `just vectors-check` verifies this),
/// so each is pinned to the exact SHA-256 recorded in `vectors/index.json`. A
/// mismatch indicates hand-edited vectors or an uncommitted regeneration.
const VECTORS = resolve(ROOT, "vectors");

/** Narrowing helper for values parsed from JSON. */
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

// Single-line JSON for downstream tooling (GH Actions step output,
// release-body templating, signing tooling).
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
