// Pre-publish sanity for @lelantos-org/circuits.
//
// Asserts every published artifact exists, falls in a generous size
// band, and (for vkey) parses as the expected JSON shape. That covers
// the package `files` whitelist plus the artifacts published only as
// GitHub release assets (tree_update_batch) — both are built by
// `just package`, so both are worth gating before a release goes out.
//
// The trusted-setup contribution (`snarkjs zkey contribute`) is
// non-deterministic — snarkjs mixes fresh `crypto.randomBytes(64)`
// into the entropy source before applying the user-supplied entropy
// (see snarkjs `getRandomRng`). So the zkey + vkey SHA-256 differ
// across every rebuild. We CANNOT pin them at the gate level without
// either forking snarkjs or committing the zkey to git.
//
// Instead: emit per-artifact SHA-256 to stdout (one `name=sha` line
// each) plus a `circuits-shas` line for GH Actions to pipe into
// `$GITHUB_STEP_SUMMARY` / release notes. Fail only on
// missing-file, out-of-range size, or malformed vkey.
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

/// Size bands are intentionally wide. The 2x2 circuit produces:
///   - 2x2.wasm           ~5 MB (deterministic from circom; ClueCheck removed)
///   - 2x2_final.zkey   ~35–45 MB (depends on ceremony randomness)
///   - verification_key.json ~3 KB (vkey JSON, derived from zkey)
/// Sizes that fall outside these bands indicate a broken build, not a
/// new ceremony output.
const FILES: ArtifactCheck[] = [
    {
        // Ceiling raised 5 MB -> 6 MB: the witness wasm had grown to 5,054,678 B
        // and was tripping the gate on an otherwise healthy build. The band is a
        // broken-build detector, not a size budget — it wants enough headroom to
        // absorb ordinary circuit growth without a false failure at publish time.
        name: "2x2.wasm",
        path: resolve(BUILD, "2x2.wasm"),
        minBytes: 3_000_000,
        maxBytes: 6_000_000,
    },
    {
        name: "2x2_final.zkey",
        path: resolve(BUILD, "2x2_final.zkey"),
        minBytes: 30_000_000,
        maxBytes: 50_000_000,
    },
    {
        name: "verification_key.json",
        path: resolve(BUILD, "verification_key.json"),
        minBytes: 1_000,
        maxBytes: 15_000,
        json: isGroth16Vkey,
    },
    /// 3x3 = `Transact(10, 3, 3)`, ~103k constraints against the same PTAU17.
    ///
    /// In the package `files` whitelist since 0.8.0, so SDK consumers can
    /// resolve the 3x3 prover artifacts from npm instead of fetching GitHub
    /// release assets (which needs a token against this private repo). It
    /// still ships as a release asset too — the workflow uploads both.
    ///
    /// Cost of that choice: ~26 MB gzipped added to every install, including
    /// 2x2-only consumers. `tree_update_batch` stays release-asset-only.
    ///
    /// Bands are measured, not scaled from 2x2: the witness wasm is *smaller*
    /// than 2x2's (wasm size tracks generated witness code, not constraint
    /// count) while the zkey is larger at ~49 MB, which would have tripped a
    /// band copied from the 2x2 entry.
    {
        name: "3x3.wasm",
        path: resolve(BUILD, "3x3.wasm"),
        minBytes: 2_500_000,
        maxBytes: 6_000_000,
    },
    {
        name: "3x3_final.zkey",
        path: resolve(BUILD, "3x3_final.zkey"),
        minBytes: 40_000_000,
        maxBytes: 70_000_000,
    },
    {
        name: "3x3_verification_key.json",
        path: resolve(BUILD, "3x3_verification_key.json"),
        minBytes: 1_000,
        maxBytes: 15_000,
        json: isGroth16Vkey,
    },
];

/** Shared vkey shape assertion for every published verification key. */
function isGroth16Vkey(v: unknown): boolean {
    return isRecord(v) && v.protocol === "groth16" && v.curve === "bn128";
}

/// The golden vectors are the one artifact class here that IS byte-deterministic
/// — `scripts/gen-vectors.ts` uses no randomness, no timestamps and no absolute
/// paths, and `just vectors-check` proves it by regenerating and diffing. So
/// unlike the zkey they get an exact SHA-256 pin, taken from `vectors/index.json`
/// (which the generator writes). A mismatch means the committed vectors were
/// hand-edited or a regeneration was not committed.
const VECTORS = resolve(ROOT, "vectors");

/** Narrowing helper: everything read back from JSON starts life as `unknown`. */
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
