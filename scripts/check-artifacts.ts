// Pre-publish sanity for @lelantos-org/circuits.
//
// Asserts every published artifact exists, falls within a size band, and, for
// a vkey, parses as the expected JSON shape. Covers the package `files`
// whitelist plus the artifacts published only as GitHub release assets
// (tree_update_batch); `just package` builds both.
//
// The trusted-setup contribution (`snarkjs zkey contribute`) is
// non-deterministic: snarkjs mixes fresh `crypto.randomBytes(64)` into the
// entropy source before applying the user-supplied entropy (see snarkjs
// `getRandomRng`), so the zkey and vkey SHA-256 differ on every rebuild and
// cannot be pinned here.
//
// Instead the gate emits per-artifact SHA-256 to stdout (one `name=sha` line
// each) plus a `circuits-shas` line for GitHub Actions to pipe into
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

/// Size bands are wide by design. The 2x2 circuit produces:
///   - 2x2.wasm                ~3.9 MB  (deterministic from circom)
///   - 2x2_final.zkey          ~22 MB   (tracks the 2^16 FFT domain)
///   - verification_key.json   ~3 KB    (derived from the zkey)
/// A size outside these bands indicates a broken build rather than a new
/// ceremony output.
///
/// zkey size follows the FFT domain and the wire count, not the ceremony
/// randomness, so these are re-measured whenever the circuits change size.
/// Measured at the counts in budget.json: 2x2 / 3x3 / tree_update_batch on
/// ptau-16, 4x4 on ptau-17.
const FILES: ArtifactCheck[] = [
    {
        // The band is a broken-build detector rather than a size budget, so the
        // ceiling carries enough headroom to absorb ordinary circuit growth
        // without failing a healthy build at publish time.
        name: "2x2.wasm",
        path: resolve(BUILD, "2x2.wasm"),
        minBytes: 3_000_000,
        maxBytes: 6_000_000,
    },
    {
        name: "2x2_final.zkey",
        path: resolve(BUILD, "2x2_final.zkey"),
        // Measured 21.7 MB.
        minBytes: 12_000_000,
        maxBytes: 36_000_000,
    },
    {
        name: "verification_key.json",
        path: resolve(BUILD, "verification_key.json"),
        minBytes: 1_000,
        maxBytes: 15_000,
        json: isGroth16Vkey,
    },
    /// 3x3 = `Transact(10, 3, 3)`; see budget.json for its constraint count.
    ///
    /// In the package `files` whitelist since 0.8.0, so SDK consumers can
    /// resolve the 3x3 prover artifacts from npm instead of fetching GitHub
    /// release assets (which needs a token against this private repo). It
    /// still ships as a release asset too — the workflow uploads both.
    ///
    /// Cost of that choice: ~26 MB gzipped added to every install, including
    /// 2x2-only consumers. `tree_update_batch` stays release-asset-only.
    ///
    /// Bands are measured, not scaled from 2x2: wasm size tracks generated
    /// witness code rather than constraint count, so the two shapes' wasm files
    /// are close in size while their zkeys are not.
    {
        name: "3x3.wasm",
        path: resolve(BUILD, "3x3.wasm"),
        minBytes: 2_500_000,
        maxBytes: 6_000_000,
    },
    {
        name: "3x3_final.zkey",
        path: resolve(BUILD, "3x3_final.zkey"),
        // Measured 30.0 MB.
        minBytes: 18_000_000,
        maxBytes: 48_000_000,
    },
    {
        name: "3x3_verification_key.json",
        path: resolve(BUILD, "3x3_verification_key.json"),
        minBytes: 1_000,
        maxBytes: 15_000,
        json: isGroth16Vkey,
    },
    /// 4x4 = `Transact(10, 4, 4)`; see budget.json for its constraint count.
    ///
    /// The one shape built on ptau-17: at 86,680 constraints it does not fit the
    /// 2^16 FFT domain, so its zkey carries a domain twice the size of 3x3's and
    /// lands at ~42 MB against 3x3's ~30 MB even though it has only 1.3x the
    /// constraints. Proving costs roughly twice a 3x3 proof.
    ///
    /// In the package `files` whitelist for the same reason as 3x3 — an SDK
    /// consumer resolves it from npm rather than needing a token for GitHub
    /// release assets — at a further ~37 MB gzipped on every install.
    {
        name: "4x4.wasm",
        path: resolve(BUILD, "4x4.wasm"),
        minBytes: 2_500_000,
        maxBytes: 8_000_000,
    },
    {
        name: "4x4_final.zkey",
        path: resolve(BUILD, "4x4_final.zkey"),
        // Measured 42.5 MB.
        minBytes: 25_000_000,
        maxBytes: 68_000_000,
    },
    {
        name: "4x4_verification_key.json",
        path: resolve(BUILD, "4x4_verification_key.json"),
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
