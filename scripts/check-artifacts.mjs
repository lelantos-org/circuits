// Pre-publish sanity for @lelantos-org/circuits.
//
// Asserts every file in the package's `files` whitelist exists, falls
// in a generous size band, and (for vkey) parses as the expected
// JSON shape.
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

import { createHash } from "node:crypto";
import { readFile, stat } from "node:fs/promises";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const BUILD = resolve(ROOT, "build");

/// Size bands are intentionally wide. The 2x2 circuit produces:
///   - 2x2.wasm           ~5 MB (deterministic from circom)
///   - 2x2_final.zkey   ~45–55 MB (depends on ceremony randomness)
///   - verification_key.json ~3 KB (vkey JSON, derived from zkey)
/// Sizes that fall outside these bands indicate a broken build, not a
/// new ceremony output.
const FILES = [
    {
        name: "2x2.wasm",
        path: resolve(BUILD, "2x2.wasm"),
        minBytes: 4_000_000,
        maxBytes: 7_000_000,
    },
    {
        name: "2x2_final.zkey",
        path: resolve(BUILD, "2x2_final.zkey"),
        minBytes: 40_000_000,
        maxBytes: 60_000_000,
    },
    {
        name: "verification_key.json",
        path: resolve(BUILD, "verification_key.json"),
        minBytes: 1_000,
        maxBytes: 15_000,
        json: (v) => v.protocol === "groth16" && v.curve === "bn128",
    },
];

const computed = {};
const failures = [];

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
            const parsed = JSON.parse(bytes.toString("utf8"));
            if (!f.json(parsed)) failures.push(`${f.name}: JSON shape check failed`);
        } catch (e) {
            failures.push(`${f.name}: invalid JSON (${e.message})`);
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

async function pkgVersion() {
    const pkg = JSON.parse(await readFile(resolve(ROOT, "package.json"), "utf8"));
    return pkg.version;
}
