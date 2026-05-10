// Pre-publish sanity for @lelantos-org/circuits.
//
// Asserts every file in the package's `files` whitelist exists, has
// non-zero size in the expected range, and matches the SHA-256 hash
// recorded in `release-manifest.json`. Bumping the manifest is
// intentional — accidental rebuilds (which reroll the trusted-setup
// ceremony) will diff and fail this check before publish.

import { createHash } from "node:crypto";
import { readFile, stat } from "node:fs/promises";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const BUILD = resolve(ROOT, "build");
const MANIFEST_PATH = resolve(ROOT, "release-manifest.json");

/// File spec: path under build/, allowed byte range, optional JSON shape check.
const FILES = [
    {
        name: "2x2.wasm",
        path: resolve(BUILD, "2x2.wasm"),
        minBytes: 4_000_000,
        maxBytes: 6_000_000,
    },
    {
        name: "2x2_final.zkey",
        path: resolve(BUILD, "2x2_final.zkey"),
        minBytes: 40_000_000,
        maxBytes: 50_000_000,
    },
    {
        name: "verification_key.json",
        path: resolve(BUILD, "verification_key.json"),
        minBytes: 1_000,
        maxBytes: 10_000,
        json: (v) => v.protocol === "groth16" && v.curve === "bn128",
    },
];

const manifest = await loadManifest();
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
        const parsed = JSON.parse(bytes.toString("utf8"));
        if (!f.json(parsed)) failures.push(`${f.name}: JSON shape check failed`);
    }
    const sha = createHash("sha256").update(bytes).digest("hex");
    computed[f.name] = sha;
    const expected = manifest?.artifacts?.[f.name];
    if (expected && expected !== sha) {
        failures.push(
            `${f.name}: SHA-256 ${sha} does not match manifest ${expected}. ` +
                `Either an unintentional rebuild (re-run \`just rebuild\` from scratch) ` +
                `or a deliberate ceremony reroll — bump release-manifest.json explicitly.`,
        );
    }
}

if (!manifest) {
    const pkg = JSON.parse(await readFile(resolve(ROOT, "package.json"), "utf8"));
    console.log("[check-artifacts] no release-manifest.json — recording current hashes:");
    console.log(JSON.stringify({ version: pkg.version, artifacts: computed }, null, 2));
    console.log(
        "Write the JSON above to circuits/release-manifest.json and rerun before publishing.",
    );
    process.exit(1);
}

if (failures.length) {
    for (const f of failures) console.error(`✗ ${f}`);
    process.exit(1);
}

console.log("✓ all artifacts present, sized in range, and match release-manifest.json");

async function loadManifest() {
    try {
        return JSON.parse(await readFile(MANIFEST_PATH, "utf8"));
    } catch {
        return null;
    }
}
