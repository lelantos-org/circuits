// Golden test-vector generator: the cross-repo contract with @lelantos-org/sdk.
//
// This repo owns the circom and therefore the layout. The two repos are held
// together by data rather than shared code: versioned vectors published in the
// npm package and checked by the SDK's own test suite.
//
// Two properties make the vectors a contract rather than a snapshot:
//
//   1. Every `y` is read out of a witness produced by the compiled circuit and
//      compared against the TypeScript Horner evaluation. On disagreement the
//      generator refuses to write. A recorded TS value alone would not detect a
//      circuit change.
//   2. The slot-name layout is read from `lean/expected/layout-<shape>.txt`,
//      the Lean model's dump, rather than regenerated here. The vector file
//      carries Lean's ordering to the SDK.
//
// Determinism is required, since `just vectors-check` diffs a regeneration
// against the committed files: no randomness, no timestamps, no absolute paths.
//
//   just vectors        regenerate
//   just vectors-check  regenerate into a temp dir and diff
//
// Per-shape construction lives in ./vectors/; this file orchestrates and writes.

import * as fs from "node:fs";
import * as path from "node:path";

import { MAX_L } from "../test/lib/constants.js";
import { ROOT, SCHEMA, writeJson } from "./vectors/common.js";
import { TRANSACT_SHAPES, buildTransactVectors } from "./vectors/transact.js";
import { buildBatchVectors } from "./vectors/batch.js";

const outDir = process.argv[2] ? path.resolve(process.argv[2]) : path.join(ROOT, "vectors");

/** What `index.json` records per file, so the SDK can detect a stale checkout. */
interface IndexEntry {
    sha256: string;
    coeffCount: number;
    layoutDigest: string;
}

async function main() {
    fs.mkdirSync(outDir, { recursive: true });

    const files: Record<string, { circuit: { coeffCount: number; layoutDigest: string } }> = {};
    for (const shape of TRANSACT_SHAPES) {
        files[`transact-${shape.id}.json`] = await buildTransactVectors(shape);
    }
    files[`tree-update-batch-${MAX_L}.json`] = await buildBatchVectors();

    const index: Record<string, IndexEntry> = {};
    for (const [name, value] of Object.entries(files)) {
        index[name] = {
            sha256: writeJson(path.join(outDir, name), value),
            coeffCount: value.circuit.coeffCount,
            layoutDigest: value.circuit.layoutDigest,
        };
    }

    // The generator version lives here and NOT in the per-file bodies, so a
    // patch bump does not invalidate every file digest.
    const pkg = JSON.parse(fs.readFileSync(path.join(ROOT, "package.json"), "utf8"));
    writeJson(path.join(outDir, "index.json"), {
        schema: SCHEMA,
        generator: `@lelantos-org/circuits@${pkg.version}`,
        files: index,
    });

    for (const [name, meta] of Object.entries(index)) {
        console.log(`${name}: ${meta.coeffCount} coeffs, layoutDigest ${meta.layoutDigest}`);
    }
    console.log(`wrote ${Object.keys(files).length + 1} files to ${path.relative(ROOT, outDir)}/`);
}

main().catch((e) => {
    console.error(e);
    process.exit(1);
});
