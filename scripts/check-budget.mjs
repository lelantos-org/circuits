// Constraint budget gate.
//
// Compiling asserts nothing about circuit size, and `groth16 setup` — where an
// overflow would otherwise surface — does not run in CI. Transact(10,3,3)
// clears the 2^16 FFT domain by 13 constraints, so the count needs its own gate.
//
// Two assertions per circuit:
//   domain  hard ceiling; crossing it requires a larger ptau and roughly
//           doubles proving time
//   exact   the count must match budget.json, so a change lands as a reviewable
//           diff rather than drifting silently
//
// Usage: check-budget.mjs [--update]

import { readFileSync, writeFileSync, statSync, readdirSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import * as snarkjs from "snarkjs";

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const BUDGET_FILE = path.join(ROOT, "budget.json");
const COMPILE_HINT = "just compile compile-3x3 compile-4x4 compile-batch";
const NAME_WIDTH = 18;

/**
 * Newest mtime among the .circom sources the production circuits are built
 * from; an artifact older than this is stale.
 *
 * `test/` is excluded: fixtures are not inputs to 2x2 / 3x3 / 4x4 /
 * tree_update_batch, and counting them would fail the gate on every added test.
 */
function newestSourceMtime(dir) {
    let newest = 0;
    for (const entry of readdirSync(dir, { withFileTypes: true })) {
        if (entry.name === "test") continue;
        const full = path.join(dir, entry.name);
        if (entry.isDirectory()) newest = Math.max(newest, newestSourceMtime(full));
        else if (entry.name.endsWith(".circom")) newest = Math.max(newest, statSync(full).mtimeMs);
    }
    return newest;
}

/**
 * Constraint count for one circuit, or an explanation of why it is unusable.
 *
 * Staleness fails rather than triggering a recompile: reading an .r1cs older
 * than the sources would report the previous commit's counts as a pass.
 */
async function measure(name, sourceMtime) {
    const file = path.join(ROOT, "build", `${name}.r1cs`);
    const rel = path.relative(ROOT, file);

    let stat;
    try {
        stat = statSync(file);
    } catch {
        return { error: `${rel} missing — run \`${COMPILE_HINT}\`` };
    }
    if (stat.mtimeMs < sourceMtime) {
        return { error: `${rel} is older than src/**.circom — stale; run \`${COMPILE_HINT}\`` };
    }
    return { constraints: (await snarkjs.r1cs.info(file)).nConstraints };
}

/** One line per circuit: what it is, and how close to the ceiling. */
function describe(name, constraints, domain) {
    const pct = ((constraints / domain) * 100).toFixed(1);
    return `${name.padEnd(NAME_WIDTH)} ${constraints} — ${domain - constraints} under ${domain} (${pct}%)`;
}

const budget = JSON.parse(readFileSync(BUDGET_FILE, "utf8"));
const sourceMtime = newestSourceMtime(path.join(ROOT, "src"));
const entries = Object.entries(budget.circuits);
const measured = await Promise.all(entries.map(([name]) => measure(name, sourceMtime)));

if (process.argv.includes("--update")) {
    const circuits = {};
    for (const [i, [name, spec]] of entries.entries()) {
        const { constraints, error } = measured[i];
        if (error) {
            console.error(`  ${name.padEnd(NAME_WIDTH)} ${error}`);
            process.exit(1);
        }
        circuits[name] = { ...spec, constraints };
        console.log(`  ${describe(name, constraints, spec.domain)}`);
    }
    writeFileSync(BUDGET_FILE, JSON.stringify({ ...budget, circuits }, null, 2) + "\n");
    console.log("\nbudget.json updated — review the diff");
    process.exit(0);
}

let failed = false;
for (const [i, [name, spec]] of entries.entries()) {
    const { constraints, error } = measured[i];
    const label = name.padEnd(NAME_WIDTH);

    if (error) {
        console.error(`  ${label} ${error}`);
        failed = true;
    } else if (constraints > spec.domain) {
        const over = constraints - spec.domain;
        console.error(
            `  ${label} ${constraints} EXCEEDS its ${spec.domain} FFT domain by ${over}.\n` +
            `      Needs a larger ptau and roughly doubles proving time.`,
        );
        failed = true;
    } else if (constraints !== spec.constraints) {
        const delta = constraints - spec.constraints;
        console.error(
            `  ${label} ${constraints}, budget says ${spec.constraints} (${delta > 0 ? "+" : ""}${delta}).\n` +
            `      ${spec.domain - constraints} from the ${spec.domain} ceiling.\n` +
            `      If intended, run \`just budget-update\` and commit budget.json.`,
        );
        failed = true;
    } else {
        console.log(`  ${describe(name, constraints, spec.domain)} ok`);
    }
}

console.log(failed ? "\nconstraint budget FAILED" : "\nconstraint budget ok");
process.exit(failed ? 1 : 0);
