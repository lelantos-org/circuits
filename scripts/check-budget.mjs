// Constraint budget gate.
//
// Compiling asserts nothing about circuit size, and `groth16 setup`, where an
// overflow would otherwise surface, does not run in CI.
//
// Two assertions per circuit:
//   domain  hard ceiling; crossing it requires a larger ptau and roughly
//           doubles proving time
//   exact   the count must match budget.json, so a change lands as a reviewable
//           diff
//
// The domain assertion is on the FFT size snarkjs derives, NOT on nConstraints:
//
//   cirPower = log2(nConstraints + nPubInputs + nOutputs + 1 - 1) + 1
//
// with a floor log2 (`snarkjs/build/cli.cjs`). `groth16 setup` therefore accepts
// a circuit iff `nConstraints + nPubInputs + nOutputs <= domain - 1`, so the
// ceiling on nConstraints alone is three lower than `domain` for a circuit with
// one public input and one public output.
//
// Usage: check-budget.mjs [--update]

import { readFileSync, writeFileSync, statSync, readdirSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import * as snarkjs from "snarkjs";

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const BUDGET_FILE = path.join(ROOT, "budget.json");
const COMPILE_HINT = "just compile-4x6 compile-batch";
const NAME_WIDTH = 18;

/**
 * Newest mtime among the .circom sources the production circuits are built
 * from; an artifact older than this is stale.
 *
 * The `test` directory is excluded: fixtures are not inputs to 4x6 or
 * tree_update_batch. The exclusion matches directories only, so a
 * `src/lib/test.circom` still counts.
 */
function newestSourceMtime(dir) {
    let newest = 0;
    for (const entry of readdirSync(dir, { withFileTypes: true })) {
        const full = path.join(dir, entry.name);
        if (entry.isDirectory()) {
            if (entry.name === "test") continue;
            newest = Math.max(newest, newestSourceMtime(full));
        }
        else if (entry.name.endsWith(".circom")) newest = Math.max(newest, statSync(full).mtimeMs);
    }
    return newest;
}

/**
 * Constraint count for one circuit, or an explanation of why it is unusable.
 *
 * Staleness fails rather than triggering a recompile: an .r1cs older than the
 * sources reports counts that do not correspond to the current circuits.
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
    const info = await snarkjs.r1cs.info(file);
    // `sized` is the signal count snarkjs sizes the FFT domain from, not the
    // constraint count; see the header. It is carried alongside so `ceiling`
    // can report the bound in the units budget.json is written in.
    return {
        constraints: info.nConstraints,
        sized: info.nConstraints + info.nPubInputs + info.nOutputs,
    };
}

/**
 * The largest `nConstraints` that still fits `domain`, in the same units as
 * budget.json. `sized - constraints` is the circuit's public-signal overhead,
 * which the FFT size includes and the budget file does not.
 */
function ceiling(constraints, sized, domain) {
    return domain - 1 - (sized - constraints);
}

/** One line per circuit: its constraint count and its distance from the ceiling. */
function describe(name, constraints, sized, domain) {
    const max = ceiling(constraints, sized, domain);
    const pct = ((sized / domain) * 100).toFixed(1);
    return `${name.padEnd(NAME_WIDTH)} ${constraints} — ${max - constraints} under ${max} (${pct}% of ${domain})`;
}

const budget = JSON.parse(readFileSync(BUDGET_FILE, "utf8"));
const sourceMtime = newestSourceMtime(path.join(ROOT, "src"));
const entries = Object.entries(budget.circuits);
const measured = await Promise.all(entries.map(([name]) => measure(name, sourceMtime)));

if (process.argv.includes("--update")) {
    const circuits = {};
    for (const [i, [name, spec]] of entries.entries()) {
        const { constraints, sized, error } = measured[i];
        if (error) {
            console.error(`  ${name.padEnd(NAME_WIDTH)} ${error}`);
            process.exit(1);
        }
        circuits[name] = { ...spec, constraints };
        console.log(`  ${describe(name, constraints, sized, spec.domain)}`);
    }
    writeFileSync(BUDGET_FILE, JSON.stringify({ ...budget, circuits }, null, 2) + "\n");
    console.log("\nbudget.json updated — review the diff");
    process.exit(0);
}

let failed = false;
for (const [i, [name, spec]] of entries.entries()) {
    const { constraints, sized, error } = measured[i];
    const label = name.padEnd(NAME_WIDTH);
    const max = error ? 0 : ceiling(constraints, sized, spec.domain);

    if (error) {
        console.error(`  ${label} ${error}`);
        failed = true;
    } else if (constraints > max) {
        const over = constraints - max;
        console.error(
            `  ${label} ${constraints} EXCEEDS its ${spec.domain} FFT domain by ${over}.\n` +
            `      snarkjs sizes the domain from ${sized} = nConstraints + nPubInputs +\n` +
            `      nOutputs, so the ceiling is ${max} constraints, not ${spec.domain}.\n` +
            `      Needs a larger ptau and roughly doubles proving time.`,
        );
        failed = true;
    } else if (constraints !== spec.constraints) {
        const delta = constraints - spec.constraints;
        console.error(
            `  ${label} ${constraints}, budget says ${spec.constraints} (${delta > 0 ? "+" : ""}${delta}).\n` +
            `      ${max - constraints} from the ${max} ceiling.\n` +
            `      If intended, run \`just budget-update\` and commit budget.json.`,
        );
        failed = true;
    } else {
        console.log(`  ${describe(name, constraints, sized, spec.domain)} ok`);
    }
}

console.log(failed ? "\nconstraint budget FAILED" : "\nconstraint budget ok");
process.exit(failed ? 1 : 0);
