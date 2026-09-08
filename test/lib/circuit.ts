// Wraps circom_tester so every test file resolves the wasm and include paths
// the same way.

import * as crypto from "crypto";
import * as fs from "fs";
import * as path from "path";
import { promisify } from "util";
import { exec as execCb } from "child_process";
import { fileURLToPath } from "url";
// circom_tester ships without TS types
// @ts-ignore
import { wasm as wasmTester } from "circom_tester";

import type { Field } from "../helpers";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.join(__dirname, "..", "..");
const SRC_DIR = path.join(ROOT, "src");
const NODE_MODULES = path.join(ROOT, "node_modules");

export const FIXTURES = path.join(ROOT, "test", "fixtures");

/**
 * A circom input object: signal name -> value, nested to whatever arity the
 * signal declares (`in_path_elements` is three deep). circom reads
 * positionally, so the key set is part of the contract with the circuit — see
 * the note atop `ref/witness.ts`.
 */
export type CircuitSignal = string | CircuitSignal[];
export type CircuitInput = Record<string, CircuitSignal>;

/**
 * The subset of circom_tester's `wasm` tester this repo uses. circom_tester
 * ships no types; this is a hand-written shim.
 *
 * `calculateWitness` returns the flat witness vector: index 0 is the constant 1,
 * then the circuit outputs in declaration order, then everything else. Read
 * outputs through `readOutput` rather than indexing.
 */
export interface CircuitTester {
    calculateWitness(input: CircuitInput, sanityCheck?: boolean): Promise<bigint[]>;
    checkConstraints(witness: bigint[]): Promise<void>;
    assertOut(witness: bigint[], expected: Record<string, unknown>): Promise<void>;
}

/**
 * Read output signal `index` out of a witness vector.
 *
 * Declared here rather than in `expect.ts` so non-test callers can use it
 * without depending on chai.
 */
export function readOutput(witness: bigint[], index = 0): Field {
    return witness[index + 1];
}

export function srcPath(...parts: string[]): string {
    return path.join(SRC_DIR, ...parts);
}

export function fixturePath(name: string): string {
    return path.join(FIXTURES, name);
}

// `wasmTester` compiles the circuit on every call; the cache reduces that to one
// compile per circuit. Mocha runs without --parallel (see package.json), so all
// spec files share one process and one cache.
//
// The output directory is pinned rather than left to circom_tester's tmpdir,
// because that compile already emits the `.r1cs` and `.sym` the R1CS-level
// suites need (`lib/r1cs.ts`) and a tmpdir would hide them behind a second
// ~100k-constraint compile. It lives under `build/`, which is gitignored.
//
// Keyed on the absolute path and holding the promise, so concurrent `before`
// hooks for one circuit await a single compile.
const TESTER_OUT = path.join(ROOT, "build", ".tester");

const cache = new Map<string, Promise<CircuitArtifacts>>();

/**
 * A compiled circuit: the wasm tester the witness suites drive, plus the paths
 * to the constraint system behind it.
 *
 * The two must come from the SAME compile. A suite that mutates a witness and
 * asks whether the R1CS still accepts it is comparing artifacts against each
 * other, so a stale `.r1cs` beside a fresh wasm would not fail loudly — it would
 * quietly answer questions about a circuit that is no longer in `src/`.
 */
export interface CircuitArtifacts {
    tester: CircuitTester;
    /** `<name>.r1cs` — what a Groth16 proof actually binds. */
    r1csPath: string;
    /** `<name>.sym` — witness index -> signal name. */
    symPath: string;
}

/** Per-circuit output directory: basename plus a hash, so two fixtures that
 *  share a basename cannot collide. */
function outputDirFor(absPath: string): string {
    const tag = crypto.createHash("sha256").update(absPath).digest("hex").slice(0, 8);
    return path.join(TESTER_OUT, `${path.basename(absPath, ".circom")}-${tag}`);
}

/**
 * Compile a circuit (once per process) and return its artifacts.
 *
 * Resolves circom_tester's `include` to node_modules, the same way for every
 * suite.
 */
export async function loadCircuitArtifacts(absPath: string): Promise<CircuitArtifacts> {
    let pending = cache.get(absPath);
    if (pending === undefined) {
        pending = (async () => {
            const output = outputDirFor(absPath);
            await fs.promises.mkdir(output, { recursive: true });
            const tester = (await wasmTester(absPath, {
                include: [NODE_MODULES],
                output,
            })) as CircuitTester;
            const base = path.basename(absPath, ".circom");
            return {
                tester,
                r1csPath: path.join(output, `${base}.r1cs`),
                symPath: path.join(output, `${base}.sym`),
            };
        })();
        cache.set(absPath, pending);
    }
    return pending;
}

/** Load a circuit by absolute path; resolves circom_tester's `include` to node_modules. */
export async function loadCircuit(absPath: string): Promise<CircuitTester> {
    return (await loadCircuitArtifacts(absPath)).tester;
}

// ===== unoptimized constraint systems =====

const exec = promisify(execCb);

/**
 * Compile a circuit to `.r1cs` and `.sym` only, with circom's optimizer off.
 *
 * `loadCircuitArtifacts` above compiles at circom's default `--O2`, which is the
 * system a proof actually binds and therefore the one to sweep for a second
 * witness. But `--O2` substitutes linear constraints away, and a bit
 * decomposition is exactly a linear constraint: after optimization the weighted
 * sum `sum 2^i b_i === in` is gone, its bits folded into whatever consumed them.
 * In `4x6` no linear combination survives with more than two power-of-two
 * coefficients, so a structural search for decompositions finds nothing at all
 * there.
 *
 * `--O0` keeps them, which is why `just picus` also compiles its own `--O0`
 * copy. Reasoning about aliasing on the `--O0` system is sound for the deployed
 * one: the optimizer's substitutions preserve the solution set, so a
 * decomposition wide enough to alias at `--O0` still aliases at `--O2`, only
 * spelled differently.
 *
 * No wasm is emitted — the caller wants the constraint system, and skipping it
 * keeps this near a second even for `4x6`.
 */
export async function compileConstraintsOnly(
    absPath: string,
): Promise<{ r1csPath: string; symPath: string }> {
    const base = path.basename(absPath, ".circom");
    const output = path.join(outputDirFor(absPath), "O0");
    const paths = {
        r1csPath: path.join(output, `${base}.r1cs`),
        symPath: path.join(output, `${base}.sym`),
    };

    let pending = o0Cache.get(absPath);
    if (pending === undefined) {
        pending = (async () => {
            await fs.promises.mkdir(output, { recursive: true });
            await exec(
                `circom ${JSON.stringify(absPath)} --r1cs --sym --O0 ` +
                    `-o ${JSON.stringify(output)} -l ${JSON.stringify(NODE_MODULES)}`,
            );
            return paths;
        })();
        o0Cache.set(absPath, pending);
    }
    return pending;
}

const o0Cache = new Map<string, Promise<{ r1csPath: string; symPath: string }>>();
