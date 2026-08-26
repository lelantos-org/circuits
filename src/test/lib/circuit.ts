// Wraps circom_tester so every test file resolves the wasm and include paths
// the same way.

import * as path from "path";
import { fileURLToPath } from "url";
// circom_tester ships without TS types
// @ts-ignore
import { wasm as wasmTester } from "circom_tester";

import type { Field } from "../helpers";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const SRC_DIR = path.join(__dirname, "..", "..");
const NODE_MODULES = path.join(SRC_DIR, "..", "node_modules");

export const FIXTURES = path.join(SRC_DIR, "test", "fixtures");

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

// `wasmTester` compiles the circuit into a fresh tmpdir on every call, so the
// cache reduces the cost to one compile per circuit rather than one per suite.
// Mocha does not run with --parallel (see package.json), so all spec files
// share one process and one cache.
//
// Keyed on the absolute path and holding the promise, so concurrent `before`
// hooks for one circuit await a single compile.
const cache = new Map<string, Promise<CircuitTester>>();

/** Load a circuit by absolute path; resolves circom_tester's `include` to node_modules. */
export async function loadCircuit(absPath: string): Promise<CircuitTester> {
    let pending = cache.get(absPath);
    if (pending === undefined) {
        pending = wasmTester(absPath, { include: [NODE_MODULES] }) as Promise<CircuitTester>;
        cache.set(absPath, pending);
    }
    return pending;
}
