// Shared wiring for the `tree_update_batch.circom` suites: the compiled circuit,
// a `BatchBuilder`, and the three assertions every batch case ends in.
//
// The suites in this directory cover:
//   - `shapes`           honest batches: counts, odd counts, deposit/spend mixes,
//                        start positions straddling every level, capacity
//   - `deposit_binding`  the leaf a deposit slot builds from its public amount,
//                        the two range checks, and what is_deposit selects
//   - `frontier`         both roots and the frontier they are rebuilt from
//   - `padding`          inactive-slot zeroing, spend-leaf zeroing, count bounds
//   - `divergent`        a witness that disagrees with the calldata it is proved
//                        against
//
// actual_count is a leaf count, so a batch may commit an odd number of leaves.
// Most cases use a small actual_count for runtime; the larger ones cover the
// multiplex logic.
//
// The witness builders live in `lib/batch.ts`, shared with the fuzz suites.
// `loadCircuit` memoizes, so all suites together cost one compile.

import { srcPath, type CircuitTester } from "../lib/circuit";
import { BatchBuilder, type BatchWitness } from "../lib/batch";
import { treeUpdateBatchInputJson } from "../lib/inputs";
import { expectNotForgeable, expectWitnessFails, expectWitnessPublic } from "../lib/expect";
import { pendingCtx, useCircuit, type CircuitCtx } from "../lib/harness";
import { ARITY, BATCH_DEPTH } from "../lib/constants";

export const CIRCUIT = srcPath("tree_update_batch.circom");

/** Leaf capacity of the batch circuit's tree: 4^11. */
export const CAPACITY = ARITY ** BATCH_DEPTH;

export interface BatchCtx extends CircuitCtx {
    /** Populated by `before`; reading it earlier throws, see `pendingCtx`. */
    batch: BatchBuilder;
}

/**
 * Register the `before` hook and return the context object it populates.
 *
 * Returns a stable object rather than the values themselves, so callers
 * destructure at test time (`const { batch, circuit } = ctx`).
 */
export function useBatchCircuit(): BatchCtx {
    const ctx = useCircuit(CIRCUIT) as BatchCtx;
    // `batch` is added here rather than by `useCircuit`, so it needs the same
    // read-before-hook guard the inherited fields get.
    Object.defineProperties(ctx, Object.getOwnPropertyDescriptors(
        pendingCtx<Pick<BatchCtx, "batch">>(["batch"], "useBatchCircuit"),
    ));
    before(() => {
        ctx.batch = new BatchBuilder(ctx.P);
    });
    return ctx;
}

/**
 * Every constraint holds, and the circuit's two outputs equal the reference
 * `w.y` and the calldata digest `w.digest`.
 */
export function expectBatchAccepts(circuit: CircuitTester, w: BatchWitness): Promise<bigint[]> {
    return expectWitnessPublic(circuit, treeUpdateBatchInputJson(w), w);
}

/** A constraint rejects `w`; `message` names the one expected to. */
export function expectBatchRejects(circuit: CircuitTester, w: BatchWitness, message: string): Promise<void> {
    return expectWitnessFails(circuit, treeUpdateBatchInputJson(w), message);
}

/**
 * `w` was bound to a divergent calldata view (`bindFiatShamir`), and the circuit
 * must not attest to it; see `expectNotForgeable`.
 */
export function expectBatchNotForgeable(circuit: CircuitTester, w: BatchWitness, field: string): Promise<void> {
    return expectNotForgeable(circuit, treeUpdateBatchInputJson(w), w, field);
}
