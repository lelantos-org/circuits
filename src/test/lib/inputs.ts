// Plain-JSON input shapers shared by spec + fuzz tests.
//
// These translate the camelCase witness the tests build into the snake_case
// signal names circom reads. circom reads positionally, so the key set is part
// of the contract with the circuit.

import { flattenBatch, type Field, type Point } from "../helpers";

/** Pad a real-slot array out to the circuit's fixed width. */
export function padToSlots<T>(real: T[], total: number, zero: T): T[] {
    const out = real.slice();
    while (out.length < total) out.push(zero);
    return out;
}

export function merkleInputJson(leaf: Field, pathElements: Field[][], pathIndices: number[]) {
    return {
        leaf: leaf.toString(),
        path_elements: pathElements.map(lvl => lvl.map(s => s.toString())),
        path_indices: pathIndices.map(p => p.toString()),
    };
}

/**
 * The PolyEval-bound fields of a TreeUpdateBatch witness — the "logical public
 * inputs". Split out from the rest because the coefficients over these are what
 * derives `z`, so they must be shapeable before `z` exists.
 */
export interface TreeUpdateBatchPublicArgs {
    oldRoot: Field;
    newRoot: Field;
    startIndex: number | bigint;
    actualCount: number | bigint;
    cms: Field[];
    cvDep: Point[];
    leafAsset: Field[];
    leafPublicIn: Field[];
    isDeposit: (number | bigint)[];
}

/** A full batch witness: the public fields above plus the private ones. */
export interface TreeUpdateBatchArgs extends TreeUpdateBatchPublicArgs {
    rcv: Field[];
    frontier: Field[][];
    z: Field;
}

// Consumed twice: `treeUpdateBatchInputJson` spreads the result into the object
// handed to the circuit, and `treeUpdateBatchCoeffs` flattens the same object,
// so the coefficient vector always describes the evaluated witness.
function publicJson(a: TreeUpdateBatchPublicArgs) {
    return {
        old_root: a.oldRoot.toString(),
        new_root: a.newRoot.toString(),
        start_index: a.startIndex.toString(),
        actual_count: a.actualCount.toString(),
        cms: a.cms.map(c => c.toString()),
        cv_dep: a.cvDep.map(p => [p[0].toString(), p[1].toString()]),
        leaf_asset: a.leafAsset.map(v => v.toString()),
        leaf_public_in: a.leafPublicIn.map(v => v.toString()),
        is_deposit: a.isDeposit.map(d => d.toString()),
    };
}

export function treeUpdateBatchInputJson(a: TreeUpdateBatchArgs) {
    return {
        z: a.z.toString(),
        ...publicJson(a),
        rcv: a.rcv.map(r => r.toString()),
        frontier_in: a.frontier.map(lvl => lvl.map(s => s.toString())),
    };
}

/**
 * PolyEval coefficients for a batch witness: 4 + 6·MAX_L of them.
 *
 * The layout is defined once, in `ref/compress.ts :: flattenBatch`, which is
 * also the source `scripts/gen-vectors.ts` publishes vectors from.
 */
export function treeUpdateBatchCoeffs(a: TreeUpdateBatchPublicArgs): Field[] {
    return flattenBatch(publicJson(a));
}
