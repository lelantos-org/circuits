// Plain-JSON input shapers shared by the spec and fuzz suites.
//
// These translate the camelCase witness the tests build into the snake_case
// signal names circom reads. The key set is part of the contract with the
// circuit.

import { batchCoeffs, flattenBatch, pointJson, pointsJson, type Field, type Point } from "../helpers";

/** Pad a real-slot array out to the circuit's fixed width. */
export function padToSlots<T>(real: T[], total: number, zero: T): T[] {
    const out = real.slice();
    while (out.length < total) out.push(zero);
    return out;
}

/** Input for the `PolyEval(N)` fixture. */
export function polyEvalInput(coeffs: Field[], z: Field) {
    return { coeffs: coeffs.map(c => c.toString()), z: z.toString() };
}

/** Little-endian bits of `scalar`, `width` of them: the `FixedBaseMulBits` input. */
export function scalarBits(scalar: Field, width: number | bigint): string[] {
    return Array.from({ length: Number(width) }, (_, i) => ((scalar >> BigInt(i)) & 1n).toString());
}

export function merkleInputJson(leaf: Field, pathElements: Field[][], pathIndices: number[]) {
    return {
        leaf: leaf.toString(),
        path_elements: pathElements.map(lvl => lvl.map(s => s.toString())),
        path_indices: pathIndices.map(p => p.toString()),
    };
}

/**
 * The PolyEval-bound fields of a TreeUpdateBatch witness: the logical public
 * inputs. Separate from the rest because `z` is derived from the coefficients
 * over them, so they must be shapeable before `z` exists.
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

// Consumed three times: `treeUpdateBatchInputJson` spreads the result into the
// object handed to the circuit, `treeUpdateBatchChallenge` flattens it into the
// preimage and `treeUpdateBatchCoeffs` into the coefficient vector. All three
// therefore always describe the same witness.
function publicJson(a: TreeUpdateBatchPublicArgs) {
    return {
        old_root: a.oldRoot.toString(),
        new_root: a.newRoot.toString(),
        start_index: a.startIndex.toString(),
        actual_count: a.actualCount.toString(),
        cms: a.cms.map(c => c.toString()),
        cv_dep: pointsJson(a.cvDep),
        leaf_asset: a.leafAsset.map(v => v.toString()),
        leaf_public_in: a.leafPublicIn.map(v => v.toString()),
        is_deposit: a.isDeposit.map(d => d.toString()),
    };
}

/**
 * The circom input object for TreeUpdateBatch.
 *
 * Key order is contractual: circom resolves signals by name, but this object is
 * serialized into `vectors/` and the SDK pins each file by SHA-256. Reordering
 * these keys breaks the published contract even though the witness is identical.
 */
export function treeUpdateBatchInputJson(a: TreeUpdateBatchArgs) {
    return {
        z: a.z.toString(),
        ...publicJson(a),
        frontier_in: a.frontier.map(lvl => lvl.map(s => s.toString())),
        rcv: a.rcv.map(r => r.toString()),
    };
}

/**
 * Challenge preimage for a batch witness: 4 + 6·MAX_L words, hashed into `z`.
 *
 * The layout is defined in `ref/compress.ts :: flattenBatch`, which is also
 * what `scripts/gen-vectors.ts` publishes vectors from.
 */
export function treeUpdateBatchChallenge(a: TreeUpdateBatchPublicArgs): Field[] {
    return flattenBatch(publicJson(a));
}

/**
 * PolyEval coefficients for a batch witness: 4 + 6·MAX_L words, the same as the
 * preimage, since every word is pinned. `ref/compress.ts :: batchCoeffs`
 * explains why every word is evaluated and which constraints pin them.
 */
export function treeUpdateBatchCoeffs(a: TreeUpdateBatchPublicArgs): Field[] {
    return batchCoeffs(publicJson(a));
}

/**
 * Input for the `PerAssetValueBalance(N_IN, N_OUT)` fixture.
 *
 * The gadget takes plain field elements: no note, no tree, no point
 * arithmetic. Shaped here rather than in the spec file because
 * `fuzz/balance.fuzz.test.ts` draws the same object.
 */
export interface PerAssetBalanceArgs {
    inAsset: Field[];
    inValue: Field[];
    outAsset: Field[];
    outValue: Field[];
    publicAssetId: Field;
    publicIn: Field;
    publicOut: Field;
}

export function perAssetValueBalanceInput(a: PerAssetBalanceArgs) {
    return {
        in_asset: a.inAsset.map(String),
        in_value: a.inValue.map(String),
        out_asset: a.outAsset.map(String),
        out_value: a.outValue.map(String),
        public_asset_id: a.publicAssetId.toString(),
        public_in: a.publicIn.toString(),
        public_out: a.publicOut.toString(),
    };
}

/** Input for the `PerAssetPointBalance(N_IN, N_OUT)` fixture. */
export interface PerAssetPointArgs {
    inCv: Point[];
    outCv: Point[];
    inRH: Point[];
    outRH: Point[];
    pubInPt: Point;
    pubOutPt: Point;
}

export function perAssetPointBalanceInput(a: PerAssetPointArgs) {
    return {
        in_cv: pointsJson(a.inCv),
        out_cv: pointsJson(a.outCv),
        in_rH: pointsJson(a.inRH),
        out_rH: pointsJson(a.outRH),
        pub_in_pt: pointJson(a.pubInPt),
        pub_out_pt: pointJson(a.pubOutPt),
    };
}
