// Plain-JSON input shapers shared by the spec and fuzz suites: they translate
// the camelCase witness the tests build into the snake_case signal names circom
// reads.

import { batchCoeffs, batchDigest, flattenBatch, type Field } from "../helpers";

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

export function merkleInputJson(leaf: Field, pathElements: Field[][], pathIndices: number[]) {
    return {
        leaf: leaf.toString(),
        path_elements: pathElements.map(lvl => lvl.map(s => s.toString())),
        path_indices: pathIndices.map(p => p.toString()),
    };
}

/**
 * The logical public inputs of a TreeUpdateBatch: its coefficients and the
 * calldata digest word. `z` is derived from them.
 */
export interface TreeUpdateBatchPublicArgs {
    oldRoot: Field;
    newRoot: Field;
    startIndex: number | bigint;
    actualCount: number | bigint;
    /** Per slot: the note commitment on a spend leaf, `inner` on a deposit leaf. */
    cms: Field[];
    leafAsset: Field[];
    leafPublicIn: Field[];
    isDeposit: (number | bigint)[];
    /**
     * The coefficient digest as calldata carries it: hashed into `z` and passed
     * to the verifier. Not a circuit input; the circuit outputs its own.
     */
    digest: Field;
}

/** A full batch witness: the public fields above plus the private ones. */
export interface TreeUpdateBatchArgs extends TreeUpdateBatchPublicArgs {
    frontier: Field[][];
    z: Field;
}

// Shared by the circuit input, the challenge preimage and the coefficient
// vector, so all three describe the same witness. The digest word is absent: it
// is not an input signal.
function publicJson(a: Omit<TreeUpdateBatchPublicArgs, "digest">) {
    return {
        old_root: a.oldRoot.toString(),
        new_root: a.newRoot.toString(),
        start_index: a.startIndex.toString(),
        actual_count: a.actualCount.toString(),
        cms: a.cms.map(c => c.toString()),
        leaf_asset: a.leafAsset.map(v => v.toString()),
        leaf_public_in: a.leafPublicIn.map(v => v.toString()),
        is_deposit: a.isDeposit.map(d => d.toString()),
    };
}

/**
 * The circom input object for TreeUpdateBatch.
 *
 * Key order is contractual: this object is serialized into `vectors/` and the
 * SDK pins each file by SHA-256.
 */
export function treeUpdateBatchInputJson(a: TreeUpdateBatchArgs) {
    return {
        z: a.z.toString(),
        ...publicJson(a),
        frontier_in: a.frontier.map(lvl => lvl.map(s => s.toString())),
    };
}

/**
 * Challenge preimage for a batch witness: the 4 + 4·MAX_L coefficients, then
 * the digest word, hashed into `z`. The layout is defined in
 * `ref/compress.ts :: flattenBatch`.
 */
export function treeUpdateBatchChallenge(a: TreeUpdateBatchPublicArgs): Field[] {
    return flattenBatch({ ...publicJson(a), digest: a.digest });
}

/** The digest of a batch witness's own coefficients: what an honest prover submits. */
export function treeUpdateBatchDigest(a: Omit<TreeUpdateBatchPublicArgs, "digest">): Field {
    return batchDigest(publicJson(a));
}

/**
 * PolyEval coefficients for a batch witness: 4 + 4·MAX_L words, the preimage
 * without its digest word.
 */
export function treeUpdateBatchCoeffs(a: TreeUpdateBatchPublicArgs): Field[] {
    return batchCoeffs(publicJson(a));
}

/** Input for the `PerAssetValueBalance(N_IN, N_OUT)` fixture: plain field elements. */
export interface PerAssetBalanceArgs {
    inAsset: Field[];
    inValue: Field[];
    outAsset: Field[];
    outValue: Field[];
    publicAssetId: Field;
    publicOut: Field;
}

export function perAssetValueBalanceInput(a: PerAssetBalanceArgs) {
    return {
        in_asset: a.inAsset.map(String),
        in_value: a.inValue.map(String),
        out_asset: a.outAsset.map(String),
        out_value: a.outValue.map(String),
        public_asset_id: a.publicAssetId.toString(),
        public_out: a.publicOut.toString(),
    };
}
