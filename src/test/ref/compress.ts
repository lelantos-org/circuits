// PolyEval coefficient layouts and the Fiat-Shamir challenge.
//
// Transcribed from src/lib/poly_eval.circom. The same orders appear in
// contracts/src/lib/PubInputs.sol :: compress and in Lelantos.piSlot
// (lean/Lelantos/Circuit/Witness.lean). lean/expected/layout-*.txt pins the Lean
// side; src/test/formal/layout_parity.test.ts ties it to this module.

import { keccak_256 } from "@noble/hashes/sha3";
import { BN254_FR, type Field } from "./field.js";
import { toBeBytes32 } from "./bytes.js";

type Loose = string | bigint | number;

const big = (x: Loose): Field => BigInt(x);

/** The public slots of a transact witness, as `toCircomInput` emits them. */
export interface FlattenInput {
    merkle_root: Loose;
    nullifier: readonly Loose[];
    out_cm: readonly Loose[];
    public_asset_id: Loose;
    public_in: Loose;
    public_out: Loose;
    in_cv: readonly (readonly Loose[])[];
    out_cv: readonly (readonly Loose[])[];
    recipient_address: Loose;
    chain_id: Loose;
    payer_address: Loose;
    relayer_address: Loose;
    out_cv_dep: readonly (readonly Loose[])[];
    out_clue_Rx: readonly Loose[];
    out_clue_Ry: readonly Loose[];
    out_clue_bits: readonly Loose[];
    out_aux_digest: Loose;
}

/**
 * TransactCompressN layout. Total = 9 + 3·N_IN + 8·N_OUT (31 at 2x2, 42 at 3x3).
 *
 * Arity is taken from the input array lengths, matching the circom template's
 * genericity over (N_IN, N_OUT).
 */
export function flatten(input: FlattenInput): Field[] {
    const nIn = input.nullifier.length;
    const nOut = input.out_cm.length;

    if (input.in_cv.length !== nIn) throw new Error("flatten: in_cv length != N_IN");
    if (
        input.out_cv.length !== nOut ||
        input.out_cv_dep.length !== nOut ||
        input.out_clue_Rx.length !== nOut ||
        input.out_clue_Ry.length !== nOut ||
        input.out_clue_bits.length !== nOut
    ) {
        throw new Error("flatten: an out_* array length != N_OUT");
    }

    const c: Field[] = [big(input.merkle_root)];
    for (const nf of input.nullifier) c.push(big(nf));
    for (const cm of input.out_cm) c.push(big(cm));
    c.push(big(input.public_asset_id), big(input.public_in), big(input.public_out));
    for (const cv of input.in_cv) c.push(big(cv[0]), big(cv[1]));
    for (const cv of input.out_cv) c.push(big(cv[0]), big(cv[1]));
    c.push(
        big(input.recipient_address),
        big(input.chain_id),
        big(input.payer_address),
        big(input.relayer_address),
    );
    for (const cv of input.out_cv_dep) c.push(big(cv[0]), big(cv[1]));
    for (let j = 0; j < nOut; j++) {
        c.push(big(input.out_clue_Rx[j]), big(input.out_clue_Ry[j]), big(input.out_clue_bits[j]));
    }
    c.push(big(input.out_aux_digest));

    const expected = 9 + 3 * nIn + 8 * nOut;
    if (c.length !== expected) {
        throw new Error(`flatten: produced ${c.length} coeffs, expected ${expected}`);
    }
    return c;
}

/** The public slots of a TreeUpdateBatch witness. */
export interface FlattenBatchInput {
    old_root: Loose;
    new_root: Loose;
    start_index: Loose;
    actual_count: Loose;
    cms: readonly Loose[];
    cv_dep: readonly (readonly Loose[])[];
    leaf_asset: readonly Loose[];
    leaf_public_in: readonly Loose[];
    is_deposit: readonly Loose[];
}

/**
 * Slot names of the BatchCompress layout, in coefficient order.
 *
 * The order `flattenBatch` emits values in, declared beside it so the names
 * published in `vectors/` and the values they label stay together. The vector
 * generator reads this directly.
 */
export function batchLayoutNames(maxL: number): string[] {
    const names = ["oldRoot", "newRoot", "startIndex", "actualCount"];
    for (let k = 0; k < maxL; k++) names.push(`cms ${k}`);
    for (let k = 0; k < maxL; k++) {
        names.push(`cvDepX ${k}`);
        names.push(`cvDepY ${k}`);
    }
    for (let k = 0; k < maxL; k++) names.push(`leafAsset ${k}`);
    for (let k = 0; k < maxL; k++) names.push(`leafPublicIn ${k}`);
    for (let k = 0; k < maxL; k++) names.push(`isDeposit ${k}`);
    return names;
}

/**
 * BatchCompress layout. Total = 4 + 6·MAX_L (28 at MAX_L = 4).
 *
 * Arrays are indexed by leaf slot: a batch commits `actual_count` individual
 * leaves, odd counts included. `batchLayoutNames` above names these slots in
 * the same order; a change to one requires the same change to the other.
 */
export function flattenBatch(input: FlattenBatchInput): Field[] {
    const maxL = input.cms.length;
    if (
        input.cv_dep.length !== maxL ||
        input.leaf_asset.length !== maxL ||
        input.leaf_public_in.length !== maxL ||
        input.is_deposit.length !== maxL
    ) {
        throw new Error("flattenBatch: array lengths disagree on MAX_L");
    }

    const c: Field[] = [
        big(input.old_root),
        big(input.new_root),
        big(input.start_index),
        big(input.actual_count),
    ];
    for (const cm of input.cms) c.push(big(cm));
    for (const p of input.cv_dep) c.push(big(p[0]), big(p[1]));
    for (const v of input.leaf_asset) c.push(big(v));
    for (const v of input.leaf_public_in) c.push(big(v));
    for (const v of input.is_deposit) c.push(big(v));

    const expected = 4 + 6 * maxL;
    if (c.length !== expected) {
        throw new Error(`flattenBatch: produced ${c.length} coeffs, expected ${expected}`);
    }
    return c;
}

/**
 * Horner evaluation y = sum_k c[k]·z^k in BN254 Fr.
 * Mirrors the in-circuit PolyEval and on-chain PubInputs._evalY.
 */
export function hornerEval(coeffs: Field[], z: Field): Field {
    let acc = 0n;
    for (let i = coeffs.length - 1; i >= 0; i--) {
        acc = (acc * z + coeffs[i]) % BN254_FR;
        if (acc < 0n) acc += BN254_FR;
    }
    return acc;
}

/**
 * `abi.encode(uint256[] coeffs)`: the preimage `fiatShamirZ` hashes.
 *
 * Layout: 32-byte offset (0x20) || 32-byte length || N × 32-byte big-endian.
 * Note the big-endian element order, which differs from the little-endian
 * encoding used elsewhere in this directory.
 *
 * Exposed separately because the circuit places no constraint on `z`, so an
 * encoding error is not detectable through witness generation. The vectors
 * record this preimage, which localises a mismatch to the encoding.
 */
export function abiEncodeCoeffs(coeffs: Field[]): Uint8Array {
    const out = new Uint8Array(64 + coeffs.length * 32);
    out.set(toBeBytes32(0x20n), 0);
    out.set(toBeBytes32(BigInt(coeffs.length)), 32);
    for (let i = 0; i < coeffs.length; i++) {
        out.set(toBeBytes32(coeffs[i]), 64 + i * 32);
    }
    return out;
}

export function fiatShamirZ(coeffs: Field[]): Field {
    let v = 0n;
    for (const b of keccak_256(abiEncodeCoeffs(coeffs))) v = (v << 8n) | BigInt(b);
    return v % BN254_FR;
}
