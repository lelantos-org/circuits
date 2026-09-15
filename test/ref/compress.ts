// PolyEval coefficient layouts and the Fiat-Shamir challenge.
//
// Transcribed from src/lib/poly_eval.circom. The same orders appear in
// contracts/src/lib/PubInputs.sol :: compress and in Lelantos.piSlot
// (lean/Lelantos/Circuit/Witness.lean). lean/expected/layout-*.txt pins the Lean
// side; test/formal/layout_parity.test.ts ties it to this module.

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
    intent_hash: Loose;
    out_cv_dep: readonly (readonly Loose[])[];
    out_clue_Rx: readonly Loose[];
    out_clue_Ry: readonly Loose[];
    out_clue_bits: readonly Loose[];
    out_aux_digest: Loose;
}

/**
 * The Fiat-Shamir challenge preimage: every logical public input, in calldata
 * order. Total = 10 + 3·N_IN + 8·N_OUT; 70 at (N_IN, N_OUT) = (4, 6).
 *
 * Superset of `coeffs` below. The five unpinned struct words, the clue triples
 * and the aux digest are hashed here but not evaluated. This binds them without
 * circuit constraints: changing one changes `z`, hence `y`, and the proof fails.
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
    for (const cv of input.out_cv_dep) c.push(big(cv[0]), big(cv[1]));
    c.push(
        big(input.recipient_address),
        big(input.chain_id),
        big(input.payer_address),
        big(input.relayer_address),
        big(input.intent_hash),
    );
    for (let j = 0; j < nOut; j++) {
        c.push(big(input.out_clue_Rx[j]), big(input.out_clue_Ry[j]), big(input.out_clue_bits[j]));
    }
    c.push(big(input.out_aux_digest));

    const expected = 10 + 3 * nIn + 8 * nOut;
    if (c.length !== expected) {
        throw new Error(`flatten: produced ${c.length} coeffs, expected ${expected}`);
    }
    return c;
}

/**
 * TransactCompressN's coefficient vector. Total = 4 + 3·N_IN + 5·N_OUT; 46 at
 * (N_IN, N_OUT) = (4, 6).
 *
 * The strict subset of `flatten` the polynomial is evaluated over: exactly the
 * slots `4x6.circom` pins with a constraint of its own. `PolyEval` is affine in
 * each coefficient and the prover knows `z` before choosing the witness, so an
 * unpinned coefficient is one linear equation in one unknown and the
 * compression binds nothing. `recipient_address`, `chain_id`, `payer_address`,
 * `relayer_address`, `intent_hash`, `out_aux_digest` and the clue fields carry
 * no circuit constraint, so they are absent here and bound through `flatten`.
 */
export function coeffs(input: FlattenInput): Field[] {
    const nIn = input.nullifier.length;
    const nOut = input.out_cm.length;
    const expected = 4 + 3 * nIn + 5 * nOut;

    // The leading words of the preimage. `PubInputs.Transact` orders pinned
    // members first so they form a prefix (see `TRANSACT_COEFFS`); slicing makes
    // the prefix relation structural. `test/transact/binding.test.ts` asserts it
    // against the compiled circuit.
    const c = flatten(input).slice(0, expected);
    if (c.length !== expected) {
        throw new Error(`coeffs: produced ${c.length} coeffs, expected ${expected}`);
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
 * Slot names of the batch challenge preimage, in order.
 *
 * Matches the order `flattenBatch` emits values in, so the names published in
 * `vectors/` label the right values. The vector generator reads this directly.
 * All `4 + 6·maxL` slots are coefficients; see `batchCoeffs`.
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
 * The batch challenge preimage. Total = 4 + 6·MAX_L (52 at MAX_L = 8).
 *
 * Arrays are indexed by leaf slot: a batch commits `actual_count` individual
 * leaves, odd counts included. `batchLayoutNames` above names these slots in
 * the same order; a change to one requires the same change to the other.
 *
 * `batchCoeffs` below is the vector the polynomial is evaluated over; for this
 * shape it equals this preimage.
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
 * BatchCompress's coefficient vector. Total = 4 + 6·MAX_L; 52 at MAX_L = 8.
 *
 * The same words as `flattenBatch`, in the same order: for this shape the
 * coefficient vector and the challenge preimage coincide, because every word is
 * pinned by a constraint of its own.
 *
 * A separate function rather than an alias of `flattenBatch`: one defines what
 * is hashed into `z`, the other what is evaluated into `y`, and they coincide
 * only because every word is pinned. Excluding a word from this vector changes
 * the soundness argument and belongs here.
 *
 * No word is excluded. `4x6.circom` excludes its trailing challenge words
 * because they are not circuit signals, so no witness copy can disagree with
 * calldata. `leaf_asset`, `leaf_public_in` and `is_deposit` are signals of
 * `tree_update_batch.circom`, and hashing a signal into `z` binds nothing: the
 * prover knows `z` first and may choose a witness that disagrees with the
 * calldata it was hashed from.
 *
 * Each word is pinned. The gated deposit binding pins `leaf_public_in[k]` and
 * `leaf_asset[k]` against `cv_dep[k]` under discrete-log hardness, but
 * degenerates alone: `ValueTimesGen(0, gen)` is the curve identity for every
 * `gen`, so at `leaf_public_in[k] === 0` the equality reduces to
 * `cv_dep[k] == rcv[k]·H` and `leaf_asset[k]` is only range-checked to 64 bits,
 * which does not pin it. Step 6a of the circuit covers this per slot: on an
 * active deposit leaf, `leaf_asset == 0` exactly when `leaf_public_in == 0`, so
 * a zero-value leaf's asset is pinned to a constant and a valued leaf's asset is
 * pinned by the binding.
 */
export function batchCoeffs(input: FlattenBatchInput): Field[] {
    // The whole preimage; see the docblock above.
    return flattenBatch(input);
}

/**
 * Horner evaluation y = sum_k c[k]·z^k in BN254 Fr.
 * Mirrors the in-circuit PolyEval and on-chain SnarkCompression.evaluatePolyAtRaw.
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
 * The element order is big-endian, unlike the little-endian encoding used
 * elsewhere in this directory.
 *
 * Exported separately because the circuit does not constrain `z`, so witness
 * generation cannot detect an encoding error. The vectors record this preimage,
 * which localises a mismatch to the encoding.
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
