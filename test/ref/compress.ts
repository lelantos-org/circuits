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
 * The Fiat-Shamir challenge preimage: every logical public input, in calldata
 * order. Total = 9 + 3·N_IN + 8·N_OUT; 69 at (N_IN, N_OUT) = (4, 6).
 *
 * Superset of `coeffs` below. The four address words, the clue triples and the
 * aux digest are hashed here but never evaluated, which is what binds them
 * without the circuit having to constrain them: change one and `z` moves, so
 * `y` moves, so the proof fails.
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
    );
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

/**
 * TransactCompressN's coefficient vector. Total = 4 + 3·N_IN + 5·N_OUT; 46 at
 * (N_IN, N_OUT) = (4, 6).
 *
 * The strict subset of `flatten` the polynomial is evaluated over: exactly the
 * slots `4x6.circom` pins with a constraint of its own. `PolyEval` is affine in
 * each coefficient and `z` is read by the prover before the witness is chosen,
 * so an unpinned coefficient is one linear equation in one unknown and the
 * compression stops binding anything. `recipient_address`, `chain_id`,
 * `payer_address`, `relayer_address`, `out_aux_digest` and the clue fields carry
 * no circuit constraint, so they are absent here and bound through `flatten`.
 */
export function coeffs(input: FlattenInput): Field[] {
    const nIn = input.nullifier.length;
    const nOut = input.out_cm.length;
    const expected = 4 + 3 * nIn + 5 * nOut;

    // The leading words of the preimage, not a second walk over the same order.
    // `PubInputs.Transact` orders its members so the pinned ones come first
    // precisely so this is a prefix — see `TRANSACT_COEFFS` — and taking it as a
    // slice makes that structural instead of a property two functions have to
    // keep agreeing on. `test/transact/binding.test.ts` asserts the prefix
    // relation against the compiled circuit.
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
 * The order `flattenBatch` emits values in, declared beside it so the names
 * published in `vectors/` and the values they label stay together. The vector
 * generator reads this directly. All `4 + 6·maxL` are coefficients — see
 * `batchCoeffs` for why none is demoted.
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
 * `batchCoeffs` below is the vector the polynomial is evaluated over, and for
 * this shape it is the whole of this one.
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
 * Kept as a separate function from `flattenBatch` rather than an alias. The two
 * answer different questions — "what is hashed into `z`" and "what is evaluated
 * into `y`" — and they are equal here only as a consequence of every word being
 * pinned. Aliasing them would make a future demotion look like a refactor
 * instead of the soundness argument it is.
 *
 * Why nothing is demoted. `4x6.circom` excludes its trailing challenge words
 * because they are not signals of the circuit at all, so no witness copy exists
 * to disagree with calldata. That does not carry over: `leaf_asset`,
 * `leaf_public_in` and `is_deposit` ARE signals of `tree_update_batch.circom`,
 * and hashing a signal into `z` binds nothing, since the prover reads `z` first
 * and may choose a witness that disagrees with the calldata it was hashed from.
 *
 * Why they are genuinely pinned. The gated deposit binding pins
 * `leaf_public_in[k]` and `leaf_asset[k]` against `cv_dep[k]` under discrete-log
 * hardness, but degenerates on its own: `ValueTimesGen(0, gen)` is the curve
 * identity for every `gen`, so at `leaf_public_in[k] === 0` the equality reduces
 * to `cv_dep[k] == rcv[k]·H` and `leaf_asset[k]` retains only a 64-bit range
 * check — and a range check is not a pin. Step 7a of the circuit closes that per
 * slot: on an active deposit leaf, `leaf_asset == 0` exactly when
 * `leaf_public_in == 0`, so a worthless leaf's asset is pinned to a constant and
 * a valued one's is pinned by the binding.
 */
export function batchCoeffs(input: FlattenBatchInput): Field[] {
    // The whole preimage. Kept as its own function, not an alias: the two
    // answer different questions, and a future demotion is written here as a
    // slice with its argument made at the docblock above.
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
