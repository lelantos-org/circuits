// PolyEval coefficient layouts, the coefficient digest and the Fiat-Shamir
// challenge, transcribed from src/lib/poly_eval.circom.
//
// Each circuit exposes three public signals, (y, digest, z): the evaluation of
// its coefficients at z, a Poseidon commitment to those coefficients, and the
// challenge. The contract takes the digest word from calldata, hashes it into z
// after the coefficients, and passes it to the verifier.
//
// The same orders appear in contracts/src/lib/PubInputs.sol :: compress and in
// Lelantos.piSlot (lean/Lelantos/Circuit/Layout.lean).

import { keccak_256 } from "@noble/hashes/sha3";
import { poseidon5 } from "poseidon-lite";
import { BN254_FR, type Field } from "./field.js";
import { toBeBytes32 } from "./bytes.js";
import { TAG_DIGEST } from "./tags.js";

type Loose = string | bigint | number;

const big = (x: Loose): Field => BigInt(x);

/** The circuit signals `TransactCompressN` evaluates and `CoeffDigest` absorbs. */
export interface DigestInput {
    merkle_root: Loose;
    nullifier: readonly Loose[];
    out_cm: readonly Loose[];
    public_asset_id: Loose;
    public_out: Loose;
}

/** The public slots of a transact witness, as `toCircomInput` emits them. */
export interface FlattenInput extends DigestInput {
    /**
     * The coefficient digest as calldata carries it: the word the contract hashes
     * into `z` and the verifier compares against the circuit's digest output.
     */
    digest: Loose;
    recipient_address: Loose;
    chain_id: Loose;
    payer_address: Loose;
    relayer_address: Loose;
    intent_hash: Loose;
    out_clue_Rx: readonly Loose[];
    out_clue_Ry: readonly Loose[];
    out_clue_bits: readonly Loose[];
    out_aux_digest: Loose;
}

/**
 * The coefficients, in order: what `y` evaluates and what the digest absorbs.
 * Total = 3 + N_IN + N_OUT; 13 at (N_IN, N_OUT) = (4, 6).
 */
export function digestPrefix(input: DigestInput): Field[] {
    const c: Field[] = [big(input.merkle_root)];
    for (const nf of input.nullifier) c.push(big(nf));
    for (const cm of input.out_cm) c.push(big(cm));
    c.push(big(input.public_asset_id), big(input.public_out));
    return c;
}

/**
 * Poseidon(5) fold over `words`, four per block, the last block zero-padded:
 *
 *   h_0     = Poseidon(TAG_DIGEST, w[0..3])
 *   h_{b+1} = Poseidon(h_b,        w[4b+4 .. 4b+7])
 *
 * Mirrors CoeffDigest in src/lib/poly_eval.circom.
 */
export function coeffDigest(words: readonly Field[]): Field {
    if (words.length < 1) throw new Error("coeffDigest: need at least one word");
    let h: Field = TAG_DIGEST;
    for (let b = 0; 4 * b < words.length; b++) {
        const block: Field[] = [h];
        for (let i = 0; i < 4; i++) block.push(words[4 * b + i] ?? 0n);
        h = poseidon5(block);
    }
    return h;
}

/** The digest of a transact's coefficients: what an honest prover puts in calldata. */
export function transactDigest(input: DigestInput): Field {
    return coeffDigest(digestPrefix(input));
}

/**
 * The Fiat-Shamir challenge preimage: every logical public input, in calldata
 * order. Total = 10 + N_IN + 4·N_OUT; 38 at (N_IN, N_OUT) = (4, 6).
 *
 * Layout: the coefficients, the digest word, then the words the circuit has no
 * signal for, which are bound by `z` alone. The digest is hashed so that it is
 * fixed before `z`.
 */
export function flatten(input: FlattenInput): Field[] {
    const nIn = input.nullifier.length;
    const nOut = input.out_cm.length;

    if (
        input.out_clue_Rx.length !== nOut ||
        input.out_clue_Ry.length !== nOut ||
        input.out_clue_bits.length !== nOut
    ) {
        throw new Error("flatten: an out_* array length != N_OUT");
    }

    const c: Field[] = digestPrefix(input);
    c.push(big(input.digest));
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

    const expected = 10 + nIn + 4 * nOut;
    if (c.length !== expected) {
        throw new Error(`flatten: produced ${c.length} coeffs, expected ${expected}`);
    }
    return c;
}

/**
 * TransactCompressN's coefficient vector: the leading words of `flatten`.
 * Total = 3 + N_IN + N_OUT; 13 at (N_IN, N_OUT) = (4, 6).
 *
 * `PolyEval` is affine in each coefficient and the prover knows `z` before
 * choosing the witness, so the evaluation binds only because the digest commits
 * the witness's coefficients before `z` is derived.
 */
export function coeffs(input: DigestInput): Field[] {
    return digestPrefix(input);
}

/** The coefficient signals of a TreeUpdateBatch witness. */
export interface BatchCoeffInput {
    old_root: Loose;
    new_root: Loose;
    start_index: Loose;
    actual_count: Loose;
    /** Per slot: the note commitment on a spend leaf, `inner` on a deposit leaf. */
    cms: readonly Loose[];
    leaf_asset: readonly Loose[];
    leaf_public_in: readonly Loose[];
    is_deposit: readonly Loose[];
}

/** The logical public inputs of a TreeUpdateBatch: the coefficients and the digest word. */
export interface FlattenBatchInput extends BatchCoeffInput {
    /** The coefficient digest as calldata carries it; see `FlattenInput.digest`. */
    digest: Loose;
}

/** Slot names of the batch coefficients, in `batchCoeffs` order; published in `vectors/`. */
export function batchLayoutNames(maxL: number): string[] {
    const names = ["oldRoot", "newRoot", "startIndex", "actualCount"];
    for (let k = 0; k < maxL; k++) names.push(`cms ${k}`);
    for (let k = 0; k < maxL; k++) names.push(`leafAsset ${k}`);
    for (let k = 0; k < maxL; k++) names.push(`leafPublicIn ${k}`);
    for (let k = 0; k < maxL; k++) names.push(`isDeposit ${k}`);
    return names;
}

/**
 * BatchCompress's coefficient vector, indexed by leaf slot. Total = 4 + 4·MAX_L;
 * 36 at MAX_L = 8.
 *
 * Every word is a signal of `tree_update_batch.circom`, so every word is
 * evaluated: the prover knows `z` before choosing the witness, so hashing a
 * signal into `z` without evaluating it binds nothing.
 */
export function batchCoeffs(input: BatchCoeffInput): Field[] {
    const maxL = input.cms.length;
    if (
        input.leaf_asset.length !== maxL ||
        input.leaf_public_in.length !== maxL ||
        input.is_deposit.length !== maxL
    ) {
        throw new Error("batchCoeffs: array lengths disagree on MAX_L");
    }

    const c: Field[] = [
        big(input.old_root),
        big(input.new_root),
        big(input.start_index),
        big(input.actual_count),
    ];
    for (const cm of input.cms) c.push(big(cm));
    for (const v of input.leaf_asset) c.push(big(v));
    for (const v of input.leaf_public_in) c.push(big(v));
    for (const v of input.is_deposit) c.push(big(v));

    const expected = 4 + 4 * maxL;
    if (c.length !== expected) {
        throw new Error(`batchCoeffs: produced ${c.length} coeffs, expected ${expected}`);
    }
    return c;
}

/** The digest of a batch's coefficients: what an honest prover puts in calldata. */
export function batchDigest(input: BatchCoeffInput): Field {
    return coeffDigest(batchCoeffs(input));
}

/**
 * The batch challenge preimage: the coefficients, then the digest word.
 * Total = 5 + 4·MAX_L (37 at MAX_L = 8).
 */
export function flattenBatch(input: FlattenBatchInput): Field[] {
    return [...batchCoeffs(input), big(input.digest)];
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
 * Layout: 32-byte offset (0x20) || 32-byte length || N × 32-byte big-endian.
 *
 * The circuit does not constrain `z`, so witness generation cannot detect an
 * encoding error; the vectors record this preimage.
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
