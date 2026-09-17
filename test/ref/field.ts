// Field and curve constants, transcribed from src/lib/tags.circom.
//
// These are consensus-critical: changing a value invalidates every issued
// proof.

/** A field element. Always a `bigint`; range depends on the field in use. */
export type Field = bigint;

/** A Baby-Jubjub point in affine coordinates. Always plain bigints. */
export type Point = [Field, Field];

/**
 * A point as the pair of decimal strings a circom input object carries.
 *
 * circom reads `signal input p[2]` as a two-element array, so every
 * point-valued input, and every point compared against a witness, goes through
 * this.
 */
export function pointJson(p: Point): string[] {
    return [p[0].toString(), p[1].toString()];
}

/** `pointJson` over an array, for `signal input pts[N][2]`. */
export function pointsJson(pts: readonly Point[]): string[][] {
    return pts.map(pointJson);
}

/**
 * BN254 scalar field modulus — the Poseidon output range, and the modulus
 * every circuit signal is reduced by.
 */
export const BN254_FR =
    21888242871839275222246405745257275088548364400416034343698204186575808495617n;

/** Baby-Jubjub prime-order subgroup order. */
export const BABYJUB_SUBGROUP_ORDER =
    2736030358979909402780800718157159386076813972158567259200215660948447373041n;

/**
 * The Baby-Jubjub identity, `(0, 1)`.
 *
 * Twisted Edwards addition is complete, so the identity is an ordinary point:
 * `ValueScalarMul` returns it at `value = 0` and `MulH` at `rcv = 0`, and
 * `PointSum` treats it as the neutral term that makes padding slots free.
 */
export const EDWARDS_IDENTITY: Point = [0n, 1n];

/** `2^64` — the `asset_id` / `value` bound the circuit range-checks. */
export const POW_2_64 = 1n << 64n;

/**
 * Least non-negative residue of `a` mod `p`.
 *
 * JS `%` keeps the sign of the dividend, so the negative intermediates Horner
 * evaluation produces would otherwise fall out of range.
 */
export function mod(a: bigint, p: bigint = BN254_FR): bigint {
    const r = a % p;
    return r < 0n ? r + p : r;
}
