// Field and curve constants, transcribed from src/lib/tags.circom.
//
// These are consensus-critical: changing a value invalidates every issued
// proof.

/** A field element. Always a `bigint`; range depends on the field in use. */
export type Field = bigint;

/** A Baby-Jubjub point in affine coordinates. Always plain bigints. */
export type Point = [Field, Field];

/**
 * BN254 scalar field modulus — the Poseidon output range, and the modulus
 * every circuit signal is reduced by.
 */
export const BN254_FR =
    21888242871839275222246405745257275088548364400416034343698204186575808495617n;

/** Baby-Jubjub prime-order subgroup order. */
export const BABYJUB_SUBGROUP_ORDER =
    2736030358979909402780800718157159386076813972158567259200215660948447373041n;

/** `2^64` — the `asset_id` / `value` bound the circuit range-checks. */
export const POW_2_64 = 1n << 64n;

/**
 * Least non-negative residue of `a` mod `p`.
 *
 * JS `%` keeps the sign of the dividend, so a negative intermediate — which
 * Horner evaluation produces — comes back out of range.
 */
export function mod(a: bigint, p: bigint = BN254_FR): bigint {
    const r = a % p;
    return r < 0n ? r + p : r;
}
