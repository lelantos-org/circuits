// Domain-separation tags. Values must equal the `TAG_*()` functions in
// src/lib/tags.circom, the source of truth.
//
// | Tag         | Value | Use                                                |
// |-------------|-------|----------------------------------------------------|
// | TAG_CM      | 1     | cm   = Poseidon(TAG_CM, packed_av, inner)           |
// | TAG_NF      | 2     | nf   = Poseidon(TAG_NF, nk, rho, cm)                |
// | TAG_PK      | 3     | pk   = Poseidon(TAG_PK, ivk, d)                     |
// | TAG_IVK     | 4     | ivk  = Poseidon(TAG_IVK, nsk)                       |
// | TAG_MERKLE  | 5     | node = Poseidon(TAG_MERKLE, c0..c3)                 |
// | TAG_DK      | 6     | dk   = Poseidon(TAG_DK, ivk)         (off-circuit)  |
// | (unused)    | 7     | reserved; do not use                                |
// | TAG_FMD_BIT | 8     | FMD bit derivation, Poseidon(6)      (off-circuit)  |
// | TAG_NK      | 9     | nk   = Poseidon(TAG_NK, nsk)                        |
// | (unused)    | 10    | reserved; do not use                                |
// | TAG_RHO     | 11    | rho  = Poseidon(TAG_RHO, nullifier[0], out_index)   |
// | TAG_INNER   | 14    | inner = Poseidon(TAG_INNER, pk, rho, rcm)           |
// | TAG_DIGEST  | 15    | first block of the coefficient digest, Poseidon(5)  |
//
// 12 (TAG_SUB_TOKEN), 13 (TAG_FMD_EXPAND), 16 (TAG_GD) and 17 (TAG_FMD_EXPAND2)
// are off-circuit and absent from `TAGS`, which mirrors the circom `TAG_*()`
// functions one-for-one.

export const TAG_CM = 1n;
export const TAG_NF = 2n;
export const TAG_PK = 3n;
export const TAG_IVK = 4n;
export const TAG_MERKLE = 5n;
export const TAG_DK = 6n;
export const TAG_FMD_BIT = 8n;
export const TAG_NK = 9n;
export const TAG_RHO = 11n;
export const TAG_FMD_EXPAND = 13n;
export const TAG_INNER = 14n;
export const TAG_DIGEST = 15n;

/** Tags keyed by circom function name. */
export const TAGS: Record<string, bigint> = {
    TAG_CM,
    TAG_NF,
    TAG_PK,
    TAG_IVK,
    TAG_MERKLE,
    TAG_DK,
    TAG_FMD_BIT,
    TAG_NK,
    TAG_RHO,
    TAG_INNER,
    TAG_DIGEST,
};
