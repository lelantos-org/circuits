// Domain-separation tags, transcribed from src/lib/tags.circom, which is the
// source of truth. Values must equal the `TAG_*()` functions there.
//
// | Tag         | Value | Use                                                |
// |-------------|-------|----------------------------------------------------|
// | TAG_CM      | 1     | reserved; NoteCommitment separates via packed_av    |
// | TAG_NF      | 2     | nf   = Poseidon(TAG_NF, nk, rho, cm)                |
// | TAG_PK      | 3     | pk   = Poseidon(TAG_PK, ivk)                        |
// | TAG_IVK     | 4     | ivk  = Poseidon(TAG_IVK, nsk)                       |
// | TAG_MERKLE  | 5     | node = Poseidon(TAG_MERKLE, c0..c3)                 |
// | TAG_DK      | 6     | dk   = Poseidon(TAG_DK, ivk)         (off-circuit)  |
// | TAG_ASSET   | 7     | V^t  = Pedersen(TAG_ASSET || asset_id_bits)         |
// | TAG_FMD_BIT | 8     | FMD bit derivation, Poseidon(6)      (off-circuit)  |
// | TAG_NK      | 9     | nk   = Poseidon(TAG_NK, nsk)                        |
// | TAG_LEAF    | 10    | leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y)   |
// | TAG_RHO     | 11    | rho  = Poseidon(TAG_RHO, nullifier[0], out_index)   |
//
// 12 (TAG_SUB_TOKEN) and 13 (TAG_FMD_EXPAND) are off-circuit. They are
// deliberately absent from `TAGS`, which mirrors the in-circuit `TAG_*()`
// functions one-for-one; `TAG_FMD_EXPAND` is exported below because the FMD
// reference impl needs it.

export const TAG_CM = 1n;
export const TAG_NF = 2n;
export const TAG_PK = 3n;
export const TAG_IVK = 4n;
export const TAG_MERKLE = 5n;
export const TAG_DK = 6n;
export const TAG_ASSET = 7n;
export const TAG_FMD_BIT = 8n;
export const TAG_NK = 9n;
export const TAG_LEAF = 10n;
export const TAG_RHO = 11n;
export const TAG_FMD_EXPAND = 13n;

/** Tags keyed by circom function name. */
export const TAGS: Record<string, bigint> = {
    TAG_CM,
    TAG_NF,
    TAG_PK,
    TAG_IVK,
    TAG_MERKLE,
    TAG_DK,
    TAG_ASSET,
    TAG_FMD_BIT,
    TAG_NK,
    TAG_LEAF,
    TAG_RHO,
};
