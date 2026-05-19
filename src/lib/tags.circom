pragma circom 2.2.3;

// Domain-separation tags. Single source of truth; mirror sdk/src/crypto/tags.ts.
// Changing any value breaks compatibility with prior proofs.
//
// | Tag         | Value | Use                                                       |
// |-------------|-------|-----------------------------------------------------------|
// | TAG_CM      | 1     | Reserved (NoteCommitment uses packed_av instead).         |
// | TAG_NF      | 2     | nf  = Poseidon(TAG_NF, nk, rho)                           |
// | TAG_PK      | 3     | pk  = Poseidon(TAG_PK, ivk)                               |
// | TAG_IVK     | 4     | ivk = Poseidon(TAG_IVK, nsk)                              |
// | TAG_MERKLE  | 5     | node = Poseidon(TAG_MERKLE, c0..c3)                       |
// | TAG_DK      | 6     | dk  = Poseidon(TAG_DK, ivk)  (off-circuit, FMD)           |
// | TAG_ASSET   | 7     | V^t = Pedersen(TAG_ASSET || asset_id_bits)                |
// | TAG_FMD_BIT | 8     | FMD bit derivation, Poseidon(6)                           |
// | TAG_NK      | 9     | nk  = Poseidon(TAG_NK, nsk)                               |
// | TAG_LEAF    | 10    | leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y)         |
//
// TAG_LEAF separates leaf from NoteCommitment: TAG_LEAF=10 vs packed_av≥2^64.
// POW_2_64 = 2^64; packs asset_id||value and bounds RangeCheck64.
function TAG_CM()     { return 1; }
function TAG_NF()     { return 2; }
function TAG_PK()     { return 3; }
function TAG_IVK()    { return 4; }
function TAG_MERKLE() { return 5; }
function TAG_DK()     { return 6; }
function TAG_ASSET()  { return 7; }
function TAG_FMD_BIT(){ return 8; }
function TAG_NK()     { return 9; }
function TAG_LEAF()   { return 10; }

function POW_2_64()   { return 18446744073709551616; }
