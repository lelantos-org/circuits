pragma circom 2.2.3;

// Domain-separation tags. Must stay in sync with sdk/src/crypto/tags.ts;
// changing a value invalidates every previously issued proof.
//
// | Tag         | Value | Use                                                  |
// |-------------|-------|------------------------------------------------------|
// | TAG_CM      | 1     | Reserved; NoteCommitment separates via packed_av.     |
// | TAG_NF      | 2     | nf   = Poseidon(TAG_NF, nk, rho, cm)                  |
// | TAG_PK      | 3     | pk   = Poseidon(TAG_PK, ivk)                          |
// | TAG_IVK     | 4     | ivk  = Poseidon(TAG_IVK, nsk)                         |
// | TAG_MERKLE  | 5     | node = Poseidon(TAG_MERKLE, c0..c3)                   |
// | TAG_DK      | 6     | dk   = Poseidon(TAG_DK, ivk)          (off-circuit)   |
// | TAG_ASSET   | 7     | V^t  = Pedersen(TAG_ASSET || asset_id_bits)           |
// | TAG_FMD_BIT | 8     | FMD bit derivation, Poseidon(6)       (off-circuit)   |
// | TAG_NK      | 9     | nk   = Poseidon(TAG_NK, nsk)                          |
// | TAG_LEAF    | 10    | leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y)     |
// | TAG_RHO     | 11    | rho  = Poseidon(TAG_RHO, nullifier[0], out_index)     |
//
// Reserved off-circuit, defined only in sdk/src/crypto/tags.ts. Listed here so
// the value space stays single-sourced and a new in-circuit tag cannot collide:
// | TAG_SUB_TOKEN  | 12 | sub token = Poseidon(TAG_SUB_TOKEN, ivk, epoch)      |
// | TAG_FMD_EXPAND | 13 | h_i       = Poseidon(TAG_FMD_EXPAND, ck_x, ck_y, i)  |
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
function TAG_RHO()    { return 11; }

// 2^64 — the shift used to pack asset_id||value in NoteCommitment.
function POW_2_64()   { return 18446744073709551616; }
