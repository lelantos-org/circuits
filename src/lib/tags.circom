pragma circom 2.2.3;

// Domain separation tags + shared constants. Single source of truth across
// note.circom, merkle.circom, balance.circom and 2x2.circom.
//
// Tag values are baked into hash inputs; changing any constant breaks
// commitment / nullifier / Merkle-node compatibility with prior proofs and
// with test/helpers.ts. Update in lockstep.
//
// | Tag         | Value | Use                                                |
// |-------------|-------|----------------------------------------------------|
// | TAG_CM      | 1     | Reserved (unused; arity-4 + (asset,value) packing  |
// |             |       | already distinguishes NoteCommitment).             |
// | TAG_NF      | 2     | nf  = Poseidon(TAG_NF, nk, rho)         arity 3    |
// | TAG_PK      | 3     | pk  = Poseidon(TAG_PK, ivk)             arity 2    |
// | TAG_IVK     | 4     | ivk = Poseidon(TAG_IVK, nsk)            arity 2    |
// | TAG_MERKLE  | 5     | node = Poseidon(TAG_MERKLE, c0..c3)     arity 5    |
// | TAG_DK      | 6     | dk  = Poseidon(TAG_DK, ivk)  (off-circuit, FMD)    |
// | TAG_ASSET   | 7     | V^t = Pedersen(TAG_ASSET || asset_id_bits)  arity Pedersen(72)
// | TAG_FMD_BIT | 8     | FMD bit derivation, arity-6 Poseidon              |
// | TAG_NK      | 9     | nk  = Poseidon(TAG_NK, nsk)             arity 2    |
//
// TAG_DK is reserved for the wallet-side FMD detection-key derivation
// (`dk = Poseidon(TAG_DK, ivk)`). No template uses it — exposed here purely
// so the SDK and any future audit can pin a single canonical value and avoid
// collision with the in-circuit tags.
//
// TAG_ASSET is prepended (LSB-first byte) to the 64-bit asset_id input of
// `HashToAssetGen` to domain-separate the asset-generator hash from any other
// Pedersen call that might one day share Baby-Jubjub `BASE[0]`.
//
// POW_2_64 = 2^64; used both as the asset/value packing multiplier in
// NoteCommitment and as the bound enforced by RangeCheck64 on private values.
function TAG_CM()     { return 1; }
function TAG_NF()     { return 2; }
function TAG_PK()     { return 3; }
function TAG_IVK()    { return 4; }
function TAG_MERKLE() { return 5; }
function TAG_DK()     { return 6; }
function TAG_ASSET()  { return 7; }
function TAG_FMD_BIT(){ return 8; }
function TAG_NK()     { return 9; }

function POW_2_64()   { return 18446744073709551616; }
