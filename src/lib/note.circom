pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/poseidon.circom";
include "tags.circom";

// Note primitives: key derivation (nsk → ivk → pk, nsk → nk), commitment,
// nullifier. Domain-separation tag values are defined in tags.circom; the
// same constants are mirrored by sdk/src/crypto/tags.ts.
//
// Key hierarchy:
//   nsk  (spend authority, never leaves owner)
//    ├─ ivk = Poseidon(TAG_IVK, nsk)   (incoming view key; can decrypt notes)
//    │    └─ pk  = Poseidon(TAG_PK, ivk)   (owner_pk bound in note commitment)
//    └─ nk  = Poseidon(TAG_NK, nsk)    (nullifier-deriving key; FVK component)
// nf = Poseidon(TAG_NF, nk, rho). Auditor holding nk can recompute nf for
// any known rho (spend detection). Poseidon one-way prevents deriving nsk
// from nk, so spend authority stays gated by nsk via pk_check in
// spent.circom. FMD detection key dk lives off-chain; no circuit
// constraints touch it.

// ivk = Poseidon(TAG_IVK, nsk)
template DeriveIvk() {
    signal input nsk;
    signal output ivk;

    component h = Poseidon(2);
    h.inputs[0] <== TAG_IVK();
    h.inputs[1] <== nsk;
    ivk <== h.out;
}

// nk = Poseidon(TAG_NK, nsk)
template DeriveNk() {
    signal input nsk;
    signal output nk;

    component h = Poseidon(2);
    h.inputs[0] <== TAG_NK();
    h.inputs[1] <== nsk;
    nk <== h.out;
}

// owner_pk = Poseidon(TAG_PK, ivk)
template DerivePk() {
    signal input ivk;
    signal output pk;

    component h = Poseidon(2);
    h.inputs[0] <== TAG_PK();
    h.inputs[1] <== ivk;
    pk <== h.out;
}

// cm = Poseidon(packed_av, owner_pk, rho, rcm)
//   packed_av = asset_id * 2^64 + value
// Domain separation by first-input: NoteCommitment uses packed_av (≥ 2^64
// for any nonzero asset_id), distinguishing it from MerkleLevel4 (TAG_MERKLE)
// and the spend/output leaf hashes (TAG_LEAF).
// Soundness of the packing requires asset_id, value < 2^64; the caller
// range-checks asset_id via HashToAssetGen's Num2Bits(64) and value via
// RangeCheck64.
template NoteCommitment() {
    signal input asset_id;
    signal input value;
    signal input owner_pk;
    signal input rho;
    signal input rcm;
    signal output cm;

    signal packed_av;
    packed_av <== asset_id * POW_2_64() + value;

    component h = Poseidon(4);
    h.inputs[0] <== packed_av;
    h.inputs[1] <== owner_pk;
    h.inputs[2] <== rho;
    h.inputs[3] <== rcm;
    cm <== h.out;
}

// nf = Poseidon(TAG_NF, nk, rho)
template Nullifier() {
    signal input nk;
    signal input rho;
    signal output nf;

    component h = Poseidon(3);
    h.inputs[0] <== TAG_NF();
    h.inputs[1] <== nk;
    h.inputs[2] <== rho;
    nf <== h.out;
}
