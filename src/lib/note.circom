pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/poseidon.circom";
include "tags.circom";

// Note primitives: key derivation (nsk → ivk → pk), commitment, nullifier.
// Domain-separation tag values come from tags.circom — single source of truth
// shared with merkle.circom and test/helpers.ts.
//
// Key hierarchy:
//   nsk  (spend authority, never leaves owner)
//    └─ ivk = Poseidon(TAG_IVK, nsk)   (incoming view key; can decrypt notes)
//         └─ pk  = Poseidon(TAG_PK, ivk)   (owner_pk bound in note commitment)
// nf still derived from nsk so spend power stays gated by nsk.
// FMD detection key dk is derived off-circuit from ivk (or independently)
// and lives entirely off-chain — no circuit constraints needed for clues.

// ivk = Poseidon(TAG_IVK, nsk)
template DeriveIvk() {
    signal input nsk;
    signal output ivk;

    component h = Poseidon(2);
    h.inputs[0] <== TAG_IVK();
    h.inputs[1] <== nsk;
    ivk <== h.out;
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
// Domain separation by arity: NoteCommitment is the only Poseidon(4) site.
// Soundness of the packing requires asset_id and value < 2^64; the caller
// (transact circuit) range-checks both via AssetEquality+RangeCheck64 on
// public_asset and per-note RangeCheck64 on value.
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

// nf = Poseidon(TAG_NF, nsk, rho)
template Nullifier() {
    signal input nsk;
    signal input rho;
    signal output nf;

    component h = Poseidon(3);
    h.inputs[0] <== TAG_NF();
    h.inputs[1] <== nsk;
    h.inputs[2] <== rho;
    nf <== h.out;
}
