pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/poseidon.circom";
include "tags.circom";

// Key hierarchy:
//   nsk → ivk = Poseidon(TAG_IVK, nsk) → pk = Poseidon(TAG_PK, ivk)
//       → nk  = Poseidon(TAG_NK, nsk)
// nf = Poseidon(TAG_NF, nk, rho).

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

// cm = Poseidon(packed_av, owner_pk, rho, rcm), packed_av = asset_id·2^64 + value.
// packed_av ≥ 2^64 (asset_id ≠ 0) provides domain separation from TAG_MERKLE / TAG_LEAF.
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
