pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/poseidon.circom";
include "tags.circom";

// Note keys, commitments and nullifiers.
//
// Key hierarchy:
//   nsk → ivk = Poseidon(TAG_IVK, nsk) → pk = Poseidon(TAG_PK, ivk)
//       → nk  = Poseidon(TAG_NK, nsk)
// nf = Poseidon(TAG_NF, nk, rho, cm).

template DeriveIvk() {
    signal input nsk;
    signal output ivk;

    component h = Poseidon(2);
    // The tag is hoisted through a `var` rather than assigned straight from the
    // call: the witness-graph builder (`build-circuit`, used to produce the
    // relayer's native witness calculator) cannot store a function result into a
    // signal. Inlining these back breaks `just build-graph`. The R1CS is
    // unaffected either way — the call folds to a constant.
    var tag = TAG_IVK();
    h.inputs[0] <== tag;
    h.inputs[1] <== nsk;
    ivk <== h.out;
}

template DeriveNk() {
    signal input nsk;
    signal output nk;

    component h = Poseidon(2);
    var tag = TAG_NK();
    h.inputs[0] <== tag;
    h.inputs[1] <== nsk;
    nk <== h.out;
}

template DerivePk() {
    signal input ivk;
    signal output pk;

    component h = Poseidon(2);
    var tag = TAG_PK();
    h.inputs[0] <== tag;
    h.inputs[1] <== ivk;
    pk <== h.out;
}

// cm = Poseidon(packed_av, owner_pk, rho, rcm), packed_av = asset_id·2^64 + value.
//
// No leading tag: asset_id != 0 is enforced by the callers, so packed_av >= 2^64
// and cm cannot collide with TAG_MERKLE (5) or TAG_LEAF (10) preimages, whose
// first field element is a small constant.
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

// rho = Poseidon(TAG_RHO, nf0, index) for output notes.
//
// nf0 = nullifier[0] is chain-unique (the contract reverts on double spend) and
// index disambiguates the outputs of one transaction, so no two committed output
// notes can share a rho.
template DeriveRho() {
    signal input nf0;
    signal input index;
    signal output rho;

    component h = Poseidon(3);
    var tag = TAG_RHO();
    h.inputs[0] <== tag;
    h.inputs[1] <== nf0;
    h.inputs[2] <== index;
    rho <== h.out;
}

// nf = Poseidon(TAG_NF, nk, rho, cm)
//
// cm is in the preimage so the nullifier identifies one exact note rather than
// the pair (nk, rho). Without it, two notes sharing a rho share a nullifier and
// spending either permanently locks the other. DeriveRho rules that out for
// transact outputs, but the deposit path (tree_update_batch's cms[]) constrains
// no rho and output rho is publicly derivable from nullifier[0], so a minimal
// deposit could otherwise plant a rho-colliding note in a victim's wallet.
// Binding cm closes this for every inserter.
template Nullifier() {
    signal input nk;
    signal input rho;
    signal input cm;
    signal output nf;

    component h = Poseidon(4);
    var tag = TAG_NF();
    h.inputs[0] <== tag;
    h.inputs[1] <== nk;
    h.inputs[2] <== rho;
    h.inputs[3] <== cm;
    nf <== h.out;
}
