pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/poseidon.circom";
include "tags.circom";

// Note keys, commitments and nullifiers.
//
//   nsk → ivk = Poseidon(TAG_IVK, nsk) → pk = Poseidon(TAG_PK, ivk, d)
//       → nk  = Poseidon(TAG_NK, nsk)
//   inner = Poseidon(TAG_INNER, pk, rho, rcm)
//   cm    = Poseidon(TAG_CM, asset_id·2^64 + value, inner), the tree leaf
//   nf    = Poseidon(TAG_NF, nk, rho, cm)

template DeriveIvk() {
    signal input nsk;
    signal output ivk;

    component h = Poseidon(2);
    // Hoisted through a `var`; see tags.circom.
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

// d is the diversifier: one ivk has a distinct pk per d. d is not range-checked;
// for any field element the pk opens only under this ivk.
template DerivePk() {
    signal input ivk;
    signal input d;
    signal output pk;

    component h = Poseidon(3);
    var tag = TAG_PK();
    h.inputs[0] <== tag;
    h.inputs[1] <== ivk;
    h.inputs[2] <== d;
    pk <== h.out;
}

// The half of a note that stays private on every path. A deposit publishes
// `inner` beside its public (asset, value) and tree_update_batch hashes the
// three into the leaf. rcm is the hiding randomness: it alone keeps owner_pk
// out of a published `inner` and (asset, value) out of a spend's published cm,
// since an output's rho is publicly derivable (DeriveRho).
template NoteInner() {
    signal input owner_pk;
    signal input rho;
    signal input rcm;
    signal output inner;

    component h = Poseidon(4);
    var tag = TAG_INNER();
    h.inputs[0] <== tag;
    h.inputs[1] <== owner_pk;
    h.inputs[2] <== rho;
    h.inputs[3] <== rcm;
    inner <== h.out;
}

// Precondition: the caller range-checks asset_id and value to 64 bits. The
// packing asset_id·2^64 + value is injective only under those bounds, which is
// what binds a leaf to one (asset, value). SpentNote and OutputNote check both,
// and tree_update_batch checks both on a deposit leaf.
//
// TAG_CM separates this hash from DerivePk and DeriveRho, the other arity-3
// hashes.
template NoteCommitment() {
    signal input asset_id;
    signal input value;
    signal input inner;
    signal output cm;

    signal packed_av;
    packed_av <== asset_id * POW_2_64() + value;

    component h = Poseidon(3);
    var tag = TAG_CM();
    h.inputs[0] <== tag;
    h.inputs[1] <== packed_av;
    h.inputs[2] <== inner;
    cm <== h.out;
}

// rho = Poseidon(TAG_RHO, nf0, index) for output notes.
//
// nf0 = nullifier[0] is chain-unique, since the contract reverts on double
// spend, and index disambiguates the outputs of one transaction, so no two
// committed output notes share a rho.
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

// cm is in the preimage so the nullifier identifies one note rather than the
// pair (nk, rho). The deposit path does not constrain rho, and an output's rho
// is publicly derivable from nullifier[0], so without cm a deposit could create
// a note sharing another owner's rho and nullifier, and spending either note
// would lock the other.
//
// Two leaves with the same cm (a deposit repeating an earlier
// (asset, value, inner)) still share a nullifier: the second leaf is
// unspendable, at the depositor's cost, and a wallet must count a cm once.
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
