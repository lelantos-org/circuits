pragma circom 2.2.3;

include "note.circom";
include "merkle.circom";
include "balance.circom";
include "asset_gen.circom";
include "value_commit.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";

// One spent-note slot.
//
// is_dummy = 0 enforces the pk check, Merkle membership and asset_id != 0.
// is_dummy = 1 bypasses those; the caller's DummyZeroValue forces value == 0.
//
// Enforced in both cases:
//   nf     == Poseidon(TAG_NF, Poseidon(TAG_NK, nsk), rho, cm)
//   value  < 2^64
//   cv     == ValueCommit(value, HashToAssetGen(asset_id), rcv)
//   cv_dep == ValueCommit(value, HashToAssetGen(asset_id), rcv_dep)
//   leaf   == Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y)
//
// rH is exposed for PerAssetPointBalance.
template SpentNote(DEPTH) {
    // ---- private witness ----
    signal input asset_id;
    signal input value;
    signal input pk;
    signal input rho;
    signal input rcm;
    signal input nsk;
    signal input rcv;
    signal input rcv_dep;
    signal input path_elements[DEPTH][3];
    signal input path_indices[DEPTH];
    signal input is_dummy;

    // ---- public binding ----
    signal input root;
    signal input nullifier;
    signal input cv[2];

    // ---- exposed to caller ----
    signal output rH[2];

    // 1. nsk → ivk → pk.
    component ivk_d = DeriveIvk();
    ivk_d.nsk <== nsk;

    component pk_check = DerivePk();
    pk_check.ivk <== ivk_d.ivk;
    (1 - is_dummy) * (pk_check.pk - pk) === 0;

    // 2. Note commitment.
    component cm = NoteCommitment();
    cm.asset_id <== asset_id;
    cm.value    <== value;
    cm.owner_pk <== pk;
    cm.rho      <== rho;
    cm.rcm      <== rcm;

    // 3. Range-check value; the bits are shared by both commitments below.
    component rng_in = RangeCheck64();
    rng_in.v <== value;

    // 4. cv     = ValueCommit(value, V^asset, rcv)      — bound in step 9.
    //    cv_dep  = ValueCommit(value, V^asset, rcv_dep)  — feeds the leaf below.
    //    Both share one value·V^asset scalar mul; see ValueCommitPair.
    component gen_in = HashToAssetGen();
    gen_in.asset_id <== asset_id;

    component vc = ValueCommitPair();
    for (var i = 0; i < 64; i++) {
        vc.bits[i] <== rng_in.bits[i];
    }
    vc.gen[0]  <== gen_in.gen[0];
    vc.gen[1]  <== gen_in.gen[1];
    vc.rcv     <== rcv;
    vc.rcv_dep <== rcv_dep;

    // 5. leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y). Recomputing the same
    //    leaf that tree_update_batch inserted pins (asset, value) to the note.
    component leaf_h = Poseidon(4);
    // The tag is hoisted through a `var` rather than assigned straight from the
    // call: the witness-graph builder (`build-circuit`, used to produce the
    // relayer's native witness calculator) cannot store a function result into a
    // signal. Inlining these back breaks `just build-graph`. The R1CS is
    // unaffected either way — the call folds to a constant.
    var tag = TAG_LEAF();
    leaf_h.inputs[0] <== tag;
    leaf_h.inputs[1] <== cm.cm;
    leaf_h.inputs[2] <== vc.cv_dep[0];
    leaf_h.inputs[3] <== vc.cv_dep[1];

    // 6. Merkle membership, skipped when is_dummy == 1.
    component mp = MerkleProofOrDummy(DEPTH);
    mp.leaf     <== leaf_h.out;
    mp.root     <== root;
    mp.is_dummy <== is_dummy;
    for (var d = 0; d < DEPTH; d++) {
        mp.path_elements[d][0] <== path_elements[d][0];
        mp.path_elements[d][1] <== path_elements[d][1];
        mp.path_elements[d][2] <== path_elements[d][2];
        mp.path_indices[d]     <== path_indices[d];
    }

    // 7. nf = Poseidon(TAG_NF, Poseidon(TAG_NK, nsk), rho, cm). cm is in the
    //    preimage so a rho collision alone cannot lock a note.
    component nk_d = DeriveNk();
    nk_d.nsk <== nsk;

    component nf_h = Nullifier();
    nf_h.nk  <== nk_d.nk;
    nf_h.rho <== rho;
    nf_h.cm  <== cm.cm;
    nf_h.nf === nullifier;

    // 8. Real notes carry asset_id != 0, so packed_av >= 2^64 in NoteCommitment.
    component asset_nz = IsZero();
    asset_nz.in <== asset_id;
    (1 - is_dummy) * asset_nz.out === 0;

    // 9. Bind cv to (asset_id, value, rcv).
    cv[0] === vc.cv[0];
    cv[1] === vc.cv[1];

    rH[0] <== vc.rH[0];
    rH[1] <== vc.rH[1];
}
