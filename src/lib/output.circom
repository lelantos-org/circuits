pragma circom 2.2.3;

include "note.circom";
include "balance.circom";
include "asset_gen.circom";
include "value_commit.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";

// One output-note slot. Enforces:
//   cm     == NoteCommitment(asset_id, value, pk, rho, rcm)
//   value  < 2^64 and asset_id != 0
//   cv     == ValueCommit(value, HashToAssetGen(asset_id), rcv)
//   cv_dep == ValueCommit(value, HashToAssetGen(asset_id), rcv_dep)
//
// cv_dep feeds leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y) in
// tree_update_batch. rH and cv_dep are exposed to the caller.
template OutputNote() {
    // ---- private witness ----
    signal input asset_id;
    signal input value;
    signal input pk;
    signal input rho;
    signal input rcm;
    signal input rcv;
    signal input rcv_dep;

    // ---- public binding ----
    signal input cm;
    signal input cv[2];

    // ---- exposed to caller ----
    signal output rH[2];
    signal output cv_dep[2];

    // 1. Bind cm.
    component cm_h = NoteCommitment();
    cm_h.asset_id <== asset_id;
    cm_h.value    <== value;
    cm_h.owner_pk <== pk;
    cm_h.rho      <== rho;
    cm_h.rcm      <== rcm;
    cm_h.cm === cm;

    // 2. Range-check value; the bits are shared by both commitments below.
    component rng = RangeCheck64();
    rng.v <== value;

    // 3. asset_id != 0, so packed_av >= 2^64 in NoteCommitment.
    component asset_nz = IsZero();
    asset_nz.in <== asset_id;
    asset_nz.out === 0;

    // 4. Bind cv to (asset_id, value, rcv) and cv_dep to (asset_id, value,
    //    rcv_dep). Same value and generator, so the two commitments differ only
    //    in their blinding and share one scalar mul; see ValueCommitPair.
    component gen = HashToAssetGen();
    gen.asset_id <== asset_id;

    component vc = ValueCommitPair();
    for (var i = 0; i < 64; i++) {
        vc.bits[i] <== rng.bits[i];
    }
    vc.gen[0]  <== gen.gen[0];
    vc.gen[1]  <== gen.gen[1];
    vc.rcv     <== rcv;
    vc.rcv_dep <== rcv_dep;

    cv[0] === vc.cv[0];
    cv[1] === vc.cv[1];

    rH[0] <== vc.rH[0];
    rH[1] <== vc.rH[1];

    cv_dep[0] <== vc.cv_dep[0];
    cv_dep[1] <== vc.cv_dep[1];
}
