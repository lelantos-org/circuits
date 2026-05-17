pragma circom 2.2.3;

include "note.circom";
include "balance.circom";
include "asset_gen.circom";
include "value_commit.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";

// OutputNote: constraints for ONE output-note slot.
//   - cm == NoteCommitment(asset_id, value, pk, rho, rcm)  (always real;
//     padding = value=0 notes to self).
//   - value < 2^64.
//   - asset_id != 0 (ghost-note defense, no dummy bypass).
//   - cv     == ValueCommit(value, HashToAssetGen(asset_id), rcv).
//   - cv_dep == ValueCommit(value, HashToAssetGen(asset_id), rcv_dep).
//     Anchored into leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y), so a
//     future spend cannot reopen under different (asset_id, value).
//
// rH exposed for PerAssetPointBalance. cv_dep exposed so caller can pin it via
// PolyEval and forward to tree_update_batch for leaf-format binding.
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

    // ---- exposed for caller ----
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

    // 2. Range-check value; bits threaded into both ValueCommits.
    component rng = RangeCheck64();
    rng.v <== value;

    // 3. asset_id != 0 (ghost-note defense).
    component asset_nz = IsZero();
    asset_nz.in <== asset_id;
    asset_nz.out === 0;

    // 4. Bind cv to (asset_id, value, rcv).
    component gen = HashToAssetGen();
    gen.asset_id <== asset_id;

    component vc = ValueCommit();
    for (var i = 0; i < 64; i++) {
        vc.bits[i] <== rng.bits[i];
    }
    vc.gen[0] <== gen.gen[0];
    vc.gen[1] <== gen.gen[1];
    vc.rcv    <== rcv;

    cv[0] === vc.cv[0];
    cv[1] === vc.cv[1];

    rH[0] <== vc.rH[0];
    rH[1] <== vc.rH[1];

    // 5. Bind cv_dep to (asset_id, value, rcv_dep). Fresh rcv_dep ≠ rcv lets
    //    cv re-randomize while cv_dep stays pinned to the leaf.
    component vc_dep = ValueCommit();
    for (var i = 0; i < 64; i++) {
        vc_dep.bits[i] <== rng.bits[i];
    }
    vc_dep.gen[0] <== gen.gen[0];
    vc_dep.gen[1] <== gen.gen[1];
    vc_dep.rcv    <== rcv_dep;

    cv_dep[0] <== vc_dep.cv[0];
    cv_dep[1] <== vc_dep.cv[1];
}
