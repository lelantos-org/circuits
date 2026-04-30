pragma circom 2.2.3;

include "note.circom";
include "balance.circom";
include "asset_gen.circom";
include "value_commit.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";

// OutputNote: enforces every constraint for ONE output-note slot.
//
//   - cm == NoteCommitment(asset_id, value, pk, rho, rcm)  (always real;
//     padding outputs are real value=0 notes addressed to the wallet itself,
//     so they are indistinguishable on chain from a real send).
//   - value < 2^64.
//   - asset_id != 0 (ghost-note defense; uniform — no dummy bypass on the
//     output side).
//   - cv == ValueCommit(value, HashToAssetGen(asset_id), rcv).
//
// `rH` is exposed for the caller's PerAssetPointBalance.
template OutputNote() {
    // ---- private witness ----
    signal input asset_id;
    signal input value;
    signal input pk;
    signal input rho;
    signal input rcm;
    signal input rcv;

    // ---- public binding ----
    signal input cm;
    signal input cv[2];

    // ---- exposed for caller ----
    signal output rH[2];

    // 1. Recompute commitment + bind to public cm.
    component cm_h = NoteCommitment();
    cm_h.asset_id <== asset_id;
    cm_h.value    <== value;
    cm_h.owner_pk <== pk;
    cm_h.rho      <== rho;
    cm_h.rcm      <== rcm;
    cm_h.cm === cm;

    // 2. Range check on private value. Bits threaded into ValueCommit below.
    component rng = RangeCheck64();
    rng.v <== value;

    // 3. Reject asset_id == 0 (ghost-note defense, no dummy bypass).
    component asset_nz = IsZero();
    asset_nz.in <== asset_id;
    asset_nz.out === 0;

    // 4. Bind cv to (asset_id, value, rcv). SOUNDNESS-CRITICAL — see SpentNote.
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
}
