pragma circom 2.2.3;

include "note.circom";
include "balance.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";

// One output-note slot. Enforces:
//   value, asset_id < 2^64 and asset_id != 0
//   cm == Poseidon(TAG_CM, asset_id·2^64 + value, Poseidon(TAG_INNER, pk, rho, rcm))
//
// cm is the leaf tree_update_batch inserts for this slot.
template OutputNote() {
    // ===== PRIVATE =====
    signal input asset_id;
    signal input value;
    signal input pk;
    signal input rho;
    signal input rcm;

    // ===== PUBLIC BINDING =====
    signal input cm;

    // 1. Range-check value and asset_id; NoteCommitment's packing needs both.
    component rng_value = RangeCheck64();
    rng_value.v <== value;

    component rng_asset = RangeCheck64();
    rng_asset.v <== asset_id;

    // 2. asset_id != 0; id 0 means "no asset" (see SpentNote).
    component asset_nz = IsZero();
    asset_nz.in <== asset_id;
    asset_nz.out === 0;

    // 3. Bind cm.
    component inner = NoteInner();
    inner.owner_pk <== pk;
    inner.rho      <== rho;
    inner.rcm      <== rcm;

    component cm_h = NoteCommitment();
    cm_h.asset_id <== asset_id;
    cm_h.value    <== value;
    cm_h.inner    <== inner.inner;
    cm_h.cm === cm;
}
