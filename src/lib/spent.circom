pragma circom 2.2.3;

include "note.circom";
include "merkle.circom";
include "balance.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";

// One spent-note slot.
//
// The note's pk is not an input. It is derived from the slot's nsk and d,
//   pk = Poseidon(TAG_PK, Poseidon(TAG_IVK, nsk), d),
// so the commitment opened here is owned by nsk on every slot.
//
// is_dummy = 0 enforces Merkle membership and asset_id != 0.
// is_dummy = 1 bypasses both; the caller's DummyZeroValue forces value == 0.
// d is any field element in both cases.
//
// Enforced in both cases:
//   is_dummy is boolean (MerkleProofOrDummy)
//   value, asset_id < 2^64
//   cm == Poseidon(TAG_CM, asset_id·2^64 + value, Poseidon(TAG_INNER, pk, rho, rcm))
//   nf == Poseidon(TAG_NF, Poseidon(TAG_NK, nsk), rho, cm)
//
// The leaf is cm. tree_update_batch inserts a spend's out_cm as it stands and
// builds a deposit's leaf from its public (asset, value) by the same hash, so
// opening cm here pins the note to the (asset, value) it was inserted with.
template SpentNote(DEPTH) {
    // ===== PRIVATE =====
    signal input asset_id;
    signal input value;
    signal input rho;
    signal input rcm;
    signal input nsk;
    signal input d;
    signal input path_elements[DEPTH][3];
    signal input path_indices[DEPTH];
    signal input is_dummy;

    // ===== PUBLIC BINDING =====
    signal input root;
    signal input nullifier;

    // 1. nsk → ivk, then (ivk, d) → pk.
    component ivk_d = DeriveIvk();
    ivk_d.nsk <== nsk;

    component owner_pk = DerivePk();
    owner_pk.ivk <== ivk_d.ivk;
    owner_pk.d   <== d;

    // 2. Range-check value and asset_id, on dummy slots too: the packing in
    //    step 3 is injective only under both bounds.
    component rng_value = RangeCheck64();
    rng_value.v <== value;

    component rng_asset = RangeCheck64();
    rng_asset.v <== asset_id;

    // 3. Note commitment.
    component inner = NoteInner();
    inner.owner_pk <== owner_pk.pk;
    inner.rho      <== rho;
    inner.rcm      <== rcm;

    component cm = NoteCommitment();
    cm.asset_id <== asset_id;
    cm.value    <== value;
    cm.inner    <== inner.inner;

    // 4. Merkle membership of cm, skipped when is_dummy == 1.
    component mp = MerkleProofOrDummy(DEPTH);
    mp.leaf     <== cm.cm;
    mp.root     <== root;
    mp.is_dummy <== is_dummy;
    for (var l = 0; l < DEPTH; l++) {
        mp.path_elements[l][0] <== path_elements[l][0];
        mp.path_elements[l][1] <== path_elements[l][1];
        mp.path_elements[l][2] <== path_elements[l][2];
        mp.path_indices[l]     <== path_indices[l];
    }

    // 5. Nullifier. cm is in the preimage, so a rho collision alone cannot lock
    //    a note.
    component nk_d = DeriveNk();
    nk_d.nsk <== nsk;

    component nf_h = Nullifier();
    nf_h.nk  <== nk_d.nk;
    nf_h.rho <== rho;
    nf_h.cm  <== cm.cm;
    nf_h.nf === nullifier;

    // 6. Real notes carry asset_id != 0. Id 0 means "no asset": the transparent
    //    bucket of a transfer names it, and a zero-value deposit leaf may.
    component asset_nz = IsZero();
    asset_nz.in <== asset_id;
    (1 - is_dummy) * asset_nz.out === 0;
}
