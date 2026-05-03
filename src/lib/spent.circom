pragma circom 2.2.3;

include "note.circom";
include "merkle.circom";
include "balance.circom";
include "asset_gen.circom";
include "value_commit.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";

// SpentNote: enforces every constraint for ONE spent-note slot.
//
// Real spend (is_dummy == 0):
//   - pk derived from nsk via ivk = Poseidon(TAG_IVK, nsk), pk = Poseidon(TAG_PK, ivk).
//   - Merkle membership of cm in tree at root.
//   - asset_id != 0 (ghost-note defense; HashToAssetGen(0) could collapse to identity).
//
// Dummy spend (is_dummy == 1):
//   - pk / Merkle / asset_nz checks bypassed; prover supplies fresh random
//     nsk and rho so the nullifier looks real on chain. Caller must enforce
//     `is_dummy * value === 0` separately (DummyZeroValue) so a dummy slot
//     contributes the additive identity to the per-asset balance.
//
// Always:
//   - nullifier === Poseidon(TAG_NF, nk, rho)  where nk = Poseidon(TAG_NK, nsk).
//   - value < 2^64.
//   - cv === ValueCommit(value, HashToAssetGen(asset_id), rcv).
//
// `rH` is exposed so the caller's PerAssetPointBalance can sum rcv·H points
// across notes (rather than running into field-wraparound issues with a
// scalar Σrcv_in − Σrcv_out).
template SpentNote(DEPTH) {
    // ---- private witness ----
    signal input asset_id;
    signal input value;
    signal input pk;
    signal input rho;
    signal input rcm;
    signal input nsk;
    signal input rcv;
    signal input path_elements[DEPTH][3];
    signal input path_indices[DEPTH];
    signal input is_dummy;

    // ---- public binding ----
    signal input root;
    signal input nullifier;
    signal input cv[2];

    // ---- exposed for caller ----
    signal output rH[2];

    // 1. Spend auth: nsk → ivk → pk.
    component ivk_d = DeriveIvk();
    ivk_d.nsk <== nsk;

    component pk_check = DerivePk();
    pk_check.ivk <== ivk_d.ivk;
    (1 - is_dummy) * (pk_check.pk - pk) === 0;

    // 2. Recompute note commitment.
    component cm = NoteCommitment();
    cm.asset_id <== asset_id;
    cm.value    <== value;
    cm.owner_pk <== pk;
    cm.rho      <== rho;
    cm.rcm      <== rcm;

    // 3. Merkle membership (bypassed when is_dummy == 1).
    component mp = MerkleProofOrDummy(DEPTH);
    mp.leaf     <== cm.cm;
    mp.root     <== root;
    mp.is_dummy <== is_dummy;
    for (var d = 0; d < DEPTH; d++) {
        mp.path_elements[d][0] <== path_elements[d][0];
        mp.path_elements[d][1] <== path_elements[d][1];
        mp.path_elements[d][2] <== path_elements[d][2];
        mp.path_indices[d]     <== path_indices[d];
    }

    // 4. Nullifier always real: nf = Poseidon(TAG_NF, nk, rho) with
    //    nk = Poseidon(TAG_NK, nsk). nk is derived in-circuit so the prover
    //    cannot smuggle a different nk than the one consistent with nsk.
    //    FVK auditor holds nk only and can recompute nf for any known rho.
    //    Dummy slots use prover-chosen random (nsk, rho) so nf is
    //    indistinguishable from a real spend on chain.
    component nk_d = DeriveNk();
    nk_d.nsk <== nsk;

    component nf_h = Nullifier();
    nf_h.nk  <== nk_d.nk;
    nf_h.rho <== rho;
    nf_h.nf === nullifier;

    // 5. Range check on private value. Bits exposed and threaded into
    //    ValueCommit below so the value scalar mul does not redo Num2Bits(64).
    component rng = RangeCheck64();
    rng.v <== value;

    // 6. Reject asset_id == 0 for real notes (ghost-note defense).
    component asset_nz = IsZero();
    asset_nz.in <== asset_id;
    (1 - is_dummy) * asset_nz.out === 0;

    // 7. Bind cv to (asset_id, value, rcv) via Sapling-style ValueCommit.
    //    SOUNDNESS-CRITICAL: this equality forces the prover-supplied public
    //    cv to be on-curve. Removing it lets a malicious prover smuggle off-
    //    curve garbage as a public input and break the balance check.
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
