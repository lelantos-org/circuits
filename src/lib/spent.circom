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
//   - cv_dep === ValueCommit(value, HashToAssetGen(asset_id), rcv_dep).
//   - merkle leaf is Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y). Pinning the
//     deposit-anchored value commitment into the leaf prevents cm-preimage
//     substitution on the deposit path.
//
// `rH` is exposed so the caller's PerAssetPointBalance can sum rcv·H points
// across notes (avoids field-wraparound on a scalar Σrcv_in − Σrcv_out — see
// balance.circom).
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

    // 3. Range check (used by both ValueCommit invocations below).
    component rng_in = RangeCheck64();
    rng_in.v <== value;

    // 4. cv_dep = ValueCommit(value, V^asset, rcv_dep). Same Pedersen commit
    //    shape as cv but with blinder rcv_dep. The leaf format
    //    `Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y)` requires cv_dep here to
    //    match the value originally committed by the depositor (or by the
    //    spend that produced this note).
    component gen_in = HashToAssetGen();
    gen_in.asset_id <== asset_id;

    component vc_dep = ValueCommit();
    for (var i = 0; i < 64; i++) {
        vc_dep.bits[i] <== rng_in.bits[i];
    }
    vc_dep.gen[0] <== gen_in.gen[0];
    vc_dep.gen[1] <== gen_in.gen[1];
    vc_dep.rcv    <== rcv_dep;

    // 5. Recompute Merkle leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y).
    //    Domain-separated from NoteCommitment via TAG_LEAF=10; NoteCommitment's
    //    first slot holds packed_av ≥ 2^64, so the two arity-4 hash sites are
    //    distinguishable by the first input alone.
    component leaf_h = Poseidon(4);
    leaf_h.inputs[0] <== TAG_LEAF();
    leaf_h.inputs[1] <== cm.cm;
    leaf_h.inputs[2] <== vc_dep.cv[0];
    leaf_h.inputs[3] <== vc_dep.cv[1];

    // 6. Merkle membership (bypassed when is_dummy == 1).
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

    // 7. Nullifier always real: nf = Poseidon(TAG_NF, nk, rho) with
    //    nk = Poseidon(TAG_NK, nsk). nk is derived in-circuit, forcing it to
    //    be consistent with nsk. FVK auditor holds nk only and can recompute
    //    nf for any known rho. Dummy slots use prover-chosen random
    //    (nsk, rho) so nf is indistinguishable from a real spend on chain.
    component nk_d = DeriveNk();
    nk_d.nsk <== nsk;

    component nf_h = Nullifier();
    nf_h.nk  <== nk_d.nk;
    nf_h.rho <== rho;
    nf_h.nf === nullifier;

    // 8. Reject asset_id == 0 for real notes (ghost-note defense).
    component asset_nz = IsZero();
    asset_nz.in <== asset_id;
    (1 - is_dummy) * asset_nz.out === 0;

    // 9. Bind cv to (asset_id, value, rcv) via Sapling-style ValueCommit.
    //    Reuses rng_in.bits + gen_in from steps 3-4. SOUNDNESS-CRITICAL:
    //    forces the prover-supplied public cv to be on-curve. Without it, an
    //    off-curve cv could pass as a public input and break the balance
    //    check.
    component vc = ValueCommit();
    for (var i = 0; i < 64; i++) {
        vc.bits[i] <== rng_in.bits[i];
    }
    vc.gen[0] <== gen_in.gen[0];
    vc.gen[1] <== gen_in.gen[1];
    vc.rcv    <== rcv;

    cv[0] === vc.cv[0];
    cv[1] === vc.cv[1];

    rH[0] <== vc.rH[0];
    rH[1] <== vc.rH[1];
}
