pragma circom 2.2.3;

include "note.circom";
include "merkle.circom";
include "balance.circom";
include "asset_gen.circom";
include "value_commit.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";

// SpentNote: constraints for ONE spent-note slot.
//
// is_dummy == 0 (real):
//   - pk = Poseidon(TAG_PK, Poseidon(TAG_IVK, nsk)).
//   - Merkle membership of leaf at root.
//   - asset_id != 0 (ghost-note defense).
//
// is_dummy == 1 (dummy):
//   - pk / Merkle / asset_nz bypassed; prover picks fresh nsk, rho so nf
//     looks real. Caller enforces is_dummy · value === 0 (DummyZeroValue)
//     so the slot adds identity to per-asset balance.
//
// Always:
//   - nullifier === Poseidon(TAG_NF, nk, rho), nk = Poseidon(TAG_NK, nsk).
//   - value < 2^64.
//   - cv     === ValueCommit(value, HashToAssetGen(asset_id), rcv).
//   - cv_dep === ValueCommit(value, HashToAssetGen(asset_id), rcv_dep).
//   - leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y); pins
//     (asset, value) so the deposit path cannot reopen under different values.
//
// rH exposed for PerAssetPointBalance (point-sum avoids Σrcv_in − Σrcv_out
// field wrap — see balance.circom).
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

    // 3. Range-check value; bits shared with both ValueCommits.
    component rng_in = RangeCheck64();
    rng_in.v <== value;

    // 4. cv_dep = ValueCommit(value, V^asset, rcv_dep). Must match the value
    //    originally committed at deposit (or by the prior spend).
    component gen_in = HashToAssetGen();
    gen_in.asset_id <== asset_id;

    component vc_dep = ValueCommit();
    for (var i = 0; i < 64; i++) {
        vc_dep.bits[i] <== rng_in.bits[i];
    }
    vc_dep.gen[0] <== gen_in.gen[0];
    vc_dep.gen[1] <== gen_in.gen[1];
    vc_dep.rcv    <== rcv_dep;

    // 5. leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y).
    component leaf_h = Poseidon(4);
    leaf_h.inputs[0] <== TAG_LEAF();
    leaf_h.inputs[1] <== cm.cm;
    leaf_h.inputs[2] <== vc_dep.cv[0];
    leaf_h.inputs[3] <== vc_dep.cv[1];

    // 6. Merkle membership (skipped if is_dummy).
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

    // 7. Nullifier always enforced: nf = Poseidon(TAG_NF, Poseidon(TAG_NK, nsk), rho).
    //    Dummy slots use fresh (nsk, rho) so nf is on-chain indistinguishable.
    component nk_d = DeriveNk();
    nk_d.nsk <== nsk;

    component nf_h = Nullifier();
    nf_h.nk  <== nk_d.nk;
    nf_h.rho <== rho;
    nf_h.nf === nullifier;

    // 8. asset_id != 0 for real notes (ghost-note defense).
    component asset_nz = IsZero();
    asset_nz.in <== asset_id;
    (1 - is_dummy) * asset_nz.out === 0;

    // 9. Bind cv to (asset_id, value, rcv). Forces cv on-curve; without it an
    //    off-curve cv could break the balance check.
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
