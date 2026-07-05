pragma circom 2.2.3;

include "lib/spent.circom";
include "lib/output.circom";
include "lib/balance.circom";
include "lib/value_commit.circom";
include "lib/poly_eval.circom";
// MASP Pool: N_IN-input × N_OUT-output transact circuit (multi-asset).
//
// Params:
//   DEPTH — Merkle depth (capacity 4^DEPTH).
//   N_IN  — spent-note slots; empty = dummies.
//   N_OUT — output-note slots; padding = value=0 notes to self.
//
// Per-note V^t = HashToAssetGen(asset_id); public bucket
// V^pub = HashToAssetGen(public_asset_id); cv = value·V^t + rcv·H.
// Balance via Edwards point equality (PerAssetPointBalance).
//
// PI compression: verifier sees only (z, y), y = PolyEval(coeffs, z).
// Coefficient slots (MUST match PubInputs.sol :: compress(Transact, aux)):
//     [ 0] merkle_root
//     [ 1] nullifier[0]
//     [ 2] nullifier[1]
//     [ 3] out_cm[0]
//     [ 4] out_cm[1]
//     [ 5] public_asset_id
//     [ 6] public_in
//     [ 7] public_out
//     [ 8..11] in_cv[0..1][0..1]
//     [12..15] out_cv[0..1][0..1]
//     [16] recipient_address
//     [17] chain_id
//     [18] payer_address
//     [19] relayer_address
//     [20..23] out_cv_dep[0..1][0..1]   (forwarded to tree_update_batch)
//   Slots [24 .. 24 + 3·N_OUT): per-output (clueRx, clueRy, clueBits).
//   Total = 24 + 3·N_OUT = 30 for N_OUT=2.
//
// FMD clue: off-circuit, PolyEval-bound. GAMMA = subscription param, not circuit.
// Per-slot logic in SpentNote / OutputNote; this file is wiring.
//
// Contract checks (not here): chain_id == block.chainid; recipient_address < 2^160;
//   nullifier[i] unspent; out_cm[j] inserted into cm tree.
// Here: in_asset, out_asset, public_asset_id, public_in, public_out < 2^64.

template Transact(DEPTH, N_IN, N_OUT) {
    // ===== PUBLIC (verifier-visible) =====
    signal input  z;   // Fiat-Shamir challenge.
    signal output y;   // PolyEval(coeffs, z).

    // ===== LOGICAL PIs (private; bound via PolyEval) =====
    signal input merkle_root;
    signal input nullifier[N_IN];
    signal input out_cm[N_OUT];
    signal input public_asset_id;
    signal input public_in;
    signal input public_out;
    signal input in_cv[N_IN][2];
    signal input out_cv[N_OUT][2];
    signal input recipient_address;
    signal input chain_id;
    signal input payer_address;
    signal input relayer_address;

    // cv_dep: pins (asset, value) into the inserted leaf; forwarded to
    // tree_update_batch.
    signal input out_cv_dep[N_OUT][2];

    // ===== PRIVATE: spent notes =====
    signal input in_asset[N_IN];
    signal input in_value[N_IN];
    signal input in_pk[N_IN];
    signal input in_rho[N_IN];
    signal input in_rcm[N_IN];
    signal input in_nsk[N_IN];
    signal input in_rcv[N_IN];
    signal input in_rcv_dep[N_IN];
    signal input in_path_elements[N_IN][DEPTH][3];
    signal input in_path_indices[N_IN][DEPTH];
    signal input in_is_dummy[N_IN];

    // ===== PRIVATE: output notes =====
    signal input out_asset[N_OUT];
    signal input out_value[N_OUT];
    signal input out_pk[N_OUT];
    signal input out_rho[N_OUT];
    signal input out_rcm[N_OUT];
    signal input out_rcv[N_OUT];
    signal input out_rcv_dep[N_OUT];

    // ===== LOGICAL PIs: FMD clue (PolyEval-bound, no constraints) =====
    // GAMMA subscription param; upper bits masked by contract.
    signal input out_clue_bits[N_OUT];
    signal input out_clue_Rx[N_OUT];
    signal input out_clue_Ry[N_OUT];

    // -------------------------------------------------------------------------
    // Spent-note slots
    // -------------------------------------------------------------------------
    component spent[N_IN];
    component in_dz = DummyZeroValue(N_IN);

    for (var i = 0; i < N_IN; i++) {
        spent[i] = SpentNote(DEPTH);
        spent[i].asset_id <== in_asset[i];
        spent[i].value    <== in_value[i];
        spent[i].pk       <== in_pk[i];
        spent[i].rho      <== in_rho[i];
        spent[i].rcm      <== in_rcm[i];
        spent[i].nsk      <== in_nsk[i];
        spent[i].rcv      <== in_rcv[i];
        spent[i].rcv_dep  <== in_rcv_dep[i];
        spent[i].is_dummy <== in_is_dummy[i];
        for (var d = 0; d < DEPTH; d++) {
            spent[i].path_elements[d][0] <== in_path_elements[i][d][0];
            spent[i].path_elements[d][1] <== in_path_elements[i][d][1];
            spent[i].path_elements[d][2] <== in_path_elements[i][d][2];
            spent[i].path_indices[d]     <== in_path_indices[i][d];
        }
        spent[i].root      <== merkle_root;
        spent[i].nullifier <== nullifier[i];
        spent[i].cv[0]     <== in_cv[i][0];
        spent[i].cv[1]     <== in_cv[i][1];

        // dummy ⇒ value == 0.
        in_dz.dummy[i] <== in_is_dummy[i];
        in_dz.value[i] <== in_value[i];
    }

    // -------------------------------------------------------------------------
    // Output-note slots
    // -------------------------------------------------------------------------
    component out_note[N_OUT];

    for (var j = 0; j < N_OUT; j++) {
        out_note[j] = OutputNote();
        out_note[j].asset_id <== out_asset[j];
        out_note[j].value    <== out_value[j];
        out_note[j].pk       <== out_pk[j];
        out_note[j].rho      <== out_rho[j];
        out_note[j].rcm      <== out_rcm[j];
        out_note[j].rcv      <== out_rcv[j];
        out_note[j].rcv_dep  <== out_rcv_dep[j];
        out_note[j].cm       <== out_cm[j];
        out_note[j].cv[0]    <== out_cv[j][0];
        out_note[j].cv[1]    <== out_cv[j][1];

        // Bind public out_cv_dep to OutputNote.cv_dep.
        out_cv_dep[j][0] === out_note[j].cv_dep[0];
        out_cv_dep[j][1] === out_note[j].cv_dep[1];
    }

    // Public-bucket scalar mults: V^pub = HashToAssetGen(public_asset_id).
    component pub_gen = HashToAssetGen();
    pub_gen.asset_id <== public_asset_id;

    component pub_in_rng = RangeCheck64();
    pub_in_rng.v <== public_in;

    component pub_in_mul = ValueScalarMul();
    for (var i = 0; i < 64; i++) {
        pub_in_mul.bits[i] <== pub_in_rng.bits[i];
    }
    pub_in_mul.gen[0] <== pub_gen.gen[0];
    pub_in_mul.gen[1] <== pub_gen.gen[1];

    component pub_out_rng = RangeCheck64();
    pub_out_rng.v <== public_out;

    component pub_out_mul = ValueScalarMul();
    for (var i = 0; i < 64; i++) {
        pub_out_mul.bits[i] <== pub_out_rng.bits[i];
    }
    pub_out_mul.gen[0] <== pub_gen.gen[0];
    pub_out_mul.gen[1] <== pub_gen.gen[1];

    component bal = PerAssetPointBalance(N_IN, N_OUT);
    for (var i = 0; i < N_IN; i++) {
        bal.in_cv[i][0] <== in_cv[i][0];
        bal.in_cv[i][1] <== in_cv[i][1];
        bal.in_rH[i][0] <== spent[i].rH[0];
        bal.in_rH[i][1] <== spent[i].rH[1];
    }
    for (var j = 0; j < N_OUT; j++) {
        bal.out_cv[j][0] <== out_cv[j][0];
        bal.out_cv[j][1] <== out_cv[j][1];
        bal.out_rH[j][0] <== out_note[j].rH[0];
        bal.out_rH[j][1] <== out_note[j].rH[1];
    }
    bal.pub_in_pt[0]  <== pub_in_mul.out[0];
    bal.pub_in_pt[1]  <== pub_in_mul.out[1];
    bal.pub_out_pt[0] <== pub_out_mul.out[0];
    bal.pub_out_pt[1] <== pub_out_mul.out[1];

    // PI compression → (z, y). Layout in TransactCompressN.
    component pe = TransactCompressN(N_IN, N_OUT);
    pe.z <== z;
    pe.merkle_root <== merkle_root;
    for (var i = 0; i < N_IN; i++) {
        pe.nullifier[i] <== nullifier[i];
        pe.in_cv[i][0]  <== in_cv[i][0];
        pe.in_cv[i][1]  <== in_cv[i][1];
    }
    for (var j = 0; j < N_OUT; j++) {
        pe.out_cm[j]        <== out_cm[j];
        pe.out_cv[j][0]     <== out_cv[j][0];
        pe.out_cv[j][1]     <== out_cv[j][1];
        pe.out_cv_dep[j][0] <== out_cv_dep[j][0];
        pe.out_cv_dep[j][1] <== out_cv_dep[j][1];
        pe.out_clue_Rx[j]   <== out_clue_Rx[j];
        pe.out_clue_Ry[j]   <== out_clue_Ry[j];
        pe.out_clue_bits[j] <== out_clue_bits[j];
    }
    pe.public_asset_id   <== public_asset_id;
    pe.public_in         <== public_in;
    pe.public_out        <== public_out;
    pe.recipient_address <== recipient_address;
    pe.chain_id          <== chain_id;
    pe.payer_address     <== payer_address;
    pe.relayer_address   <== relayer_address;
    y <== pe.y;
}

// Verifier sees only (z, y). Params must match on-chain CommitmentTree.
// DEPTH=10 → 4^10 = 1,048,576 leaves; N_IN=2 spent; N_OUT=2 output.
component main {
    public [ z ]
} = Transact(10, 2, 2);
