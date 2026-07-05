pragma circom 2.2.3;

include "lib/spent.circom";
include "lib/output.circom";
include "lib/balance.circom";
include "lib/value_commit.circom";
include "lib/poly_eval.circom";
// MASP Pool: 3-input × 3-output transact circuit. Same wiring as 2x2.circom
// with N_IN=N_OUT=3; see it for the full spec.
//
// PI compression: verifier sees only (z, y), y = PolyEval(coeffs, z).
// Coefficient slots (MUST match PubInputs.sol :: compress(Transact3x3, aux)
// once added; layout from TransactCompressN(3,3) in lib/poly_eval.circom):
//     [ 0]        merkle_root
//     [ 1.. 3]    nullifier[0..2]
//     [ 4.. 6]    out_cm[0..2]
//     [ 7]        public_asset_id
//     [ 8]        public_in
//     [ 9]        public_out
//     [10..15]    in_cv[0..2][0..1]
//     [16..21]    out_cv[0..2][0..1]
//     [22]        recipient_address
//     [23]        chain_id
//     [24]        payer_address
//     [25]        relayer_address
//     [26..31]    out_cv_dep[0..2][0..1]   (forwarded to tree_update_batch)
//   Slots [32 .. 32 + 3·N_OUT): per-output (clueRx, clueRy, clueBits).
//   Total = 8 + 3·N_IN + 8·N_OUT = 41 for (3,3).
//
// FMD clue: off-circuit, PolyEval-bound.

template Transact3(DEPTH, N_IN, N_OUT) {
    // ===== PUBLIC =====
    signal input  z;
    signal output y;

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

    // ===== LOGICAL PIs: FMD clue (off-circuit, PolyEval-bound) =====
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

        out_cv_dep[j][0] === out_note[j].cv_dep[0];
        out_cv_dep[j][1] === out_note[j].cv_dep[1];
    }

    // Public-bucket scalar mults.
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

    // Per-asset point balance.
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

    // PI compression via generalized compressor.
    component pe = TransactCompressN(N_IN, N_OUT);
    pe.z <== z;
    pe.merkle_root <== merkle_root;
    for (var i = 0; i < N_IN; i++) {
        pe.nullifier[i] <== nullifier[i];
        pe.in_cv[i][0]  <== in_cv[i][0];
        pe.in_cv[i][1]  <== in_cv[i][1];
    }
    for (var j = 0; j < N_OUT; j++) {
        pe.out_cm[j]      <== out_cm[j];
        pe.out_cv[j][0]   <== out_cv[j][0];
        pe.out_cv[j][1]   <== out_cv[j][1];
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

// Transact3(DEPTH=10, N_IN=3, N_OUT=3). GAMMA is subscription-time parameter.
component main {
    public [ z ]
} = Transact3(10, 3, 3);
