pragma circom 2.2.3;

include "spent.circom";
include "output.circom";
include "balance.circom";
include "asset_gen.circom";
include "value_commit.circom";
include "poly_eval.circom";

// MASP pool: N_IN-input × N_OUT-output multi-asset transact circuit.
// Instantiated by 4x6.circom.
//
// Parameters:
//   DEPTH — Merkle depth; capacity 4^DEPTH leaves.
//   N_IN  — spent-note slots; unused slots are dummies.
//   N_OUT — output-note slots; unused slots are value-0 notes to self.
//
// Per-note generator V^t = HashToAssetGen(asset_id); the transparent bucket
// uses V^pub = HashToAssetGen(public_asset_id); cv = value·V^t + rcv·H.
// PerAssetValueBalance enforces conservation; PerAssetPointBalance is defence
// in depth (see balance.circom).
//
// Per-slot constraints live in SpentNote and OutputNote; this template wires
// them together.
//
// The verifier sees only the public signals (y, z), in that order, with
// y = PolyEval(coeffs, z). The coefficient layout is TransactCompressN's and
// must match PubInputs.sol.
//
// Enforced here: in_asset, out_asset, public_asset_id, public_in and public_out
// are all < 2^64.
//
// Left to the contract: chain_id == block.chainid, recipient_address < 2^160,
// each nullifier[i] unspent, each out_cm[j] inserted into the commitment tree,
// and out_aux_digest recomputed from the aux calldata rather than taken from it.
template Transact(DEPTH, N_IN, N_OUT) {
    // ===== PUBLIC (verifier-visible) =====
    signal input  z;   // Fiat-Shamir challenge.
    signal output y;   // PolyEval(coeffs, z).

    // ===== LOGICAL PUBLIC INPUTS (private signals, bound via PolyEval) =====
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

    // Pins (asset, value) into the inserted leaf; forwarded to tree_update_batch.
    signal input out_cv_dep[N_OUT][2];

    // FMD clue. Computed off-circuit and constrained only by PolyEval; GAMMA is a
    // subscription-time parameter, not a circuit parameter.
    signal input out_clue_bits[N_OUT];
    signal input out_clue_Rx[N_OUT];
    signal input out_clue_Ry[N_OUT];

    // Digest of the encrypted-note payload (ephPub + ciphertext, per output),
    // computed off-circuit and constrained only by PolyEval, as the clue fields
    // are. Stops a relayer corrupting the payload while keeping the proof
    // valid; see poly_eval.circom :: TransactCompressN.
    signal input out_aux_digest;

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

        // is_dummy == 1 ⇒ value == 0.
        in_dz.dummy[i] <== in_is_dummy[i];
        in_dz.value[i] <== in_value[i];
    }

    // -------------------------------------------------------------------------
    // Output-note slots
    // -------------------------------------------------------------------------
    // out_rho is pinned to DeriveRho(nullifier[0], j) so no two committed output
    // notes can share a rho, and therefore no two can share a future nullifier.
    component out_rho_d[N_OUT];
    component out_note[N_OUT];

    for (var j = 0; j < N_OUT; j++) {
        out_rho_d[j] = DeriveRho();
        out_rho_d[j].nf0   <== nullifier[0];
        out_rho_d[j].index <== j;
        out_rho[j] === out_rho_d[j].rho;

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

    // -------------------------------------------------------------------------
    // Transparent bucket: public_in / public_out as points on V^pub
    // -------------------------------------------------------------------------
    component pub_gen = HashToAssetGen();
    pub_gen.asset_id <== public_asset_id;

    component pub_in_mul = ValueTimesGen();
    pub_in_mul.value  <== public_in;
    pub_in_mul.gen[0] <== pub_gen.gen[0];
    pub_in_mul.gen[1] <== pub_gen.gen[1];

    component pub_out_mul = ValueTimesGen();
    pub_out_mul.value  <== public_out;
    pub_out_mul.gen[0] <== pub_gen.gen[0];
    pub_out_mul.gen[1] <== pub_gen.gen[1];

    // -------------------------------------------------------------------------
    // Value conservation
    // -------------------------------------------------------------------------
    component vbal = PerAssetValueBalance(N_IN, N_OUT);
    for (var i = 0; i < N_IN; i++) {
        vbal.in_asset[i] <== in_asset[i];
        vbal.in_value[i] <== in_value[i];
    }
    for (var j = 0; j < N_OUT; j++) {
        vbal.out_asset[j] <== out_asset[j];
        vbal.out_value[j] <== out_value[j];
    }
    vbal.public_asset_id <== public_asset_id;
    vbal.public_in       <== public_in;
    vbal.public_out      <== public_out;

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

    // -------------------------------------------------------------------------
    // Public-input compression → (y, z)
    // -------------------------------------------------------------------------
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
    pe.out_aux_digest    <== out_aux_digest;
    y <== pe.y;
}
