pragma circom 2.2.3;

include "lib/spent.circom";
include "lib/output.circom";
include "lib/balance.circom";
include "lib/value_commit.circom";

// MASP Pool: N_IN-input × N_OUT-output transact circuit (v1, multi-asset).
//
// Template params:
//   DEPTH  — Merkle tree depth (quaternary). Capacity = 4^DEPTH.
//   N_IN   — number of spent-note slots. Empty slots = dummies.
//   N_OUT  — number of output-note slots. Padding outputs are real value=0
//            notes addressed to self (no on-chain dummy sentinel).
//
// Public inputs (Solidity verifier sees these):
//   merkle_root, nullifier[..], out_cm[..],
//   public_asset_id, pub_asset_gen_x, pub_asset_gen_y,
//   public_in, public_out,
//   in_cv[..][2], out_cv[..][2],
//   recipient_address, chain_id
//
// Multi-asset model (Sapling / Namada-faithful):
//   - Each note carries a private asset_id. Circuit derives a Baby-Jubjub
//     generator V^t = HashToAssetGen(asset_id) per note.
//   - Per-note value commitment cv = value · V^t + rcv · H (Sapling).
//   - Balance check via Edwards point equality:
//        Σ in_cv + public_in · V^pub + Σ out_rH
//          == Σ out_cv + public_out · V^pub + Σ in_rH
//     where V^pub is the public asset generator passed as (x,y) by the
//     contract from a precomputed registry.
//   - Distinct assets live in distinct V^t subgroups, so cross-asset balance
//     leakage is impossible without breaking the discrete log of Pedersen.
//
// Per-slot logic is delegated to `SpentNote` (lib/spent.circom) and
// `OutputNote` (lib/output.circom). This file is a wiring layer only.
//
// Properties NOT enforced in-circuit — contract MUST check before verifying:
//   - chain_id == block.chainid
//   - public_in, public_out  < 2^64
//   - public_asset_id < 2^64 (or whatever registry key range applies)
//   - registry[public_asset_id] == (pub_asset_gen_x, pub_asset_gen_y)
//   - recipient_address typed as address (< 2^160)
//   - nullifier[i] always inserted (no sentinel); revert on already-spent
//   - out_cm[j] always inserted into cm tree (no sentinel)

template Transact(DEPTH, N_IN, N_OUT) {
    // ===== PUBLIC =====
    signal input merkle_root;
    signal input nullifier[N_IN];
    signal input out_cm[N_OUT];
    signal input public_asset_id;
    signal input pub_asset_gen_x;
    signal input pub_asset_gen_y;
    signal input public_in;
    signal input public_out;
    signal input in_cv[N_IN][2];
    signal input out_cv[N_OUT][2];
    signal input recipient_address;
    signal input chain_id;

    // ===== PRIVATE: spent notes =====
    signal input in_asset[N_IN];
    signal input in_value[N_IN];
    signal input in_pk[N_IN];
    signal input in_rho[N_IN];
    signal input in_rcm[N_IN];
    signal input in_nsk[N_IN];
    signal input in_rcv[N_IN];
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

        // Dummy ⇒ value == 0 so dummy slots add the additive identity to balance.
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
        out_note[j].cm       <== out_cm[j];
        out_note[j].cv[0]    <== out_cv[j][0];
        out_note[j].cv[1]    <== out_cv[j][1];
    }

    // -------------------------------------------------------------------------
    // Public-bucket scalar mults
    //
    // Caller (contract) supplies (pub_asset_gen_x, pub_asset_gen_y) from a
    // precomputed registry keyed by public_asset_id. Validate the supplied
    // point in-circuit:
    //   - on Baby-Jubjub curve
    //   - x != 0 (rules out identity (0,1) and 2-torsion (0,-1))
    // Prime-order subgroup membership (cofactor 8) is enforced off-chain by
    // the contract; see CIRCUITS.md "Smart-contract obligations".
    //
    // ValueScalarMul also range-checks public_in / public_out to 64 bits via
    // its inner Num2Bits(64) — belt-and-suspenders to the on-chain `< 2^64`.
    // -------------------------------------------------------------------------
    component pub_gen_safe = SafePoint();
    pub_gen_safe.p[0] <== pub_asset_gen_x;
    pub_gen_safe.p[1] <== pub_asset_gen_y;

    component pub_in_mul = ValueScalarMul();
    pub_in_mul.value  <== public_in;
    pub_in_mul.gen[0] <== pub_asset_gen_x;
    pub_in_mul.gen[1] <== pub_asset_gen_y;

    component pub_out_mul = ValueScalarMul();
    pub_out_mul.value  <== public_out;
    pub_out_mul.gen[0] <== pub_asset_gen_x;
    pub_out_mul.gen[1] <== pub_asset_gen_y;

    // -------------------------------------------------------------------------
    // Per-asset point balance
    //
    // Substituting cv = value·V + rcv·H and rearranging so rcv·H cancels:
    //   Σ in_cv + public_in·V^pub + Σ out_rH  ==  Σ out_cv + public_out·V^pub + Σ in_rH
    // Equivalent to per-asset value conservation:
    //   Σ value_in·V_in + public_in·V^pub  ==  Σ value_out·V_out + public_out·V^pub
    // Distinct assets live in distinct subgroups (independent V^t points),
    // so cross-asset cancellation is infeasible.
    // -------------------------------------------------------------------------
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
    // Pin orphan public signals
    //
    // public_asset_id is bound by the contract registry but otherwise has no
    // in-circuit constraint partner; recipient_address and chain_id are
    // similarly unconstrained here. PinPublic prevents circom from pruning
    // them from the public-signal layout.
    // -------------------------------------------------------------------------
    component pin = PinPublic(3);
    pin.v[0] <== public_asset_id;
    pin.v[1] <== recipient_address;
    pin.v[2] <== chain_id;
}

component main {
    public [
        merkle_root,
        nullifier,
        out_cm,
        public_asset_id,
        pub_asset_gen_x,
        pub_asset_gen_y,
        public_in,
        public_out,
        in_cv,
        out_cv,
        recipient_address,
        chain_id
    ]
// Quaternary tree: depth 10 → 4^10 = 1,048,576 leaves (binary-equivalent depth 20).
} = Transact(10, 2, 2);
