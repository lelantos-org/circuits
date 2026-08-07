pragma circom 2.2.3;

include "lib/transact.circom";

// 3-input × 3-output transact circuit. Logic is in Transact (lib/transact.circom).
//
// PolyEval coefficient slots, which must match the PubInputs.sol :: compress
// overload for this shape:
//     [ 0]      merkle_root
//     [ 1.. 3]  nullifier[0..2]
//     [ 4.. 6]  out_cm[0..2]
//     [ 7]      public_asset_id
//     [ 8]      public_in
//     [ 9]      public_out
//     [10..15]  in_cv[0..2][0..1]
//     [16..21]  out_cv[0..2][0..1]
//     [22]      recipient_address
//     [23]      chain_id
//     [24]      payer_address
//     [25]      relayer_address
//     [26..31]  out_cv_dep[0..2][0..1]
//     [32..40]  (clue_Rx, clue_Ry, clue_bits) per output
// Total = 8 + 3·N_IN + 8·N_OUT = 41.
component main {
    public [ z ]
} = Transact(10, 3, 3);
