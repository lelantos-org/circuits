pragma circom 2.2.3;

include "lib/transact.circom";

// 2-input × 2-output transact circuit. Logic is in Transact (lib/transact.circom).
// Not the deployed shape (see 3x3.circom); it is the shape the Lean
// satisfiability witnesses are built at.
//
// DEPTH = 10 matches the on-chain CommitmentTree: 4^10 = 1,048,576 leaves.
//
// PolyEval coefficient slots, which must match PubInputs.sol :: compress(Transact, aux):
//     [ 0]      merkle_root
//     [ 1.. 2]  nullifier[0..1]
//     [ 3.. 4]  out_cm[0..1]
//     [ 5]      public_asset_id
//     [ 6]      public_in
//     [ 7]      public_out
//     [ 8..11]  in_cv[0..1][0..1]
//     [12..15]  out_cv[0..1][0..1]
//     [16]      recipient_address
//     [17]      chain_id
//     [18]      payer_address
//     [19]      relayer_address
//     [20..23]  out_cv_dep[0..1][0..1]   (forwarded to tree_update_batch)
//     [24..29]  (clue_Rx, clue_Ry, clue_bits) per output
//     [30]      out_aux_digest           (contract recomputes; never read from calldata)
// Total = 9 + 3·N_IN + 8·N_OUT = 31.
component main {
    public [ z ]
} = Transact(10, 2, 2);
