pragma circom 2.2.3;

include "lib/transact.circom";

// 3-input × 3-output transact circuit, the deployed transact shape. Logic is in
// Transact (lib/transact.circom).
//
// DEPTH = 10 matches the on-chain CommitmentTree: 4^10 = 1,048,576 leaves.
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
//     [41]      out_aux_digest           (contract recomputes; never read from calldata)
// Total = 9 + 3·N_IN + 8·N_OUT = 42.
//
// Build with `just rebuild-3x3`, which exports the verifier to
// contracts/src/verifiers/Verifier.sol. The layout is pinned by
// scripts/gen-vectors.ts (refuses to publish unless the circuit's y equals the
// reference PolyEval over the 42 coefficients) and by layout_parity.test.ts
// against lean/expected/layout-3x3.txt.
//
// Not yet established for this shape:
//   - a multi-party phase-2 ceremony; setup-3x3 is single-contributor.
//   - Lean non-vacuity: transact3x3_sound has no exhibited witness.
//
// Consumer-side checks indexed by input or output must range over the whole
// shape: pairwise nullifier distinctness over all three pairs, and the out_cm
// and out_cv_dep cross-bindings to tree_update_batch over all three outputs.
// out_cv_dep sits inside the leaf preimage and spent.circom recomputes it from
// the note, so an unbound output index yields an unspendable leaf.
component main {
    public [ z ]
} = Transact(10, 3, 3);
