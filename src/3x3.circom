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
//     [41]      out_aux_digest           (contract recomputes; never read from calldata)
// Total = 9 + 3·N_IN + 8·N_OUT = 42.
//
// NOT DEPLOYED. No justfile recipe compiles this shape, no test instantiates it,
// and no trusted setup exists for it. It is kept only so `Transact` is exercised
// at a third shape by the Lean development (lean/expected/layout-3x3.txt).
// Deploying it requires: a compile/setup recipe, its own phase-2 ceremony, a
// PubInputs.sol compress overload for 42 slots, a satisfying Lean witness
// (transact3x3_sound is not yet shown non-vacuous), and extending
// layout_parity.test.ts to this shape.
//
// Note §10.5's `require(nullifier[0] != nullifier[1])` must generalise to all
// three pairs at this shape.
component main {
    public [ z ]
} = Transact(10, 3, 3);
