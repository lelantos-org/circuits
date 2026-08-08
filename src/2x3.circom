pragma circom 2.2.3;

include "lib/transact.circom";

// 2-input × 3-output transact circuit. Logic is in Transact (lib/transact.circom).
//
// PolyEval coefficient slots, which must match the PubInputs.sol :: compress
// overload for this shape:
//     [ 0]      merkle_root
//     [ 1.. 2]  nullifier[0..1]
//     [ 3.. 5]  out_cm[0..2]
//     [ 6]      public_asset_id
//     [ 7]      public_in
//     [ 8]      public_out
//     [ 9..12]  in_cv[0..1][0..1]
//     [13..18]  out_cv[0..2][0..1]
//     [19]      recipient_address
//     [20]      chain_id
//     [21]      payer_address
//     [22]      relayer_address
//     [23..28]  out_cv_dep[0..2][0..1]
//     [29..37]  (clue_Rx, clue_Ry, clue_bits) per output
//     [38]      out_aux_digest           (contract recomputes; never read from calldata)
// Total = 9 + 3·N_IN + 8·N_OUT = 39.
//
// NOT DEPLOYED. No justfile recipe compiles this shape, no test instantiates it,
// and no trusted setup exists for it. It is kept only so `Transact` is exercised
// at a second shape by the Lean development (lean/expected/layout-2x3.txt).
// Deploying it requires: a compile/setup recipe, its own phase-2 ceremony, a
// PubInputs.sol compress overload for 39 slots, a satisfying Lean witness
// (transact2x3_sound is not yet shown non-vacuous), and extending
// layout_parity.test.ts to this shape.
component main {
    public [ z ]
} = Transact(10, 2, 3);
