pragma circom 2.2.3;

include "lib/insert.circom";
include "lib/poly_eval.circom";
include "../node_modules/circomlib/circuits/bitify.circom";

// TreeUpdate: relayer-side proof that the canonical commitment tree advances
// from `old_root` to `new_root` by inserting exactly two leaves [cm0, cm1] at
// indices [start_index, start_index+1] over a relayer-supplied frontier.
//
// Lazy-root model:
//   - The contract's MASP.transact carries (transact_2x2 proof, tree_update
//     proof). The tree-update proof binds (oldRoot, newRoot, cm0, cm1,
//     startIndex). The contract enforces oldRoot == currentRoot() and
//     startIndex == committedCount, then advances the on-chain root ring.
//   - `old_root` is NOT recomputed in-circuit from the frontier. The contract
//     anchors it via the chain check; an inconsistent (frontier_in, old_root)
//     would still produce *some* new_root, which the contract would commit,
//     but no honest tree reconstruction would reproduce it — useless ring
//     entry, no soundness break (relayer harms only itself).
//
// PI compression mirrors 2x2.circom: 5 logical PIs are folded into (z, y) via
// PolyEval(5). Coefficient ordering MUST match the contract's
// _compressTreeUpdatePI (TreeUpdatePubInputs flatten order):
//
//   [0] old_root
//   [1] new_root
//   [2] cm0
//   [3] cm1
//   [4] start_index
//
// Quaternary tree, depth 10 → 4^10 = 2^20 = 1,048,576 leaves.
// We need start_index + 1 to fit in 20 bits, so start_index ≤ 2^20 - 2.
// The Num2Bits(20) on (start_index + 1) is the binding range check.
template TreeUpdate(DEPTH) {
    // ===== PUBLIC (verifier-visible) =====
    signal input  z;   // Fiat-Shamir challenge supplied by the contract.
    signal output y;   // PolyEval(5)(coeffs, z); binds the 5 logical PIs.

    // ===== LOGICAL PIs — private witnesses, bound via PolyEval =====
    signal input old_root;
    signal input new_root;
    signal input cm0;
    signal input cm1;
    signal input start_index;

    // ===== PRIVATE: relayer-supplied frontier =====
    signal input frontier_in[DEPTH][3];

    // -------------------------------------------------------------------------
    // Decompose start_index and start_index+1 into 2-bit-per-level digits.
    //
    // Num2Bits(2*DEPTH) on (start_index + 1) is the binding bound: it succeeds
    // iff start_index + 1 < 2^(2*DEPTH) = 4^DEPTH. So start_index ≤ 4^DEPTH-2,
    // leaving room for the second insert at start_index + 1 ≤ 4^DEPTH - 1.
    // We also Num2Bits(2*DEPTH) on start_index itself for digit extraction.
    // -------------------------------------------------------------------------
    var BITS = 2 * DEPTH;

    component sb0 = Num2Bits(BITS);
    sb0.in <== start_index;

    signal start_plus_1;
    start_plus_1 <== start_index + 1;

    component sb1 = Num2Bits(BITS);
    sb1.in <== start_plus_1;

    signal idx0_digits[DEPTH];
    signal idx1_digits[DEPTH];
    for (var d = 0; d < DEPTH; d++) {
        idx0_digits[d] <== sb0.out[2*d] + 2 * sb0.out[2*d + 1];
        idx1_digits[d] <== sb1.out[2*d] + 2 * sb1.out[2*d + 1];
    }

    // -------------------------------------------------------------------------
    // First insert: cm0 at start_index over frontier_in.
    // -------------------------------------------------------------------------
    component ins0 = QuaternaryInsert(DEPTH);
    ins0.leaf <== cm0;
    for (var d = 0; d < DEPTH; d++) {
        ins0.idx_digit[d] <== idx0_digits[d];
        for (var s = 0; s < 3; s++) {
            ins0.frontier_in[d][s] <== frontier_in[d][s];
        }
    }

    // -------------------------------------------------------------------------
    // Second insert: cm1 at start_index+1 over the post-first-insert frontier.
    // -------------------------------------------------------------------------
    component ins1 = QuaternaryInsert(DEPTH);
    ins1.leaf <== cm1;
    for (var d = 0; d < DEPTH; d++) {
        ins1.idx_digit[d] <== idx1_digits[d];
        for (var s = 0; s < 3; s++) {
            ins1.frontier_in[d][s] <== ins0.frontier_out[d][s];
        }
    }

    // -------------------------------------------------------------------------
    // Bind the public new_root to the second insert's output root.
    // -------------------------------------------------------------------------
    new_root === ins1.root;

    // -------------------------------------------------------------------------
    // Compress (old_root, new_root, cm0, cm1, start_index) into (z, y).
    // Order MUST match contract _compressTreeUpdatePI.
    // -------------------------------------------------------------------------
    component pe = PolyEval(5);
    pe.coeffs[0] <== old_root;
    pe.coeffs[1] <== new_root;
    pe.coeffs[2] <== cm0;
    pe.coeffs[3] <== cm1;
    pe.coeffs[4] <== start_index;
    pe.z <== z;
    y    <== pe.y;
}

component main {
    public [ z ]
} = TreeUpdate(10);
