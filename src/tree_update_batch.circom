pragma circom 2.2.3;

include "lib/insert.circom";
include "lib/poly_eval.circom";
include "../node_modules/circomlib/circuits/bitify.circom";
include "../node_modules/circomlib/circuits/comparators.circom";

// TreeUpdateBatch: relayer-side proof that the canonical commitment tree
// advances from `old_root` to `new_root` by inserting up to MAX_N pairs of
// leaves [cms[0], cms[1], cms[2], cms[3], ...] at indices
// [start_index, start_index+1, start_index+2, start_index+3, ...] over a
// relayer-supplied frontier.
//
// `actual_count` selects how many pairs are real (1 ≤ actual_count ≤ MAX_N).
// Trailing slots (i ≥ actual_count) are non-active: their cms must be 0 and
// they do not advance the running root or frontier.
//
// PI compression mirrors tree_update.circom: logical PIs folded into (z, y)
// via PolyEval. Coefficient ordering MUST match the contract's
// _compressTreeUpdateBatchPI flatten order:
//
//   [0]                       old_root
//   [1]                       new_root
//   [2]                       start_index
//   [3]                       actual_count
//   [4 .. 3 + 2*MAX_N]        cms[0 .. 2*MAX_N - 1]
//
// Quaternary tree, depth DEPTH → 4^DEPTH leaves.
// We need start_index + 2*MAX_N - 1 to fit in 2*DEPTH bits.
template TreeUpdateBatch(DEPTH, MAX_N) {
    // ===== PUBLIC =====
    signal input  z;
    signal output y;

    // ===== LOGICAL PIs =====
    signal input old_root;
    signal input new_root;
    signal input start_index;
    signal input actual_count;            // 1..MAX_N
    signal input cms[2 * MAX_N];          // padding (i ≥ 2*actual_count) MUST be 0

    // ===== PRIVATE =====
    signal input frontier_in[DEPTH][3];

    // -------------------------------------------------------------------------
    // 1. Range-check actual_count ∈ [1, MAX_N].
    //    Decompose (actual_count - 1) in COUNT_BITS bits where 2^COUNT_BITS ≥ MAX_N.
    //    For MAX_N = 16 → COUNT_BITS = 4 → bounds (actual_count - 1) ∈ [0, 15]
    //    → actual_count ∈ [1, 16].
    // -------------------------------------------------------------------------
    var COUNT_BITS = 4;
    assert((1 << COUNT_BITS) >= MAX_N);
    component cnt_bits = Num2Bits(COUNT_BITS);
    cnt_bits.in <== actual_count - 1;

    // -------------------------------------------------------------------------
    // 2. Per-pair active selectors: active[i] = (i < actual_count).
    // -------------------------------------------------------------------------
    component lt[MAX_N];
    signal active[MAX_N];
    for (var i = 0; i < MAX_N; i++) {
        lt[i] = LessThan(COUNT_BITS + 1);
        lt[i].in[0] <== i;
        lt[i].in[1] <== actual_count;
        active[i] <== lt[i].out;
    }

    // -------------------------------------------------------------------------
    // 3. Padding constraint: if !active[i], both cms must be zero.
    // -------------------------------------------------------------------------
    for (var i = 0; i < MAX_N; i++) {
        // (1 - active[i]) * cms[2i]   === 0
        // (1 - active[i]) * cms[2i+1] === 0
        (1 - active[i]) * cms[2 * i]     === 0;
        (1 - active[i]) * cms[2 * i + 1] === 0;
    }

    // -------------------------------------------------------------------------
    // 4. Sequential pair-inserts with multiplexed frontier and root.
    //
    //    For pair i: insert cms[2i] at start_index+2i, then cms[2i+1] at
    //    start_index+2i+1, threading the frontier. The "active" mux gates
    //    whether this pair's outputs propagate.
    // -------------------------------------------------------------------------
    var BITS = 2 * DEPTH;

    // Pre-declare arrays — Circom 2.x disallows in-loop signal decls.
    component idxA_bits[MAX_N];
    component idxB_bits[MAX_N];
    signal idxA_dig[MAX_N][DEPTH];
    signal idxB_dig[MAX_N][DEPTH];

    component insA[MAX_N];
    component insB[MAX_N];

    // Running tree state. fr[i][lvl][s] is the frontier after pair i; fr[0]
    // is frontier_in. running_root[i] is the root after pair i; running_root[0]
    // would be the root of the empty / pre-batch tree, but we never read it
    // for unmuxed values. We initialize running_root[0] to old_root for clean
    // reasoning, even though the constraint-system view doesn't tie it.
    signal fr[MAX_N + 1][DEPTH][3];
    signal running_root[MAX_N + 1];

    for (var lvl = 0; lvl < DEPTH; lvl++) {
        for (var s = 0; s < 3; s++) {
            fr[0][lvl][s] <== frontier_in[lvl][s];
        }
    }
    running_root[0] <== old_root;

    // Per-pair muxed frontier / root tmp signals
    signal mux_fr_a[MAX_N][DEPTH][3];
    signal mux_fr_b[MAX_N][DEPTH][3];
    signal mux_root_a[MAX_N];
    signal mux_root_b[MAX_N];

    for (var i = 0; i < MAX_N; i++) {
        // Range checks: indices fit in 2*DEPTH bits.
        idxA_bits[i] = Num2Bits(BITS);
        idxA_bits[i].in <== start_index + 2 * i;
        idxB_bits[i] = Num2Bits(BITS);
        idxB_bits[i].in <== start_index + 2 * i + 1;

        for (var d = 0; d < DEPTH; d++) {
            idxA_dig[i][d] <== idxA_bits[i].out[2 * d] + 2 * idxA_bits[i].out[2 * d + 1];
            idxB_dig[i][d] <== idxB_bits[i].out[2 * d] + 2 * idxB_bits[i].out[2 * d + 1];
        }

        // First insert in pair: cms[2i] over fr[i].
        insA[i] = QuaternaryInsert(DEPTH);
        insA[i].leaf <== cms[2 * i];
        for (var d = 0; d < DEPTH; d++) {
            insA[i].idx_digit[d] <== idxA_dig[i][d];
            for (var s = 0; s < 3; s++) {
                insA[i].frontier_in[d][s] <== fr[i][d][s];
            }
        }

        // Second insert in pair: cms[2i+1] over insA's frontier_out.
        insB[i] = QuaternaryInsert(DEPTH);
        insB[i].leaf <== cms[2 * i + 1];
        for (var d = 0; d < DEPTH; d++) {
            insB[i].idx_digit[d] <== idxB_dig[i][d];
            for (var s = 0; s < 3; s++) {
                insB[i].frontier_in[d][s] <== insA[i].frontier_out[d][s];
            }
        }

        // Multiplex: if active[i] == 1 use insB outputs, else carry fr[i] / running_root[i].
        for (var d = 0; d < DEPTH; d++) {
            for (var s = 0; s < 3; s++) {
                mux_fr_a[i][d][s] <== active[i] * insB[i].frontier_out[d][s];
                mux_fr_b[i][d][s] <== (1 - active[i]) * fr[i][d][s];
                fr[i + 1][d][s]   <== mux_fr_a[i][d][s] + mux_fr_b[i][d][s];
            }
        }

        mux_root_a[i]       <== active[i] * insB[i].root;
        mux_root_b[i]       <== (1 - active[i]) * running_root[i];
        running_root[i + 1] <== mux_root_a[i] + mux_root_b[i];
    }

    // -------------------------------------------------------------------------
    // 5. Bind public new_root.
    // -------------------------------------------------------------------------
    new_root === running_root[MAX_N];

    // -------------------------------------------------------------------------
    // 6. PolyEval compression.
    //    Layout: [old_root, new_root, start_index, actual_count, cms[0..2*MAX_N-1]]
    //    Total = 4 + 2*MAX_N coefficients (36 for MAX_N=16).
    //    MUST match contracts/src/lib/PubInputs.sol :: TreeUpdateBatch.compress.
    // -------------------------------------------------------------------------
    var TOTAL = 4 + 2 * MAX_N;
    component pe = PolyEval(TOTAL);
    pe.coeffs[0] <== old_root;
    pe.coeffs[1] <== new_root;
    pe.coeffs[2] <== start_index;
    pe.coeffs[3] <== actual_count;
    for (var i = 0; i < 2 * MAX_N; i++) {
        pe.coeffs[4 + i] <== cms[i];
    }
    pe.z <== z;
    y <== pe.y;
}

// DEPTH = 10 (matches tree_update.circom and on-chain CommitmentTree).
// MAX_N = 16 (32 leaves per batch; one Permit2 sig per pair).
component main {
    public [ z ]
} = TreeUpdateBatch(10, 16);
