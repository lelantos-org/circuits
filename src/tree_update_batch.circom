pragma circom 2.2.3;

include "lib/insert.circom";
include "lib/poly_eval.circom";
include "lib/tags.circom";
include "lib/asset_gen.circom";
include "lib/value_commit.circom";
include "lib/balance.circom";
include "lib/frontier_root.circom";
include "../node_modules/circomlib/circuits/poseidon.circom";
include "../node_modules/circomlib/circuits/babyjub.circom";
include "../node_modules/circomlib/circuits/bitify.circom";
include "../node_modules/circomlib/circuits/comparators.circom";

// TreeUpdateBatch: relayer-side proof that the canonical commitment tree
// advances from `old_root` to `new_root` by inserting up to MAX_N pairs of
// leaves at indices [start_index, start_index+1, ..., start_index+2*MAX_N-1]
// over a relayer-supplied frontier.
//
// `actual_count` selects how many pairs are real (1 ≤ actual_count ≤ MAX_N).
// Trailing slots (i ≥ actual_count) are non-active: their cms / cv_deps must
// be zero and they do not advance the running root or frontier.
//
// PER-LEAF FORMAT:
//   leaf_j = Poseidon(TAG_LEAF, cms[j], cv_dep[j][0], cv_dep[j][1])
//
// `cv_dep[j]` is the depositor- (or spender-) anchored Pedersen value
// commitment for the note at slot j. Spends recompute this leaf in
// spent.circom from the same (asset, value, rcv_dep) used to bind the cm
// preimage, so substituting the (asset, value) at spend time is impossible.
//
// PER-PAIR DEPOSIT BINDING (gated by `is_deposit[i] = 1`):
//   cv_dep[2i] + cv_dep[2i+1]  ==  pair_public_in[i] · V^pair_asset[i]
//                                  + rcv_total[i] · H
//
// where V^pair_asset[i] = HashToAssetGen(pair_asset[i]). This is the load-
// bearing C-1 fix: the deposit path runs no transact SNARK, so the per-pair
// Pedersen aggregate forces (asset_j, value_j) for every leaf in the pair to
// sum to (pair_asset[i], pair_public_in[i]). Independence of asset
// generators rules out cross-asset substitution.
//
// `is_deposit[i] = 0` skips the aggregate (used by spend's tree update where
// the two output notes may have differing per-output (asset, value) and the
// 2x2 balance circuit already proves conservation).
//
// PI compression mirrors prior tree_update.circom: logical PIs folded into
// (z, y) via PolyEval. Coefficient ordering MUST match the contract's
// PubInputs.TreeUpdateBatch::compress order:
//
//   [0]                                       old_root
//   [1]                                       new_root
//   [2]                                       start_index
//   [3]                                       actual_count
//   [4 .. 3 + 2*MAX_N]                        cms[0 .. 2*MAX_N - 1]
//   [4 + 2*MAX_N .. 3 + 4*MAX_N]              cv_dep_x[0..2*MAX_N-1] interleaved with y
//                                              i.e. cv_dep_flat[0..4*MAX_N-1] = (x0,y0,x1,y1,...)
//   [4 + 6*MAX_N .. 3 + 7*MAX_N]              pair_asset[0 .. MAX_N - 1]
//   [4 + 7*MAX_N .. 3 + 8*MAX_N]              pair_public_in[0 .. MAX_N - 1]
//   [4 + 8*MAX_N .. 3 + 9*MAX_N]              is_deposit[0 .. MAX_N - 1]
//
// Total = 4 + 9*MAX_N coefficients (= 76 for MAX_N=8).
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
    signal input cv_dep[2 * MAX_N][2];    // per-cm Pedersen value commitment (padding zero)
    signal input pair_asset[MAX_N];       // per-pair publicAssetId (deposit only; padding 0)
    signal input pair_public_in[MAX_N];   // per-pair publicIn (deposit only; padding 0)
    signal input is_deposit[MAX_N];       // 0/1 per pair; 1 = deposit-mode aggregate check

    // ===== PRIVATE =====
    signal input frontier_in[DEPTH][3];
    signal input rcv_total[MAX_N];        // = rcv_dep_0 + rcv_dep_1 per pair (deposit only)

    // -------------------------------------------------------------------------
    // 1. Range-check actual_count ∈ [1, MAX_N].
    //    Decompose (actual_count - 1) in COUNT_BITS bits where 2^COUNT_BITS ≥ MAX_N.
    //    For MAX_N = 8 → COUNT_BITS = 3 → bounds (actual_count - 1) ∈ [0, 7]
    //    → actual_count ∈ [1, 8].
    // -------------------------------------------------------------------------
    var COUNT_BITS = 3;
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
    // 3. Padding constraints: if !active[i], all per-pair fields must be zero.
    //    cms / cv_dep zeroed per inactive pair. pair_asset / pair_public_in /
    //    is_deposit / rcv_total also zero (padding cannot smuggle aggregate
    //    constraints into inactive slots).
    // -------------------------------------------------------------------------
    for (var i = 0; i < MAX_N; i++) {
        (1 - active[i]) * cms[2 * i]     === 0;
        (1 - active[i]) * cms[2 * i + 1] === 0;
        (1 - active[i]) * cv_dep[2 * i][0]     === 0;
        (1 - active[i]) * cv_dep[2 * i][1]     === 0;
        (1 - active[i]) * cv_dep[2 * i + 1][0] === 0;
        (1 - active[i]) * cv_dep[2 * i + 1][1] === 0;
        (1 - active[i]) * pair_asset[i]        === 0;
        (1 - active[i]) * pair_public_in[i]    === 0;
        (1 - active[i]) * is_deposit[i]        === 0;
        (1 - active[i]) * rcv_total[i]         === 0;
    }

    // -------------------------------------------------------------------------
    // 4. is_deposit[i] is boolean (0 or 1). Booleanize via x*(1-x) === 0.
    // -------------------------------------------------------------------------
    for (var i = 0; i < MAX_N; i++) {
        is_deposit[i] * (1 - is_deposit[i]) === 0;
    }

    // -------------------------------------------------------------------------
    // 5. Compute leaf_j = Poseidon(TAG_LEAF, cm_j, cv_dep_j_x, cv_dep_j_y).
    //    Domain-separated from NoteCommitment by TAG_LEAF=10 vs packed_av≥2^64.
    // -------------------------------------------------------------------------
    component leaf_h[2 * MAX_N];
    signal leaves[2 * MAX_N];
    for (var k = 0; k < 2 * MAX_N; k++) {
        leaf_h[k] = Poseidon(4);
        leaf_h[k].inputs[0] <== TAG_LEAF();
        leaf_h[k].inputs[1] <== cms[k];
        leaf_h[k].inputs[2] <== cv_dep[k][0];
        leaf_h[k].inputs[3] <== cv_dep[k][1];
        leaves[k] <== leaf_h[k].out;
    }

    // -------------------------------------------------------------------------
    // 6. Per-pair deposit binding: enforce Pedersen aggregate when active and
    //    is_deposit[i] == 1. C-1 closure: forces (asset_j, value_j) of both
    //    output cms in the pair to satisfy
    //       Σ value_j · V^pair_asset = pair_public_in · V^pair_asset
    //    (independence of asset generators rules out cross-asset).
    //
    //    Soundness rests on:
    //      - HashToAssetGen producing independent generators per asset_id
    //        (already an existing assumption underpinning PerAssetPointBalance).
    //      - H = BASE[2] independent of every V^t (already documented in
    //        value_commit.circom).
    //      - Pedersen binding on (value, asset_id): given fixed cv_dep_total,
    //        knowing two openings with distinct (asset, value) pairs implies
    //        a discrete-log relation between V^pair_asset and H.
    // -------------------------------------------------------------------------
    component asset_gen[MAX_N];
    component pub_in_rng[MAX_N];
    component pub_in_mul[MAX_N];
    component rH_mul[MAX_N];
    component sum_vc[MAX_N];
    component expected[MAX_N];
    signal active_dep[MAX_N];
    for (var i = 0; i < MAX_N; i++) {
        // active && is_deposit -- only when both are 1, the aggregate is enforced
        active_dep[i] <== active[i] * is_deposit[i];

        // V^asset = HashToAssetGen(pair_asset[i])
        asset_gen[i] = HashToAssetGen();
        asset_gen[i].asset_id <== pair_asset[i];

        // pair_public_in[i] · V^asset (range-check + scalar mul)
        pub_in_rng[i] = RangeCheck64();
        pub_in_rng[i].v <== pair_public_in[i];

        pub_in_mul[i] = ValueScalarMul();
        for (var b = 0; b < 64; b++) {
            pub_in_mul[i].bits[b] <== pub_in_rng[i].bits[b];
        }
        pub_in_mul[i].gen[0] <== asset_gen[i].gen[0];
        pub_in_mul[i].gen[1] <== asset_gen[i].gen[1];

        // rcv_total[i] · H
        rH_mul[i] = MulH();
        rH_mul[i].scalar <== rcv_total[i];

        // expected = pair_public_in · V^asset + rcv_total · H
        expected[i] = BabyAdd();
        expected[i].x1 <== pub_in_mul[i].out[0];
        expected[i].y1 <== pub_in_mul[i].out[1];
        expected[i].x2 <== rH_mul[i].out[0];
        expected[i].y2 <== rH_mul[i].out[1];

        // sum_vc = cv_dep[2i] + cv_dep[2i+1]
        sum_vc[i] = BabyAdd();
        sum_vc[i].x1 <== cv_dep[2 * i][0];
        sum_vc[i].y1 <== cv_dep[2 * i][1];
        sum_vc[i].x2 <== cv_dep[2 * i + 1][0];
        sum_vc[i].y2 <== cv_dep[2 * i + 1][1];

        // active_dep * (sum_vc - expected) === 0  (per coordinate)
        active_dep[i] * (sum_vc[i].xout - expected[i].xout) === 0;
        active_dep[i] * (sum_vc[i].yout - expected[i].yout) === 0;
    }

    // -------------------------------------------------------------------------
    // 7. Bind frontier_in to old_root  (SOUNDNESS-CRITICAL).
    //
    //    Without this binding `frontier_in` is unconstrained: a malicious
    //    relayer passes `oldRoot == currentRoot()` on chain while supplying
    //    a forged frontier, then `new_root` (derived from that frontier +
    //    honest leaves) overwrites `currentRoot` with a state no honest
    //    user can extend ⇒ permanent pool-wide DoS.
    //
    //    Defense: recompute old_root inside the SNARK from frontier_in +
    //    start_index digits (== on-chain `committedCount`) and assert
    //    equality. See lib/frontier_root.circom.
    // -------------------------------------------------------------------------
    var BITS = 2 * DEPTH;
    component start_index_bits = Num2Bits(BITS);
    start_index_bits.in <== start_index;

    component frontier_root = FrontierRoot(DEPTH);
    for (var k = 0; k < BITS; k++) {
        frontier_root.start_index_bits[k] <== start_index_bits.out[k];
    }
    for (var d = 0; d < DEPTH; d++) {
        for (var s = 0; s < 3; s++) {
            frontier_root.frontier_in[d][s] <== frontier_in[d][s];
        }
    }
    old_root === frontier_root.root;

    // -------------------------------------------------------------------------
    // 8. Sequential pair-inserts with multiplexed frontier and root.
    //
    //    For pair i: insert leaves[2i] at start_index+2i, then leaves[2i+1]
    //    at start_index+2i+1, threading the frontier. The "active" mux gates
    //    whether this pair's outputs propagate.
    // -------------------------------------------------------------------------

    // Pre-declare arrays — Circom 2.x disallows in-loop signal decls.
    component idxA_bits[MAX_N];
    component idxB_bits[MAX_N];
    signal idxA_dig[MAX_N][DEPTH];
    signal idxB_dig[MAX_N][DEPTH];

    component insA[MAX_N];
    component insB[MAX_N];

    // Running tree state. fr[i][lvl][s] is the frontier after pair i;
    // fr[0] == frontier_in. running_root[i] is the root after pair i;
    // running_root[0] := old_root (now soundly bound via FrontierRoot in
    // section 7) and is read only by the inactive-pair mux.
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

        // First insert in pair: leaves[2i] over fr[i].
        insA[i] = QuaternaryInsert(DEPTH);
        insA[i].leaf <== leaves[2 * i];
        for (var d = 0; d < DEPTH; d++) {
            insA[i].idx_digit[d] <== idxA_dig[i][d];
            for (var s = 0; s < 3; s++) {
                insA[i].frontier_in[d][s] <== fr[i][d][s];
            }
        }

        // Second insert in pair: leaves[2i+1] over insA's frontier_out.
        insB[i] = QuaternaryInsert(DEPTH);
        insB[i].leaf <== leaves[2 * i + 1];
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
    // 9. Bind public new_root.
    // -------------------------------------------------------------------------
    new_root === running_root[MAX_N];

    // -------------------------------------------------------------------------
    // 10. PolyEval compression. Coefficient layout MUST match
    //    contracts/src/lib/PubInputs.sol :: TreeUpdateBatch.compress order.
    //    Total = 4 + 9*MAX_N coefficients.
    // -------------------------------------------------------------------------
    var TOTAL = 4 + 9 * MAX_N;
    component pe = PolyEval(TOTAL);
    pe.coeffs[0] <== old_root;
    pe.coeffs[1] <== new_root;
    pe.coeffs[2] <== start_index;
    pe.coeffs[3] <== actual_count;
    var off = 4;
    for (var i = 0; i < 2 * MAX_N; i++) {
        pe.coeffs[off + i] <== cms[i];
    }
    off = off + 2 * MAX_N;
    for (var i = 0; i < 2 * MAX_N; i++) {
        pe.coeffs[off + 2 * i + 0] <== cv_dep[i][0];
        pe.coeffs[off + 2 * i + 1] <== cv_dep[i][1];
    }
    off = off + 4 * MAX_N;
    for (var i = 0; i < MAX_N; i++) {
        pe.coeffs[off + i] <== pair_asset[i];
    }
    off = off + MAX_N;
    for (var i = 0; i < MAX_N; i++) {
        pe.coeffs[off + i] <== pair_public_in[i];
    }
    off = off + MAX_N;
    for (var i = 0; i < MAX_N; i++) {
        pe.coeffs[off + i] <== is_deposit[i];
    }
    pe.z <== z;
    y <== pe.y;
}

// DEPTH = 10 (matches on-chain CommitmentTree).
// MAX_N = 8 (16 leaves per batch; halved from 16 to amortize prover cost
// with the new Pedersen-aggregate constraints + free up ptau headroom).
component main {
    public [ z ]
} = TreeUpdateBatch(10, 8);
