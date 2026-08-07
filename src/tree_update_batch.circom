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

// Relayer proof advancing the commitment tree from old_root to new_root by
// inserting up to MAX_N leaf pairs at [start_index, start_index + 2·MAX_N).
//
// actual_count ∈ [1, MAX_N] selects the active pairs; trailing slots must be zero.
// leaf_j = Poseidon(TAG_LEAF, cms[j], cv_dep[j][0], cv_dep[j][1]), where cv_dep is
// the depositor's or spender's Pedersen value commitment. Spends recompute the
// same leaf in spent.circom, so (asset, value) cannot be substituted later.
//
// Per-pair deposit binding, applied when is_deposit[i] == 1:
//   cv_dep[2i+1] == rcv_dep_pad[i]·H                                (pad, value 0)
//   cv_dep[2i] + cv_dep[2i+1] == pair_public_in[i]·V^pair_asset[i] + rcv_total[i]·H
//
// Deposits carry no transact proof, so both leaves must be pinned individually.
// The sum alone fixes only Σvalue modulo the subgroup order: a depositor could
// set cv_dep[2i] = 2^63·V^A + r0·H, let cv_dep[2i+1] absorb
// (pair_public_in − 2^63) mod l as an unspendable leaf they abandon, and walk
// away with a valid 2^63 note for a one-unit deposit. Forcing the pad leaf to
// value 0 makes cv_dep[2i] exactly pair_public_in·V^asset +
// (rcv_total − rcv_dep_pad)·H, so no split is free.
//
// is_deposit[i] == 0 skips both checks; the transact circuit proves conservation
// for spends.
//
// PolyEval coefficient layout, which must match
// PubInputs.sol :: compress(TreeUpdateBatch):
//   [0]                            old_root
//   [1]                            new_root
//   [2]                            start_index
//   [3]                            actual_count
//   [4 .. 3 + 2·MAX_N]             cms
//   [4 + 2·MAX_N .. 3 + 6·MAX_N]   cv_dep flattened as (x0, y0, x1, y1, ...)
//   [4 + 6·MAX_N .. 3 + 7·MAX_N]   pair_asset
//   [4 + 7·MAX_N .. 3 + 8·MAX_N]   pair_public_in
//   [4 + 8·MAX_N .. 3 + 9·MAX_N]   is_deposit
// Total = 4 + 9·MAX_N (76 for MAX_N = 8).
//
// The caller must ensure start_index + 2·MAX_N - 1 < 4^DEPTH.
template TreeUpdateBatch(DEPTH, MAX_N) {
    // ===== PUBLIC =====
    signal input  z;
    signal output y;

    // ===== LOGICAL PUBLIC INPUTS =====
    signal input old_root;
    signal input new_root;
    signal input start_index;
    signal input actual_count;            // 1..MAX_N
    signal input cms[2 * MAX_N];          // padding (i >= 2·actual_count) must be 0
    signal input cv_dep[2 * MAX_N][2];    // per-cm value commitment; padding zero
    signal input pair_asset[MAX_N];       // per-pair publicAssetId; deposits only
    signal input pair_public_in[MAX_N];   // per-pair publicIn; deposits only
    signal input is_deposit[MAX_N];       // 1 enables the deposit binding checks

    // ===== PRIVATE =====
    signal input frontier_in[DEPTH][3];
    signal input rcv_total[MAX_N];        // rcv_dep_0 + rcv_dep_1 per pair
    signal input rcv_dep_pad[MAX_N];      // rcv_dep of the pad leaf 2i+1

    // 1. Range-check actual_count ∈ [1, MAX_N] via Num2Bits(actual_count - 1).
    //    That bounds it by 2^COUNT_BITS, so the bound must be tight to MAX_N.
    var COUNT_BITS = 3;
    assert((1 << COUNT_BITS) == MAX_N);
    component cnt_bits = Num2Bits(COUNT_BITS);
    cnt_bits.in <== actual_count - 1;

    // 2. active[i] = (i < actual_count).
    component lt[MAX_N];
    signal active[MAX_N];
    for (var i = 0; i < MAX_N; i++) {
        lt[i] = LessThan(COUNT_BITS + 1);
        lt[i].in[0] <== i;
        lt[i].in[1] <== actual_count;
        active[i] <== lt[i].out;
    }

    // 3. Zero every field of an inactive pair. cv_dep feeds PolyEval, so without
    //    this a prover could inject arbitrary cv_dep into inactive slots.
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
        (1 - active[i]) * rcv_dep_pad[i]       === 0;
    }

    // 4. Booleanize is_deposit[i] and zero the deposit-only fields on spend pairs,
    //    so a relayer cannot smuggle a nonzero pair_asset / pair_public_in into
    //    the public inputs.
    for (var i = 0; i < MAX_N; i++) {
        is_deposit[i] * (1 - is_deposit[i]) === 0;
        (1 - is_deposit[i]) * pair_asset[i]     === 0;
        (1 - is_deposit[i]) * pair_public_in[i] === 0;
    }

    // 5. leaf_j = Poseidon(TAG_LEAF, cm_j, cv_dep_j_x, cv_dep_j_y).
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

    // 6. cv_dep points must lie on Baby-Jubjub. For deposits this is the only
    //    per-point cv_dep constraint: an off-curve point satisfies the sum binding
    //    but produces a note no on-curve ValueCommit can respend. Inactive slots
    //    hold (0, 0), which is off-curve, so (1 - active) shifts y to check (0, 1).
    component cv_on_curve[2 * MAX_N];
    for (var i = 0; i < MAX_N; i++) {
        for (var j = 0; j < 2; j++) {
            var k = 2 * i + j;
            cv_on_curve[k] = BabyCheck();
            cv_on_curve[k].x <== cv_dep[k][0];
            cv_on_curve[k].y <== cv_dep[k][1] + (1 - active[i]);
        }
    }

    // 7. Per-pair deposit binding, gated by active[i]·is_deposit[i]. Together the
    //    two equalities pin cv_dep[2i] to exactly pair_public_in units of
    //    pair_asset; see the header for why the sum alone is insufficient.
    component asset_gen[MAX_N];
    component pub_in_mul[MAX_N];
    component rH_mul[MAX_N];
    component pad_rH_mul[MAX_N];
    component sum_vc[MAX_N];
    component expected[MAX_N];
    signal active_dep[MAX_N];
    for (var i = 0; i < MAX_N; i++) {
        active_dep[i] <== active[i] * is_deposit[i];

        asset_gen[i] = HashToAssetGen();
        asset_gen[i].asset_id <== pair_asset[i];

        // pair_public_in · V^asset, with pair_public_in range-checked to 64 bits.
        pub_in_mul[i] = ValueTimesGen();
        pub_in_mul[i].value  <== pair_public_in[i];
        pub_in_mul[i].gen[0] <== asset_gen[i].gen[0];
        pub_in_mul[i].gen[1] <== asset_gen[i].gen[1];

        // expected = pair_public_in·V^asset + rcv_total·H
        rH_mul[i] = MulH();
        rH_mul[i].scalar <== rcv_total[i];

        expected[i] = BabyAdd();
        expected[i].x1 <== pub_in_mul[i].out[0];
        expected[i].y1 <== pub_in_mul[i].out[1];
        expected[i].x2 <== rH_mul[i].out[0];
        expected[i].y2 <== rH_mul[i].out[1];

        sum_vc[i] = BabyAdd();
        sum_vc[i].x1 <== cv_dep[2 * i][0];
        sum_vc[i].y1 <== cv_dep[2 * i][1];
        sum_vc[i].x2 <== cv_dep[2 * i + 1][0];
        sum_vc[i].y2 <== cv_dep[2 * i + 1][1];

        active_dep[i] * (sum_vc[i].xout - expected[i].xout) === 0;
        active_dep[i] * (sum_vc[i].yout - expected[i].yout) === 0;

        // Pad leaf commits to value 0: cv_dep[2i+1] == rcv_dep_pad[i]·H.
        pad_rH_mul[i] = MulH();
        pad_rH_mul[i].scalar <== rcv_dep_pad[i];
        active_dep[i] * (cv_dep[2 * i + 1][0] - pad_rH_mul[i].out[0]) === 0;
        active_dep[i] * (cv_dep[2 * i + 1][1] - pad_rH_mul[i].out[1]) === 0;
    }

    // 8. Bind frontier_in to old_root.
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

    // 9. Sequential pair inserts; active[i] selects whether the pair propagates.
    component idxA_bits[MAX_N];
    component idxB_bits[MAX_N];
    signal idxA_dig[MAX_N][DEPTH];
    signal idxB_dig[MAX_N][DEPTH];

    component insA[MAX_N];
    component insB[MAX_N];

    // Running state: fr[0] = frontier_in, running_root[0] = old_root.
    signal fr[MAX_N + 1][DEPTH][3];
    signal running_root[MAX_N + 1];

    for (var lvl = 0; lvl < DEPTH; lvl++) {
        for (var s = 0; s < 3; s++) {
            fr[0][lvl][s] <== frontier_in[lvl][s];
        }
    }
    running_root[0] <== old_root;

    signal mux_fr_a[MAX_N][DEPTH][3];
    signal mux_fr_b[MAX_N][DEPTH][3];
    signal mux_root_a[MAX_N];
    signal mux_root_b[MAX_N];

    for (var i = 0; i < MAX_N; i++) {
        // Insertion indices, range-checked to 2·DEPTH bits.
        idxA_bits[i] = Num2Bits(BITS);
        idxA_bits[i].in <== start_index + 2 * i;
        idxB_bits[i] = Num2Bits(BITS);
        idxB_bits[i].in <== start_index + 2 * i + 1;

        for (var d = 0; d < DEPTH; d++) {
            idxA_dig[i][d] <== idxA_bits[i].out[2 * d] + 2 * idxA_bits[i].out[2 * d + 1];
            idxB_dig[i][d] <== idxB_bits[i].out[2 * d] + 2 * idxB_bits[i].out[2 * d + 1];
        }

        // Insert leaves[2i] over fr[i].
        insA[i] = QuaternaryInsert(DEPTH);
        insA[i].leaf <== leaves[2 * i];
        for (var d = 0; d < DEPTH; d++) {
            insA[i].idx_digit[d] <== idxA_dig[i][d];
            for (var s = 0; s < 3; s++) {
                insA[i].frontier_in[d][s] <== fr[i][d][s];
            }
        }

        // Insert leaves[2i+1] over insA's frontier.
        insB[i] = QuaternaryInsert(DEPTH);
        insB[i].leaf <== leaves[2 * i + 1];
        for (var d = 0; d < DEPTH; d++) {
            insB[i].idx_digit[d] <== idxB_dig[i][d];
            for (var s = 0; s < 3; s++) {
                insB[i].frontier_in[d][s] <== insA[i].frontier_out[d][s];
            }
        }

        // active[i] ? insB outputs : carry the previous state forward.
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

    // 10. Bind new_root.
    new_root === running_root[MAX_N];

    // 11. Public-input compression → (z, y).
    component pe = BatchCompress(MAX_N);
    pe.z <== z;
    pe.old_root <== old_root;
    pe.new_root <== new_root;
    pe.start_index <== start_index;
    pe.actual_count <== actual_count;
    for (var i = 0; i < 2 * MAX_N; i++) {
        pe.cms[i] <== cms[i];
        pe.cv_dep[i][0] <== cv_dep[i][0];
        pe.cv_dep[i][1] <== cv_dep[i][1];
    }
    for (var i = 0; i < MAX_N; i++) {
        pe.pair_asset[i] <== pair_asset[i];
        pe.pair_public_in[i] <== pair_public_in[i];
        pe.is_deposit[i] <== is_deposit[i];
    }
    y <== pe.y;
}

// DEPTH = 10 must match 2x2.circom and the on-chain CommitmentTree.
// MAX_N = 8 gives at most 16 leaves per batch, sized for ptau_20 headroom.
// Changing either requires a new ceremony and a contract change, since the
// public-input layout is 4 + 9·MAX_N.
component main {
    public [ z ]
} = TreeUpdateBatch(10, 8);
