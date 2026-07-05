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

// TreeUpdateBatch: relayer proof advancing the tree old_root → new_root by
// inserting up to MAX_N leaf pairs at [start_index, start_index+2·MAX_N).
//
// actual_count ∈ [1, MAX_N] selects active pairs; trailing slots must be zero.
// leaf_j = Poseidon(TAG_LEAF, cms[j], cv_dep[j][0], cv_dep[j][1]). cv_dep is the
// depositor/spender Pedersen commitment; spends recompute the same leaf in
// spent.circom, so (asset, value) cannot be substituted.
//
// Per-pair deposit binding (is_deposit[i] == 1):
//   cv_dep[2i] + cv_dep[2i+1] == pair_public_in[i]·V^pair_asset[i] + rcv_total[i]·H
// Deposits run no transact SNARK; this aggregate pins both leaves to
// (pair_asset, pair_public_in). is_deposit == 0 skips it (spend conservation
// proved by 2x2's balance circuit).
//
// PI compression — layout (MUST match PubInputs.sol :: compress(TreeUpdateBatch)):
//   [0]                                       old_root
//   [1]                                       new_root
//   [2]                                       start_index
//   [3]                                       actual_count
//   [4 .. 3 + 2·MAX_N]                        cms
//   [4 + 2·MAX_N .. 3 + 6·MAX_N]              cv_dep_flat = (x0,y0,x1,y1,...)
//   [4 + 6·MAX_N .. 3 + 7·MAX_N]              pair_asset
//   [4 + 7·MAX_N .. 3 + 8·MAX_N]              pair_public_in
//   [4 + 8·MAX_N .. 3 + 9·MAX_N]              is_deposit
// Total = 4 + 9·MAX_N (= 76 for MAX_N=8).
//
// Caller MUST ensure start_index + 2·MAX_N - 1 < 4^DEPTH.
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

    // 1. Range-check actual_count ∈ [1, MAX_N] via Num2Bits(actual_count - 1).
    var COUNT_BITS = 3;
    // Range-check below gives actual_count ∈ [1, 2^COUNT_BITS]; require the bound
    // tight to MAX_N (else actual_count could exceed MAX_N for non-power-of-2).
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

    // 3. Zero all fields of inactive pairs. cv_dep feeds PolyEval, so without
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
    }

    // 4. Booleanize is_deposit[i]; zero deposit-only fields on spend pairs so a
    //    relayer cannot smuggle nonzero pair_asset/pair_public_in into the PI.
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

    // 5b. cv_dep points MUST lie on Baby-Jubjub. For deposits this is the sole
    //     cv_dep constraint; an off-curve point satisfies the sum binding but
    //     yields a note no (on-curve) ValueCommit can respend. Inactive slots
    //     hold (0,0) (off-curve), so add (1 - active) to y → checks as (0,1).
    component cv_on_curve[2 * MAX_N];
    for (var i = 0; i < MAX_N; i++) {
        for (var j = 0; j < 2; j++) {
            var k = 2 * i + j;
            cv_on_curve[k] = BabyCheck();
            cv_on_curve[k].x <== cv_dep[k][0];
            cv_on_curve[k].y <== cv_dep[k][1] + (1 - active[i]);
        }
    }

    // 6. Per-pair deposit binding (gated by active[i] · is_deposit[i]):
    //      cv_dep[2i] + cv_dep[2i+1] == pair_public_in[i]·V^asset[i] + rcv_total[i]·H
    component asset_gen[MAX_N];
    component pub_in_rng[MAX_N];
    component pub_in_mul[MAX_N];
    component rH_mul[MAX_N];
    component sum_vc[MAX_N];
    component expected[MAX_N];
    signal active_dep[MAX_N];
    for (var i = 0; i < MAX_N; i++) {
        active_dep[i] <== active[i] * is_deposit[i];

        asset_gen[i] = HashToAssetGen();
        asset_gen[i].asset_id <== pair_asset[i];

        // pair_public_in · V^asset
        pub_in_rng[i] = RangeCheck64();
        pub_in_rng[i].v <== pair_public_in[i];

        pub_in_mul[i] = ValueScalarMul();
        for (var b = 0; b < 64; b++) {
            pub_in_mul[i].bits[b] <== pub_in_rng[i].bits[b];
        }
        pub_in_mul[i].gen[0] <== asset_gen[i].gen[0];
        pub_in_mul[i].gen[1] <== asset_gen[i].gen[1];

        // rcv_total · H
        rH_mul[i] = MulH();
        rH_mul[i].scalar <== rcv_total[i];

        // expected = pub_in·V^asset + rcv_total·H
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

        // active_dep · (sum_vc - expected) === 0 per coord.
        active_dep[i] * (sum_vc[i].xout - expected[i].xout) === 0;
        active_dep[i] * (sum_vc[i].yout - expected[i].yout) === 0;
    }

    // 7. Bind frontier_in to old_root via FrontierRoot.
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

    // 8. Sequential pair-inserts. active[i] muxes whether the pair propagates.

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

    // Muxed frontier / root tmps.
    signal mux_fr_a[MAX_N][DEPTH][3];
    signal mux_fr_b[MAX_N][DEPTH][3];
    signal mux_root_a[MAX_N];
    signal mux_root_b[MAX_N];

    for (var i = 0; i < MAX_N; i++) {
        // Index range checks (2·DEPTH bits).
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

        // active[i] ? insB outputs : carry forward.
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

    // 9. Bind new_root.
    new_root === running_root[MAX_N];

    // 10. PolyEval compression (see BatchCompress).
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

// TreeUpdateBatch(DEPTH=10, MAX_N=8):
//   DEPTH=10 must match 2x2.circom and on-chain CommitmentTree.
//   MAX_N=8 → ≤16 leaves/batch (sized for ptau_20 headroom).
// Changing either needs a ceremony + contract change (PI layout = 4 + 9·MAX_N).
component main {
    public [ z ]
} = TreeUpdateBatch(10, 8);
