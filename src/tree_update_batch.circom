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
// inserting up to MAX_L leaves at [start_index, start_index + MAX_L).
//
// actual_count ∈ [1, MAX_L] is a LEAF count, so odd counts are permitted: one
// batch carries either a 3-output transact bundle or a single-leaf deposit.
// Trailing slots must be zero.
//
// leaf_k = Poseidon(TAG_LEAF, cms[k], cv_dep[k][0], cv_dep[k][1]), where cv_dep
// is the depositor's or spender's Pedersen value commitment. Spends recompute
// the same leaf in spent.circom, so (asset, value) cannot be substituted later.
//
// Per-leaf deposit binding, applied when is_deposit[k] == 1:
//   cv_dep[k] == leaf_public_in[k]·V^leaf_asset[k] + rcv[k]·H
//
// Deposits carry no transact proof, so the batch circuit pins the leaf itself.
// The binding is per leaf rather than over an aggregate: a sum would fix only
// Σvalue modulo the subgroup order l, letting a depositor place 2^63·V^A in one
// leaf, absorb (public_in − 2^63) mod l in a second leaf they abandon, and
// retain a valid 2^63 note for a one-unit deposit. One equality per leaf admits
// no such split.
//
// is_deposit[k] == 0 skips the check; the transact circuit proves conservation
// for spends.
//
// PolyEval coefficient layout, which must match
// PubInputs.sol :: compress(TreeUpdateBatch):
//   [0]                            old_root
//   [1]                            new_root
//   [2]                            start_index
//   [3]                            actual_count
//   [4 .. 3 + MAX_L]               cms
//   [4 + MAX_L .. 3 + 3·MAX_L]     cv_dep flattened as (x0, y0, x1, y1, ...)
//   [4 + 3·MAX_L .. 3 + 4·MAX_L]   leaf_asset
//   [4 + 4·MAX_L .. 3 + 5·MAX_L]   leaf_public_in
//   [4 + 5·MAX_L .. 3 + 6·MAX_L]   is_deposit
// Total = 4 + 6·MAX_L (28 for MAX_L = 4).
//
// The caller must ensure start_index + MAX_L - 1 < 4^DEPTH.
template TreeUpdateBatch(DEPTH, MAX_L) {
    // ===== PUBLIC =====
    signal input  z;
    signal output y;

    // ===== LOGICAL PUBLIC INPUTS =====
    signal input old_root;
    signal input new_root;
    signal input start_index;
    signal input actual_count;            // 1..MAX_L, counted in leaves
    signal input cms[MAX_L];              // padding (k >= actual_count) must be 0
    signal input cv_dep[MAX_L][2];        // per-cm value commitment; padding zero
    signal input leaf_asset[MAX_L];       // per-leaf publicAssetId; deposits only
    signal input leaf_public_in[MAX_L];   // per-leaf publicIn; deposits only
    signal input is_deposit[MAX_L];       // 1 enables the deposit binding check

    // ===== PRIVATE =====
    signal input frontier_in[DEPTH][3];
    signal input rcv[MAX_L];              // rcv_dep of leaf k

    // 1. Range-check actual_count ∈ [1, MAX_L] via Num2Bits(actual_count - 1).
    //    That bounds it by 2^COUNT_BITS, so the bound must be tight to MAX_L.
    var COUNT_BITS = 2;
    assert((1 << COUNT_BITS) == MAX_L);
    component cnt_bits = Num2Bits(COUNT_BITS);
    cnt_bits.in <== actual_count - 1;

    // 2. active[k] = (k < actual_count).
    component lt[MAX_L];
    signal active[MAX_L];
    for (var k = 0; k < MAX_L; k++) {
        lt[k] = LessThan(COUNT_BITS + 1);
        lt[k].in[0] <== k;
        lt[k].in[1] <== actual_count;
        active[k] <== lt[k].out;
    }

    // 3. Zero every field of an inactive leaf. cv_dep feeds PolyEval, so without
    //    this a prover could inject arbitrary cv_dep into inactive slots.
    for (var k = 0; k < MAX_L; k++) {
        (1 - active[k]) * cms[k]            === 0;
        (1 - active[k]) * cv_dep[k][0]      === 0;
        (1 - active[k]) * cv_dep[k][1]      === 0;
        (1 - active[k]) * leaf_asset[k]     === 0;
        (1 - active[k]) * leaf_public_in[k] === 0;
        (1 - active[k]) * is_deposit[k]     === 0;
        (1 - active[k]) * rcv[k]            === 0;
    }

    // 4. Booleanize is_deposit[k] and zero the deposit-only fields on spend
    //    leaves, so a relayer cannot smuggle a nonzero leaf_asset /
    //    leaf_public_in into the public inputs.
    for (var k = 0; k < MAX_L; k++) {
        is_deposit[k] * (1 - is_deposit[k]) === 0;
        (1 - is_deposit[k]) * leaf_asset[k]     === 0;
        (1 - is_deposit[k]) * leaf_public_in[k] === 0;
    }

    // 5. leaf_k = Poseidon(TAG_LEAF, cm_k, cv_dep_k_x, cv_dep_k_y).
    component leaf_h[MAX_L];
    signal leaves[MAX_L];
    for (var k = 0; k < MAX_L; k++) {
        leaf_h[k] = Poseidon(4);
        leaf_h[k].inputs[0] <== TAG_LEAF();
        leaf_h[k].inputs[1] <== cms[k];
        leaf_h[k].inputs[2] <== cv_dep[k][0];
        leaf_h[k].inputs[3] <== cv_dep[k][1];
        leaves[k] <== leaf_h[k].out;
    }

    // 6. cv_dep points must lie on Baby-Jubjub. For spend leaves this is the
    //    only per-point cv_dep constraint here: an off-curve point produces a
    //    note no on-curve ValueCommit can respend. Inactive slots hold (0, 0),
    //    which is off-curve, so (1 - active) shifts y to check (0, 1).
    component cv_on_curve[MAX_L];
    for (var k = 0; k < MAX_L; k++) {
        cv_on_curve[k] = BabyCheck();
        cv_on_curve[k].x <== cv_dep[k][0];
        cv_on_curve[k].y <== cv_dep[k][1] + (1 - active[k]);
    }

    // 7. Per-leaf deposit binding, gated by active[k]·is_deposit[k]. The single
    //    equality pins cv_dep[k] to exactly leaf_public_in units of leaf_asset;
    //    see the header for why an aggregate over several leaves would not.
    component asset_gen[MAX_L];
    component pub_in_mul[MAX_L];
    component rH_mul[MAX_L];
    component expected[MAX_L];
    signal active_dep[MAX_L];
    for (var k = 0; k < MAX_L; k++) {
        active_dep[k] <== active[k] * is_deposit[k];

        asset_gen[k] = HashToAssetGen();
        asset_gen[k].asset_id <== leaf_asset[k];

        // leaf_public_in · V^asset, with leaf_public_in range-checked to 64 bits.
        pub_in_mul[k] = ValueTimesGen();
        pub_in_mul[k].value  <== leaf_public_in[k];
        pub_in_mul[k].gen[0] <== asset_gen[k].gen[0];
        pub_in_mul[k].gen[1] <== asset_gen[k].gen[1];

        // expected = leaf_public_in·V^asset + rcv·H
        rH_mul[k] = MulH();
        rH_mul[k].scalar <== rcv[k];

        expected[k] = BabyAdd();
        expected[k].x1 <== pub_in_mul[k].out[0];
        expected[k].y1 <== pub_in_mul[k].out[1];
        expected[k].x2 <== rH_mul[k].out[0];
        expected[k].y2 <== rH_mul[k].out[1];

        active_dep[k] * (cv_dep[k][0] - expected[k].xout) === 0;
        active_dep[k] * (cv_dep[k][1] - expected[k].yout) === 0;
    }

    // 8. Bind frontier_in to old_root.
    var BITS = 2 * DEPTH;
    component start_index_bits = Num2Bits(BITS);
    start_index_bits.in <== start_index;

    component frontier_root = FrontierRoot(DEPTH);
    for (var b = 0; b < BITS; b++) {
        frontier_root.start_index_bits[b] <== start_index_bits.out[b];
    }
    for (var d = 0; d < DEPTH; d++) {
        for (var s = 0; s < 3; s++) {
            frontier_root.frontier_in[d][s] <== frontier_in[d][s];
        }
    }
    old_root === frontier_root.root;

    // 9. Sequential single-leaf inserts; active[k] selects whether the leaf
    //    propagates.
    component idx_bits[MAX_L];
    signal idx_dig[MAX_L][DEPTH];

    component ins[MAX_L];

    // Running state: fr[0] = frontier_in, running_root[0] = old_root.
    signal fr[MAX_L + 1][DEPTH][3];
    signal running_root[MAX_L + 1];

    for (var lvl = 0; lvl < DEPTH; lvl++) {
        for (var s = 0; s < 3; s++) {
            fr[0][lvl][s] <== frontier_in[lvl][s];
        }
    }
    running_root[0] <== old_root;

    signal mux_fr_a[MAX_L][DEPTH][3];
    signal mux_fr_b[MAX_L][DEPTH][3];
    signal mux_root_a[MAX_L];
    signal mux_root_b[MAX_L];

    for (var k = 0; k < MAX_L; k++) {
        // Insertion index, range-checked to 2·DEPTH bits.
        idx_bits[k] = Num2Bits(BITS);
        idx_bits[k].in <== start_index + k;

        for (var d = 0; d < DEPTH; d++) {
            idx_dig[k][d] <== idx_bits[k].out[2 * d] + 2 * idx_bits[k].out[2 * d + 1];
        }

        // Insert leaves[k] over fr[k].
        ins[k] = QuaternaryInsert(DEPTH);
        ins[k].leaf <== leaves[k];
        for (var d = 0; d < DEPTH; d++) {
            ins[k].idx_digit[d] <== idx_dig[k][d];
            for (var s = 0; s < 3; s++) {
                ins[k].frontier_in[d][s] <== fr[k][d][s];
            }
        }

        // active[k] ? ins outputs : carry the previous state forward.
        for (var d = 0; d < DEPTH; d++) {
            for (var s = 0; s < 3; s++) {
                mux_fr_a[k][d][s] <== active[k] * ins[k].frontier_out[d][s];
                mux_fr_b[k][d][s] <== (1 - active[k]) * fr[k][d][s];
                fr[k + 1][d][s]   <== mux_fr_a[k][d][s] + mux_fr_b[k][d][s];
            }
        }

        mux_root_a[k]       <== active[k] * ins[k].root;
        mux_root_b[k]       <== (1 - active[k]) * running_root[k];
        running_root[k + 1] <== mux_root_a[k] + mux_root_b[k];
    }

    // 10. Bind new_root.
    new_root === running_root[MAX_L];

    // 11. Public-input compression → (y, z).
    component pe = BatchCompress(MAX_L);
    pe.z <== z;
    pe.old_root <== old_root;
    pe.new_root <== new_root;
    pe.start_index <== start_index;
    pe.actual_count <== actual_count;
    for (var k = 0; k < MAX_L; k++) {
        pe.cms[k] <== cms[k];
        pe.cv_dep[k][0] <== cv_dep[k][0];
        pe.cv_dep[k][1] <== cv_dep[k][1];
        pe.leaf_asset[k] <== leaf_asset[k];
        pe.leaf_public_in[k] <== leaf_public_in[k];
        pe.is_deposit[k] <== is_deposit[k];
    }
    y <== pe.y;
}

// DEPTH = 10 must match the transact circuits and the on-chain CommitmentTree.
//
// MAX_L = 4: 57,106 constraints, inside the 2^16 FFT domain and ptau_16, with
// 8,430 constraints of headroom. A leaf slot costs roughly 12k constraints, and
// `just budget` fails CI if the domain is crossed.
//
// MAX_L is at its floor. COUNT_BITS above requires a power of two, and a spend
// emits TRANSACT_OUT = 3 leaves that must fit one batch — MASP.sol pins
// `actualCount` to exactly that on the transfer path. Only flushBatch
// (deposits, one leaf each) uses more than 3 slots.
//
// Changing either parameter requires a new ceremony and a contract change,
// since the public-input layout is 4 + 6·MAX_L.
component main {
    public [ z ]
} = TreeUpdateBatch(10, 4);
