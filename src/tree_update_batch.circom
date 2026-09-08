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
// inserting actual_count leaves at start_index.
//
// actual_count is in [1, MAX_L] and counts leaves, so odd counts are permitted.
// One batch carries either a spend's N_OUT output leaves or a run of deposits,
// two leaves each. Trailing slots must be zero.
//
// leaf_k = Poseidon(TAG_LEAF, cms[k], cv_dep[k][0], cv_dep[k][1]), where cv_dep
// is the depositor's or spender's Pedersen value commitment. Spends recompute
// the same leaf in spent.circom, binding (asset, value) across the two proofs.
//
// Per-leaf deposit binding, applied when is_deposit[k] == 1:
//   cv_dep[k] == leaf_public_in[k]·V^leaf_asset[k] + rcv[k]·H
//
// Deposits carry no transact proof, so this circuit pins the leaf itself. The
// binding is per leaf rather than over an aggregate: a sum would fix only
// Σvalue modulo the subgroup order l, letting a depositor place 2^63·V^A in one
// leaf, absorb (public_in − 2^63) mod l in a second leaf they abandon, and keep
// a valid 2^63 note for a one-unit deposit. One equality per leaf admits no
// such split.
//
// The binding is not injective in (asset, value) on its own. HashToAssetGen is
// circomlib Pedersen over a 72-bit message, so V^a = m(a)·BASE0 for a publicly
// computable m(a) of about 2^85 (src/README.md § 5), and the equality pins the
// product value·m(asset) rather than the pair. Two registered ids whose
// multipliers share a large factor admit v·m(a) == v'·m(a') with both values
// inside the 64-bit range, letting a depositor pay v of the cheap asset while
// committing the depositor-chosen cms[k] to (a', v') and spending the leaf as
// the expensive one. The separation of the registered id set is what rules this
// out: `just asset-ids <ids>` computes the bound and must be run before
// registration, since AssetRegistry.addAsset accepts an arbitrary uint64.
//
// is_deposit[k] == 0 skips the binding; the transact circuit proves conservation
// for spends. Asset id 0 is rejected on a deposit leaf that carries value, since
// SpentNote refuses that id on every real note and the leaf would be
// unspendable; on a zero-value leaf it is instead REQUIRED, see step 7a.
//
// PolyEval coefficient layout. Must match
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
// Total = 4 + 6·MAX_L (52 for MAX_L = 8). The challenge preimage and the
// coefficient vector are the same words: every one is pinned, so every one is
// evaluated.
//
// The deposit-binding fields are NOT demoted to challenge-only. They are
// signals of this circuit, and hashing a signal into z binds nothing — the
// prover reads z before choosing a witness and may hand the verifier one that
// disagrees with the calldata z was hashed from. Only a constraint pins them;
// the deposit binding in step 7, and step 7a where it degenerates, are those
// constraints. See BatchCompress in lib/poly_eval.circom and src/README.md § 2a.
//
// Capacity: the per-slot index range check is gated on active[k], so the bound
// is start_index + actual_count - 1 < 4^DEPTH, over the leaves actually
// inserted.
//
// Soundness obligations left to the contract. FrontierRoot binds frontier_in to
// old_root but cannot bind start_index: a tree holding n leaves and one holding
// n leaves plus trailing empties have the same root, so a (frontier, root) pair
// is consistent with more than one index. The consumer must enforce, as MASP.sol
// does:
//
//   1. start_index == committedCount, the authoritative leaf count
//      (MASP._validateBatchHeader). Without it a relayer replays a valid batch
//      at a lower index and overwrites committed leaves.
//   2. actual_count pinned to the emitting operation, exactly TRANSACT_OUT
//      leaves on the spend path.
//   3. cms[k] and cv_dep[k] forwarded from the paired transact proof rather than
//      taken from the relayer, for every output slot of that spend.
//   4. is_deposit[k] pinned per active slot, not taken from the relayer: 1 on
//      every leaf of a deposit batch, 0 on every leaf of a spend batch. The
//      circuit constrains it only to be boolean, and it gates the deposit
//      binding, so a relayer that sets it to 0 on a deposit leaf inserts a leaf
//      whose cv_dep is bound to nothing but BabyCheck. MASP._drainDeposit and
//      MASP._validateRequest enforce this over every active slot.
//   5. publicIn != 0 on every principal deposit, so a leaf that carries value
//      also carries an asset the binding pins. The circuit does not require it:
//      it accepts a zero-value deposit leaf and canonicalises its leaf_asset to
//      0 (step 7a), which is sound because that asset reaches nothing. MASP
//      enforces it anyway via `MustHaveDeposit` in _validateDeposit.
//   6. leaf_asset[k] == 0 on every zero-value deposit leaf, matching step 7a.
//      MASP._drainDeposit sets it for the fee note it emits; a consumer that
//      forwards a non-zero asset on a worthless leaf produces a batch no prover
//      can satisfy.
//
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

    // 1. Range-check actual_count in [1, MAX_L] via Num2Bits(actual_count - 1),
    //    which bounds it by 2^COUNT_BITS. COUNT_BITS is derived from MAX_L so
    //    the two cannot diverge; the assert enforces the power-of-two
    //    requirement the derivation cannot.
    var COUNT_BITS = 0;
    var count_span = MAX_L;
    while (count_span > 1) {
        count_span = count_span \ 2;
        COUNT_BITS++;
    }
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

    // 3. Zero every field of an inactive leaf. These fields feed PolyEval, so
    //    otherwise a prover injects arbitrary values into inactive slots.
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
    //    leaves, so a relayer cannot place a nonzero leaf_asset or
    //    leaf_public_in into the public inputs of a batch carrying no deposit.
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
        // Hoisted through a `var`; see tags.circom.
        var tag = TAG_LEAF();
        leaf_h[k].inputs[0] <== tag;
        leaf_h[k].inputs[1] <== cms[k];
        leaf_h[k].inputs[2] <== cv_dep[k][0];
        leaf_h[k].inputs[3] <== cv_dep[k][1];
        leaves[k] <== leaf_h[k].out;
    }

    // 6. cv_dep must lie on Baby-Jubjub. For spend leaves this is the only
    //    per-point cv_dep constraint here: an off-curve point produces a note no
    //    on-curve ValueCommit can respend. Inactive slots hold (0, 0), which is
    //    off-curve, so (1 - active) shifts y to check (0, 1).
    component cv_on_curve[MAX_L];
    for (var k = 0; k < MAX_L; k++) {
        cv_on_curve[k] = BabyCheck();
        cv_on_curve[k].x <== cv_dep[k][0];
        cv_on_curve[k].y <== cv_dep[k][1] + (1 - active[k]);
    }

    // 7. Per-leaf deposit binding, gated by active[k]·is_deposit[k]. The
    //    equality pins cv_dep[k] to leaf_public_in units of leaf_asset.
    component asset_gen[MAX_L];
    component pub_in_mul[MAX_L];
    component rH_mul[MAX_L];
    component expected[MAX_L];
    component leaf_asset_nz[MAX_L];
    signal active_dep[MAX_L];

    component pub_in_nz[MAX_L];
    for (var k = 0; k < MAX_L; k++) {
        active_dep[k] <== active[k] * is_deposit[k];

        leaf_asset_nz[k] = IsZero();
        leaf_asset_nz[k].in <== leaf_asset[k];

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

        pub_in_nz[k] = IsZero();
        pub_in_nz[k].in <== leaf_public_in[k];

        // 7a. Pin leaf_asset[k] in the one case the equality above cannot.
        //
        // That equality pins leaf_asset[k] only while the V^leaf_asset[k] term
        // survives: ValueTimesGen(0, gen) is the curve identity for EVERY gen,
        // so at leaf_public_in[k] == 0 it reduces to cv_dep[k] == rcv[k]·H and
        // the asset leaves the system entirely. leaf_asset[k] would then be a
        // coefficient holding only a 64-bit range check, and a range check
        // bounds a coefficient without pinning it: four such leaves give
        // 4 × 64 = 256 bits of free dial against a 254-bit modulus, which is a
        // small CVP rather than a search. A `fbps = 0` flush supplies four.
        //
        // So tie the two together, per slot:
        //
        //   value != 0  the equality is non-degenerate and pins the asset under
        //               discrete-log hardness. Asset must be != 0, as before:
        //               SpentNote refuses id 0 on every real note, so a leaf
        //               minted there is committed and unspendable, and the
        //               deposit path is the only inserter that mints a leaf
        //               without a transact proof.
        //   value == 0  the asset is unconstrained by the equality AND carries
        //               no information — cv_dep is rcv·H whatever it says, and
        //               it reaches neither the note commitment nor the leaf
        //               hash, so nothing downstream reads it. Canonicalise it
        //               to 0. Pinned to a constant is pinned.
        //
        // Both directions are the one statement `asset == 0 iff value == 0`,
        // which is why this is a single constraint rather than a pair.
        //
        // Left gated on active_dep[k] even though steps 3 and 5 already force
        // both fields to zero on every inactive and spend slot, so an ungated
        // equality would hold there for free and would save the product. The
        // gate is what keeps the two IsZero outputs distinct signals: ungated,
        // --O1 substitutes one for the other and folds the `.in`/`.out` pair
        // that `lib/explain.ts :: isZeroHint` reads to check its precondition.
        // The explainer then refuses — correctly, since it will not assume a
        // layout — and the free `inv` hints go unexplained. Sixteen constraints
        // is a cheap price for a checkable precondition.
        //
        // The zero-value case is legitimate and must stay provable: a flush at
        // fbps = 0 mints a worthless fee note, which `MASP._validateDeposit`
        // permits explicitly. What this removes is its freedom, not the shape.
        //
        // Nothing here refers to a neighbouring slot, so the circuit stays
        // agnostic to how a consumer lays deposits out across the batch.
        active_dep[k] * (leaf_asset_nz[k].out - pub_in_nz[k].out) === 0;
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
    signal idx_in[MAX_L];
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
        // Insertion index, range-checked to 2·DEPTH bits and gated on active[k].
        // An inactive slot's insert is muxed away below, so range-checking its
        // index would bound capacity alone and put the top MAX_L - 1 leaves of
        // the tree out of reach. An inactive slot decomposes 0; its digits are
        // discarded with the insert.
        idx_in[k] <== active[k] * (start_index + k);
        idx_bits[k] = Num2Bits(BITS);
        idx_bits[k].in <== idx_in[k];

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

// DEPTH = 11 must match the transact circuits and the on-chain CommitmentTree
// (4^11 = 4,194,304 leaves; MAX_LEAVES and EMPTY_ROOT in CommitmentTree.sol).
//
// MAX_L is at its floor for the 4x6 transact shape: COUNT_BITS requires a power
// of two, and a spend emits TRANSACT_OUT = 6 leaves that must fit one batch,
// with MASP.sol pinning `actualCount` to exactly that on the spend path. Six is
// not a power of two, so the floor is 8. Only flushBatch uses the slack,
// carrying four two-leaf deposits per batch.
//
// Budget: this circuit grows on both axes at once — four more leaf slots at
// roughly 12k constraints each, plus a depth level across all eight — so it,
// not the transact circuit, decides whether 2^17 holds. Run `just budget` for
// the measured count.
//
// Changing either parameter requires a new ceremony and a contract change,
// since the public-input layout is 4 + 6·MAX_L.
component main {
    public [ z ]
} = TreeUpdateBatch(11, 8);
