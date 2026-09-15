pragma circom 2.2.3;

include "lib/batch_append.circom";
include "lib/poly_eval.circom";
include "lib/tags.circom";
include "lib/asset_gen.circom";
include "lib/value_commit.circom";
include "lib/balance.circom";
include "../node_modules/circomlib/circuits/poseidon.circom";
include "../node_modules/circomlib/circuits/babyjub.circom";

// Relayer proof that advances the commitment tree from old_root to new_root by
// inserting actual_count leaves at start_index.
//
// actual_count is in [1, MAX_L] and counts leaves; odd counts are permitted. A
// batch carries either a spend's N_OUT output leaves or a run of deposits (two
// leaves each). Trailing slots must be zero.
//
// leaf_k = Poseidon(TAG_LEAF, cms[k], cv_dep[k][0], cv_dep[k][1]), where cv_dep
// is the depositor's or spender's Pedersen value commitment. spent.circom
// recomputes the same leaf, binding (asset, value) across the two proofs.
//
// Per-leaf deposit binding, applied when is_deposit[k] == 1:
//   cv_dep[k] == leaf_public_in[k]·V^leaf_asset[k] + rcv[k]·H
//
// Deposits have no transact proof, so this circuit binds the leaf. The binding
// is per leaf, not aggregate: a sum fixes Σvalue only modulo the subgroup order
// l, which lets a depositor place 2^63·V^A in one leaf, absorb
// (public_in − 2^63) mod l in a second, abandoned leaf, and hold a valid 2^63
// note for a one-unit deposit.
//
// The binding alone is not injective in (asset, value). HashToAssetGen is
// circomlib Pedersen over a 72-bit message, so V^a = m(a)·BASE0 for a publicly
// computable m(a) of about 2^85 (src/README.md § 5), and the equality pins the
// product value·m(asset), not the pair. Two registered ids whose multipliers
// share a large factor admit v·m(a) == v'·m(a') with both values in the 64-bit
// range, so a depositor could pay v of one asset while committing cms[k] to
// (a', v') and spend the leaf as the other. Separation of the registered id set
// rules this out: run `just asset-ids <ids>` to check the bound before
// registration, since AssetRegistry.addAsset accepts an arbitrary uint64.
//
// is_deposit[k] == 0 skips the binding; the transact circuit proves conservation
// for spends. On a deposit leaf, asset id 0 is rejected when the leaf carries
// value (SpentNote refuses id 0, so the leaf would be unspendable) and required
// when it does not (step 6a).
//
// PolyEval coefficient layout; must match
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
// coefficient vector are the same words; every word is constrained, so every
// word is evaluated.
//
// The deposit-binding fields are coefficients, not challenge-only words. They
// are signals of this circuit, and hashing a signal into z binds nothing: the
// prover reads z before choosing a witness and can supply one that disagrees
// with the calldata z was hashed from. Only a constraint pins them: the deposit
// binding (step 6) and its degenerate case (step 6a). See BatchCompress in
// lib/poly_eval.circom and src/README.md § 2a.
//
// The tree logic (count and activity, position and capacity, frontier, both
// roots) is in lib/batch_append.circom and documented in its header. A prover
// MUST supply zero in frontier slots that no digit reads.
//
// Soundness obligations on the contract. BatchAppend binds frontier_in to
// old_root but cannot bind start_index: a tree of n leaves and a tree of n
// leaves plus trailing empties have the same root, so a (frontier, root) pair
// is consistent with more than one index. The consumer must enforce, as MASP.sol
// does:
//
//   1. start_index == committedCount, the authoritative leaf count
//      (MASP._validateBatchHeader). Otherwise a relayer can replay a valid batch
//      at a lower index and overwrite committed leaves. The check reads the live
//      count at execution, so batches may chain within one transaction
//      (contracts' Bundler); each sees the count and old_root left by the
//      previous one.
//   2. actual_count pinned to the emitting operation: exactly TRANSACT_OUT
//      leaves on the spend path.
//   3. cms[k] and cv_dep[k] forwarded from the paired transact proof, not taken
//      from the relayer, for every output slot of that spend.
//   4. is_deposit[k] pinned per active slot, not taken from the relayer: 1 on
//      every leaf of a deposit batch, 0 on every leaf of a spend batch. The
//      circuit constrains it only to be boolean and it gates the deposit
//      binding, so a relayer setting it to 0 on a deposit leaf inserts a leaf
//      whose cv_dep is constrained only by BabyCheck. MASP._drainDeposit and
//      MASP._validateRequest enforce this over every active slot.
//   5. publicIn != 0 on every principal deposit, so a leaf that carries value
//      also carries an asset the binding pins. The circuit accepts a zero-value
//      deposit leaf and canonicalises its leaf_asset to 0 (step 6a), which is
//      sound because that asset reaches nothing. MASP enforces this via
//      `MustHaveDeposit` in _validateDeposit.
//   6. leaf_asset[k] == 0 on every zero-value deposit leaf, matching step 6a.
//      MASP._drainDeposit sets it for the fee note it emits; a non-zero asset on
//      a zero-value leaf makes the batch unprovable.
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

    // 1. leaf_k = Poseidon(TAG_LEAF, cm_k, cv_dep_k_x, cv_dep_k_y).
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

    // 2. Tree append: actual_count in [1, MAX_L], the activity prefix, the run
    //    within tree capacity, the frontier pin, and the roots before and after.
    //    See lib/batch_append.circom.
    component append = BatchAppend(DEPTH, MAX_L);
    append.start_index <== start_index;
    append.actual_count <== actual_count;
    for (var k = 0; k < MAX_L; k++) {
        append.leaves[k] <== leaves[k];
    }
    for (var d = 0; d < DEPTH; d++) {
        for (var s = 0; s < 3; s++) {
            append.frontier_in[d][s] <== frontier_in[d][s];
        }
    }
    old_root === append.old_root;
    new_root === append.new_root;

    // 3. Zero every field of an inactive leaf. These fields feed PolyEval, so
    //    unconstrained inactive slots would be free coefficients.
    for (var k = 0; k < MAX_L; k++) {
        (1 - append.active[k]) * cms[k]            === 0;
        (1 - append.active[k]) * cv_dep[k][0]      === 0;
        (1 - append.active[k]) * cv_dep[k][1]      === 0;
        (1 - append.active[k]) * leaf_asset[k]     === 0;
        (1 - append.active[k]) * leaf_public_in[k] === 0;
        (1 - append.active[k]) * is_deposit[k]     === 0;
        (1 - append.active[k]) * rcv[k]            === 0;
    }

    // 4. Booleanize is_deposit[k] and zero the deposit-only fields on spend
    //    leaves, so a relayer cannot place a nonzero leaf_asset or
    //    leaf_public_in into the public inputs of a batch carrying no deposit.
    for (var k = 0; k < MAX_L; k++) {
        is_deposit[k] * (1 - is_deposit[k]) === 0;
        (1 - is_deposit[k]) * leaf_asset[k]     === 0;
        (1 - is_deposit[k]) * leaf_public_in[k] === 0;
    }

    // 5. cv_dep lies on Baby-Jubjub. For spend leaves this is the only per-point
    //    cv_dep constraint here; an off-curve point yields a note no on-curve
    //    ValueCommit can respend. Inactive slots hold the off-curve (0, 0), so
    //    (1 - active) shifts y to check (0, 1) instead.
    component cv_on_curve[MAX_L];
    for (var k = 0; k < MAX_L; k++) {
        cv_on_curve[k] = BabyCheck();
        cv_on_curve[k].x <== cv_dep[k][0];
        cv_on_curve[k].y <== cv_dep[k][1] + (1 - append.active[k]);
    }

    // 6. Per-leaf deposit binding, gated by append.active[k]·is_deposit[k]. The
    //    equality pins cv_dep[k] to leaf_public_in units of leaf_asset.
    component asset_gen[MAX_L];
    component pub_in_mul[MAX_L];
    component rH_mul[MAX_L];
    component expected[MAX_L];
    component leaf_asset_nz[MAX_L];
    signal active_dep[MAX_L];

    component pub_in_nz[MAX_L];
    for (var k = 0; k < MAX_L; k++) {
        active_dep[k] <== append.active[k] * is_deposit[k];

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

        // 6a. Pin leaf_asset[k] where the equality above degenerates.
        //
        // ValueTimesGen(0, gen) is the identity for every gen, so at
        // leaf_public_in[k] == 0 the equality reduces to cv_dep[k] == rcv[k]·H
        // and does not constrain leaf_asset[k]. That coefficient would carry
        // only a 64-bit range check, which bounds but does not pin it: four
        // such leaves (as in a `fbps = 0` flush) give 4 × 64 = 256 free bits
        // against a 254-bit modulus, solvable as a small CVP instance.
        //
        // One constraint enforces `asset == 0 iff value == 0` per slot:
        //   value != 0  the equality pins the asset under discrete-log
        //               hardness, and the asset must be != 0: SpentNote refuses
        //               id 0, so the leaf would be unspendable, and the deposit
        //               path inserts leaves without a transact proof.
        //   value == 0  the asset carries no information (cv_dep is rcv·H, and
        //               the asset reaches neither the note commitment nor the
        //               leaf hash), so it is canonicalised to 0.
        //
        // The active_dep[k] gate is not needed for soundness (steps 3 and 4 zero
        // both fields on inactive and spend slots) but keeps the two IsZero
        // outputs distinct signals. Ungated, --O1 substitutes one for the other
        // and folds the `.in`/`.out` pair that `lib/explain.ts :: isZeroHint`
        // reads to check its precondition, leaving the `inv` hints unexplained.
        // The gate costs sixteen constraints.
        //
        // The zero-value case must remain provable: a flush at fbps = 0 mints a
        // zero-value fee note, which `MASP._validateDeposit` permits. The
        // constraint references no other slot, so it does not depend on how a
        // consumer lays out deposits across the batch.
        active_dep[k] * (leaf_asset_nz[k].out - pub_in_nz[k].out) === 0;
    }

    // 7. Public-input compression → (y, z).
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
// MAX_L = 8 is the minimum for the 4x6 transact shape: COUNT_BITS requires a
// power of two, and a spend emits TRANSACT_OUT = 6 leaves that must fit one
// batch (MASP.sol pins `actualCount` to exactly that on the spend path). Only
// flushBatch uses the remaining capacity, carrying four two-leaf deposits.
//
// Budget: BatchAppend cost grows with depth rather than leaf count, so a leaf
// slot's cost is dominated by its deposit binding. Run `just budget` for the
// measured count and domain.
//
// Changing either parameter requires a new ceremony and a contract change,
// since the public-input layout is 4 + 6·MAX_L.
component main {
    public [ z ]
} = TreeUpdateBatch(11, 8);
