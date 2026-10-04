pragma circom 2.2.3;

include "lib/batch_append.circom";
include "lib/poly_eval.circom";
include "lib/note.circom";
include "lib/balance.circom";
include "../node_modules/circomlib/circuits/comparators.circom";

// Relayer proof that advances the commitment tree from old_root to new_root by
// inserting actual_count leaves at start_index.
//
// actual_count is in [1, MAX_L] and counts leaves; odd counts are permitted. A
// batch carries either a spend's N_OUT output leaves or a run of deposits (two
// leaves each). Trailing slots must be zero.
//
// A leaf is a note commitment,
//
//   cm = Poseidon(TAG_CM, asset_id·2^64 + value, inner),
//   inner = Poseidon(TAG_INNER, pk, rho, rcm),
//
// and the word in cms[k] is read by is_deposit[k]:
//
//   is_deposit[k] == 0   cms[k] is the cm a transact proof bound as out_cm. It
//                        is the leaf. The transact circuit proved conservation
//                        for it; nothing is opened here.
//   is_deposit[k] == 1   cms[k] is the depositor's `inner`. The leaf is
//                        Poseidon(TAG_CM, leaf_asset[k]·2^64 + leaf_public_in[k],
//                        cms[k]): this circuit builds cm from the public amount.
//
// Deposits have no transact proof, so this circuit binds the leaf. SpentNote
// recomputes cm from the note it opens and proves that cm is in the tree, so a
// deposit leaf can be spent only as leaf_public_in units of leaf_asset: the
// packing is injective under the two 64-bit range checks, and a second opening
// is a Poseidon collision. Nothing depends on which ids are registered.
//
// The binding is per leaf. There is no aggregate, so no split between leaves
// is available to a depositor.
//
// PolyEval coefficient layout; must match
// PubInputs.sol :: compress(TreeUpdateBatch):
//   [0]                            old_root
//   [1]                            new_root
//   [2]                            start_index
//   [3]                            actual_count
//   [4 .. 3 + MAX_L]               cms
//   [4 + MAX_L .. 3 + 2·MAX_L]     leaf_asset
//   [4 + 2·MAX_L .. 3 + 3·MAX_L]   leaf_public_in
//   [4 + 3·MAX_L .. 3 + 4·MAX_L]   is_deposit
// Total = 4 + 4·MAX_L (36 for MAX_L = 8). Every word is a signal of this
// circuit, so every word is evaluated: hashing a signal into z without
// evaluating it binds nothing, since the prover reads z before choosing a
// witness and can supply one that disagrees with the calldata z was hashed
// from.
//
// The public signals are (y, digest, z), in that order. digest is the
// CoeffDigest of the 36 coefficients; the contract takes it from calldata,
// hashes it into z after the coefficients, and passes it to the verifier. See
// BatchCompress in lib/poly_eval.circom and src/README.md § 2a.
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
//   3. cms[k] forwarded from the paired transact proof's out_cm, not taken from
//      the relayer, for every output slot of that spend; and, on a deposit
//      slot, the `inner` the depositor escrowed.
//   4. is_deposit[k] pinned per active slot, not taken from the relayer: 1 on
//      every leaf of a deposit batch, 0 on every leaf of a spend batch. The
//      circuit constrains it only to be boolean, and it selects how cms[k]
//      becomes a leaf. Both mistakes verify:
//        cleared on a deposit leaf   the depositor's word is inserted as it
//                                    stands. A depositor who escrowed a cm of
//                                    its choosing in place of `inner` holds a
//                                    note of any value for a one-unit deposit.
//        set on a spend leaf         the leaf is the hash of out_cm under
//                                    (leaf_asset, leaf_public_in). It has no
//                                    opening, so the spend's outputs are burned.
//      MASP._drainDeposit and MASP._validateRequest enforce this over every
//      active slot.
//   5. leaf_asset[k] and leaf_public_in[k] taken from the contract's own record
//      of the deposit, since they are the amount the leaf is minted for.
//
// The circuit refuses value under asset id 0 on a deposit leaf (step 5): id 0
// means "no asset", SpentNote refuses it on a real note, and such a leaf would
// be unspendable. A zero-value deposit leaf may name any id, 0 included; the
// fee note of a zero-fee deposit does.
//
template TreeUpdateBatch(DEPTH, MAX_L) {
    // ===== PUBLIC =====
    signal input  z;
    signal output y;
    signal output digest;   // CoeffDigest of the logical public inputs below

    // ===== LOGICAL PUBLIC INPUTS =====
    signal input old_root;
    signal input new_root;
    signal input start_index;
    signal input actual_count;            // 1..MAX_L, counted in leaves
    signal input cms[MAX_L];              // cm (spend) or inner (deposit); padding 0
    signal input leaf_asset[MAX_L];       // per-leaf publicAssetId; deposits only
    signal input leaf_public_in[MAX_L];   // per-leaf publicIn; deposits only
    signal input is_deposit[MAX_L];       // 1: build the leaf from the public amount

    // ===== PRIVATE =====
    signal input frontier_in[DEPTH][3];

    // 1. Booleanize is_deposit[k] and zero the deposit-only fields on spend
    //    leaves, so a relayer cannot place a nonzero leaf_asset or
    //    leaf_public_in into the public inputs of a batch carrying no deposit.
    //    Neither field reaches a spend leaf.
    for (var k = 0; k < MAX_L; k++) {
        is_deposit[k] * (1 - is_deposit[k]) === 0;
        (1 - is_deposit[k]) * leaf_asset[k]     === 0;
        (1 - is_deposit[k]) * leaf_public_in[k] === 0;
    }

    // 2. The leaf. On a deposit slot it is the note commitment over the public
    //    amount and the depositor's `inner`; on a spend slot it is cms[k].
    //
    //    Both fields are range-checked on every slot: NoteCommitment's packing
    //    is injective only under the two bounds, and that injectivity is the
    //    deposit binding.
    component rng_asset[MAX_L];
    component rng_public_in[MAX_L];
    component dep_cm[MAX_L];
    signal dep_delta[MAX_L];
    signal leaves[MAX_L];
    for (var k = 0; k < MAX_L; k++) {
        rng_asset[k] = RangeCheck64();
        rng_asset[k].v <== leaf_asset[k];

        rng_public_in[k] = RangeCheck64();
        rng_public_in[k].v <== leaf_public_in[k];

        dep_cm[k] = NoteCommitment();
        dep_cm[k].asset_id <== leaf_asset[k];
        dep_cm[k].value    <== leaf_public_in[k];
        dep_cm[k].inner    <== cms[k];

        dep_delta[k] <== is_deposit[k] * (dep_cm[k].cm - cms[k]);
        leaves[k] <== cms[k] + dep_delta[k];
    }

    // 3. Tree append: actual_count in [1, MAX_L], the activity prefix, the run
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

    // 4. Zero every field of an inactive leaf. BatchAppend ignores an inactive
    //    slot's leaf, so nothing else would give these words a meaning.
    for (var k = 0; k < MAX_L; k++) {
        (1 - append.active[k]) * cms[k]            === 0;
        (1 - append.active[k]) * leaf_asset[k]     === 0;
        (1 - append.active[k]) * leaf_public_in[k] === 0;
        (1 - append.active[k]) * is_deposit[k]     === 0;
    }

    // 5. No value under asset id 0. SpentNote refuses id 0 on a real note, so a
    //    leaf minted there would be unspendable, and the deposit path inserts
    //    leaves without a transact proof to catch it.
    //
    //    Ungated: steps 1 and 4 force leaf_public_in[k] to zero on spend and
    //    inactive slots, where the product vanishes whatever the asset is.
    //    A zero-value deposit leaf is unaffected and may name any id.
    component leaf_asset_z[MAX_L];
    for (var k = 0; k < MAX_L; k++) {
        leaf_asset_z[k] = IsZero();
        leaf_asset_z[k].in <== leaf_asset[k];
        leaf_asset_z[k].out * leaf_public_in[k] === 0;
    }

    // 6. Public-input compression → (y, digest, z).
    component pe = BatchCompress(MAX_L);
    pe.z <== z;
    pe.old_root <== old_root;
    pe.new_root <== new_root;
    pe.start_index <== start_index;
    pe.actual_count <== actual_count;
    for (var k = 0; k < MAX_L; k++) {
        pe.cms[k] <== cms[k];
        pe.leaf_asset[k] <== leaf_asset[k];
        pe.leaf_public_in[k] <== leaf_public_in[k];
        pe.is_deposit[k] <== is_deposit[k];
    }
    y <== pe.y;
    digest <== pe.digest;
}

// DEPTH = 11 must match the transact circuits and the on-chain CommitmentTree
// (4^11 = 4,194,304 leaves; MAX_LEAVES and EMPTY_ROOT in CommitmentTree.sol).
//
// MAX_L = 8 is the minimum for the 4x6 transact shape: COUNT_BITS requires a
// power of two, and a spend emits TRANSACT_OUT = 6 leaves that must fit one
// batch (MASP.sol pins `actualCount` to exactly that on the spend path). Only
// flushBatch uses the remaining capacity, carrying four two-leaf deposits.
//
// Budget: BatchAppend cost grows with depth rather than leaf count, and a leaf
// slot costs one Poseidon(3) and two range checks. Run `just budget` for the
// measured count and domain.
//
// Changing either parameter requires a new ceremony and a contract change,
// since the coefficient layout is 4 + 4·MAX_L.
component main {
    public [ z ]
} = TreeUpdateBatch(11, 8);
