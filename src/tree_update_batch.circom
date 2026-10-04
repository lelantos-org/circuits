pragma circom 2.2.3;

include "lib/batch_append.circom";
include "lib/poly_eval.circom";
include "lib/note.circom";
include "lib/balance.circom";
include "../node_modules/circomlib/circuits/comparators.circom";

// Relayer proof that advances the commitment tree from old_root to new_root by
// inserting actual_count leaves at start_index.
//
// actual_count is in [1, MAX_L] and counts leaves; odd counts are permitted.
// Trailing slots must be zero.
//
// A leaf is a note commitment,
//
//   cm = Poseidon(TAG_CM, asset_id·2^64 + value, inner),
//   inner = Poseidon(TAG_INNER, pk, rho, rcm),
//
// and the word in cms[k] is read by is_deposit[k]:
//
//   is_deposit[k] == 0   cms[k] is the out_cm of a transact proof and is the
//                        leaf; nothing is opened here.
//   is_deposit[k] == 1   cms[k] is the depositor's `inner`. The leaf is
//                        Poseidon(TAG_CM, leaf_asset[k]·2^64 + leaf_public_in[k],
//                        cms[k]).
//
// Deposits have no transact proof, so this circuit binds each deposit leaf to
// its public amount. SpentNote recomputes cm from the note it opens, and the
// packing is injective under the two 64-bit range checks, so the leaf can be
// spent only as leaf_public_in units of leaf_asset.
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
// circuit, so every word is evaluated: a signal hashed into z but not
// evaluated is unbound, since the prover reads z before choosing a witness.
//
// The public signals are (y, digest, z), in that order. digest is the
// CoeffDigest of the coefficients; the contract takes it from calldata, hashes
// it into z after the coefficients, and passes it to the verifier. See
// BatchCompress in lib/poly_eval.circom and src/README.md § 2a.
//
// The tree logic is in lib/batch_append.circom. A prover must supply zero in
// frontier slots that no digit reads.
//
// Obligations on the contract. BatchAppend binds frontier_in to old_root but
// not start_index: a tree of n leaves and one with trailing empties have the
// same root. The consumer must enforce, as MASP.sol does:
//
//   1. start_index == committedCount, the live leaf count at execution
//      (MASP._validateBatchHeader). Otherwise a relayer can replay a valid batch
//      at a lower index and overwrite committed leaves.
//   2. actual_count pinned to the emitting operation: TRANSACT_OUT leaves on
//      the spend path.
//   3. cms[k] taken from the paired transact proof's out_cm on a spend slot and
//      from the `inner` the depositor escrowed on a deposit slot, not from the
//      relayer.
//   4. is_deposit[k] pinned per active slot, not taken from the relayer: 1 on
//      every leaf of a deposit batch, 0 on every leaf of a spend batch
//      (MASP._drainDeposit, MASP._validateRequest). The circuit constrains it
//      only to be boolean, and both mistakes verify. Cleared on a deposit leaf,
//      the depositor's word is inserted unhashed, so an escrowed cm in place of
//      `inner` yields a note of any value. Set on a spend leaf, the leaf has no
//      opening and the spend's outputs are burned.
//   5. leaf_asset[k] and leaf_public_in[k] taken from the contract's own record
//      of the deposit.
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
    //    leaves, which neither field reaches.
    for (var k = 0; k < MAX_L; k++) {
        is_deposit[k] * (1 - is_deposit[k]) === 0;
        (1 - is_deposit[k]) * leaf_asset[k]     === 0;
        (1 - is_deposit[k]) * leaf_public_in[k] === 0;
    }

    // 2. The leaf. On a deposit slot it is the note commitment over the public
    //    amount and the depositor's `inner`; on a spend slot it is cms[k].
    //    Both fields are range-checked on every slot: NoteCommitment's packing
    //    is injective only under the two bounds.
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

    // 4. Zero every field of an inactive slot. BatchAppend ignores its leaf, so
    //    nothing else constrains these words.
    for (var k = 0; k < MAX_L; k++) {
        (1 - append.active[k]) * cms[k]            === 0;
        (1 - append.active[k]) * leaf_asset[k]     === 0;
        (1 - append.active[k]) * leaf_public_in[k] === 0;
        (1 - append.active[k]) * is_deposit[k]     === 0;
    }

    // 5. No value under asset id 0. Id 0 means "no asset" and SpentNote refuses
    //    it on a real note, so a leaf minted there would be unspendable.
    //    Ungated: steps 1 and 4 force leaf_public_in[k] to zero on spend and
    //    inactive slots. A zero-value deposit leaf may name any id.
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
// batch.
//
// Changing either parameter requires a new ceremony and a contract change,
// since the coefficient layout is 4 + 4·MAX_L.
component main {
    public [ z ]
} = TreeUpdateBatch(11, 8);
