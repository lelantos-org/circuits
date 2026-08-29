pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/poseidon.circom";
include "../../node_modules/circomlib/circuits/bitify.circom";
include "tags.circom";

// Decompose path_index ∈ {0..3} into bits[0..1] (LSB-first) and the one-hot
// selector s[k] = 1 iff k == path_index:
//   s[0] = (1-b0)(1-b1), s[1] = b0(1-b1), s[2] = (1-b0)b1, s[3] = b0·b1.
// Num2Bits(2) also range-checks path_index.
template PathIndexSelectors() {
    signal input path_index;
    signal output bits[2];
    signal output s[4];

    component idx_bits = Num2Bits(2);
    idx_bits.in <== path_index;
    bits[0] <== idx_bits.out[0];
    bits[1] <== idx_bits.out[1];

    signal bb;
    bb <== bits[0] * bits[1];
    s[0] <== 1 - bits[0] - bits[1] + bb;
    s[1] <== bits[0] - bb;
    s[2] <== bits[1] - bb;
    s[3] <== bb;
}

// Empty-subtree hashes: zeros[0] = 0, zeros[d+1] = Poseidon(TAG_MERKLE, zeros[d] × 4).
// TAG_MERKLE must match MerkleLevel4.
//
// These are compile-time constants, but circom does not constant-fold Poseidon:
// computing the chain in-circuit costs DEPTH × Poseidon(5) constraints per
// instantiation, and `tree_update_batch` instantiates EmptySubtreeHashes
// MAX_L + 1 times (one per QuaternaryInsert, plus FrontierRoot) for the same
// fixed table.
//
// The table is pinned two ways:
//   - `src/test/merkle.test.ts` recomputes the chain with circomlibjs and asserts
//     every entry, including that EMPTY_SUBTREE(10) is the genesis root.
//   - EMPTY_SUBTREE(DEPTH) equals CommitmentTree.EMPTY_ROOT in the contracts
//     repo. Read it from the table below and convert; a second copy written out
//     here is a constant that can silently drift from the one that matters.
//
// Extending the tree beyond DEPTH = 11 requires appending entries here.
function EMPTY_SUBTREE(d) {
    assert(d >= 0);
    assert(d <= 11);
    var z[12];
    z[0]  = 0;
    z[1]  = 9688446225132779566270323192018004944760743136261961935684920214842198706882;
    z[2]  = 7372477669598451827916824388459948538481024917085258427336598380045876808937;
    z[3]  = 6963002638166051310340460060373962221427984164408700966057955389678820537775;
    z[4]  = 4501891970687803437678777359116189768994683435388499944223872268390656914248;
    z[5]  = 3179580195589593749366678182492387114398097369354143955628276022038298865503;
    z[6]  = 21800864736458967629487849402702439053787989654957290894223200992718642916160;
    z[7]  = 6243778328599448874473440891433129521442396349997420030341684817177854107879;
    z[8]  = 7697891372117443905574123126877256384618067426963460859230406409031270788574;
    z[9]  = 9730897556345557679365537455943876163307163461955882385767465684822645783047;
    z[10] = 8609704094418396324511832574933371601208234217740666943293213721288143421607;
    z[11] = 13105024820937039918253549408468725512672689423801512358804472101234041165599;
    return z[d];
}

template EmptySubtreeHashes(DEPTH) {
    signal output zeros[DEPTH + 1];

    // The value is hoisted through a `var` rather than assigned straight from the
    // call: the witness-graph builder (`build-circuit`, used to produce the
    // relayer's native witness calculator) cannot store a function result into a
    // signal. Inlining these back breaks `just build-graph`. The R1CS is
    // unaffected either way — the call folds to a constant.
    for (var i = 0; i <= DEPTH; i++) {
        var zero = EMPTY_SUBTREE(i);
        zeros[i] <== zero;
    }
}
