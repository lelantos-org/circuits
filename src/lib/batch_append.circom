pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/poseidon.circom";
include "../../node_modules/circomlib/circuits/bitify.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";
include "tags.circom";
include "common.circom";

// BatchAppend(DEPTH, MAX_L): the quaternary commitment tree before and after
// appending the first actual_count of MAX_L leaves at start_index, both roots
// computed from one frontier. This header is the one place the construction is
// explained; tree_update_batch.circom, the Lean model
// (lean/Lelantos/Gadgets/BatchAppend.lean) and the docs point here.
//
// WHAT THE TEMPLATE OWNS. Everything its correctness rests on is enforced
// inside, so it is safe to instantiate on its own:
//   * actual_count in [1, MAX_L]: Num2Bits(COUNT_BITS) on actual_count - 1,
//     with MAX_L a power of two.
//   * active[k] = (k < actual_count): LessThan, exported for the caller.
//   * start_index < 4^DEPTH: Num2Bits(2·DEPTH), whose bits are the per-level
//     digits and are boolean by construction.
//   * start_index + actual_count - 1 < 4^DEPTH: the whole run fits the tree.
//
// DIGITS. r_d is digit d of start_index. The selector s[d][r] = 1 iff r_d == r
// is a linear combination of the digit's two bits and bb[d], their product.
//
// FRONTIER. frontier_in[d][k] for k < r_d is the filled left sibling at level d.
// The slots k >= r_d hold nothing, and are pinned to zero:
//     (1 - read) · frontier_in[d][k] === 0,   read = Σ_{r > k} s[d][r].
// Under the pin frontier_in[d][k] = read · frontier_in[d][k], so both roots below
// add a frontier slot as a plain linear term instead of a selector product. A
// prover MUST supply zero in the unread slots; the in-repo writers do
// (Frontier::slots, MerkleTree::frontier, sdk merkle.ts frontier()).
//
// OLD ROOT. The running node along start_index, from an empty leaf:
//     old_node[0] = 0;  child k of old_node[d+1] is
//         frontier_in[d][k]   if k <  r_d
//         old_node[d]         if k == r_d
//         EMPTY_SUBTREE(d)    if k >  r_d.
// That is the root of the tree holding start_index leaves with this frontier.
//
// NEW ROOT. At level d the run changes positions lo_d = start_index >> 2d
// through hi_d = (start_index + actual_count - 1) >> 2d. A fixed window keeps
// W[d] = BATCH_WINDOW(DEPTH, MAX_L, d) of them, slot j at position lo_d + j:
// n consecutive leaves touch at most (n - 2) \ 4^d + 2 nodes at level d, capped
// at the level's width 4^(DEPTH - d). For MAX_L = 8 the widths are 8, 3, 2, …,
// 2, 1, which is 22 hashes. Child k of slot j reads BATCH_SRC(W[d], j, k, r_d):
//     p = 4j + k - r_d < 0     frontier_in[d][k]   (only at j = 0, k < 3)
//     0 <= p < W[d]           node[d][p]
//     p >= W[d]               EMPTY_SUBTREE(d)
// Leaf slot t holds active[t] · leaves[t], so an inactive slot is
// EMPTY_SUBTREE(0) = 0, and a window slot past hi_d reads only empty children and
// hashes to EMPTY_SUBTREE(d + 1). That keeps the fixed shape correct for every
// count, and it is the one step that needs the EMPTY_SUBTREE table to be the
// empty-subtree chain (ZerosCoherent in the Lean model).

// Worst-case number of nodes n consecutive leaves change at level d <= DEPTH.
function BATCH_WINDOW(DEPTH, n, d) {
    if (d == 0) {
        return n;
    }
    var w = 1;
    if (n >= 2) {
        w = (n - 2) \ (4 ** d) + 2;
    }
    var cap = 4 ** (DEPTH - d);
    if (w > cap) {
        w = cap;
    }
    return w;
}

// Where child k of window slot j reads from at digit r, over a lower window of
// width w: -1 for the frontier slot, the lower slot p = 4j + k - r while p < w,
// and w for the empty subtree past the window.
function BATCH_SRC(w, j, k, r) {
    var p = 4 * j + k - r;
    if (p < 0) {
        return -1;
    }
    if (p < w) {
        return p;
    }
    return w;
}

// Number of window-node children read from a lower window node, over every
// level and every digit: the size of the new root's product array.
function BATCH_NPROD(DEPTH, MAX_L) {
    var n = 0;
    for (var d = 0; d < DEPTH; d++) {
        var w = BATCH_WINDOW(DEPTH, MAX_L, d);
        for (var j = 0; j < BATCH_WINDOW(DEPTH, MAX_L, d + 1); j++) {
            for (var k = 0; k < 4; k++) {
                for (var r = 0; r < 4; r++) {
                    var src = BATCH_SRC(w, j, k, r);
                    if (src >= 0 && src < w) {
                        n++;
                    }
                }
            }
        }
    }
    return n;
}

template BatchAppend(DEPTH, MAX_L) {
    signal input start_index;
    signal input actual_count;
    signal input leaves[MAX_L];
    signal input frontier_in[DEPTH][3];
    signal output old_root;
    signal output new_root;
    signal output active[MAX_L];

    assert(EMPTY_SUBTREE(0) == 0);
    // Hoisted through a `var`; see tags.circom.
    var tag = TAG_MERKLE();
    // W[0] = MAX_L is not capped by the tree width, so a batch must fit a tree.
    assert(MAX_L <= 4 ** DEPTH);

    // Count and activity. COUNT_BITS is derived from MAX_L so the two cannot
    // diverge; the assert enforces the power of two the derivation cannot.
    var COUNT_BITS = 0;
    var count_span = MAX_L;
    while (count_span > 1) {
        count_span = count_span \ 2;
        COUNT_BITS++;
    }
    assert((1 << COUNT_BITS) == MAX_L);
    component cnt_bits = Num2Bits(COUNT_BITS);
    cnt_bits.in <== actual_count - 1;

    component lt[MAX_L];
    for (var k = 0; k < MAX_L; k++) {
        lt[k] = LessThan(COUNT_BITS + 1);
        lt[k].in[0] <== k;
        lt[k].in[1] <== actual_count;
        active[k] <== lt[k].out;
    }

    // Position and capacity. No wraparound in the last index: start_index <
    // 2^(2·DEPTH) and actual_count - 1 < MAX_L.
    var BITS = 2 * DEPTH;
    component idx_bits = Num2Bits(BITS);
    idx_bits.in <== start_index;
    component last_idx_bits = Num2Bits(BITS);
    last_idx_bits.in <== start_index + actual_count - 1;

    // Digit selectors.
    signal bb[DEPTH];
    var s[DEPTH][4];
    for (var d = 0; d < DEPTH; d++) {
        bb[d] <== idx_bits.out[2 * d] * idx_bits.out[2 * d + 1];
        s[d][0] = 1 - idx_bits.out[2 * d] - idx_bits.out[2 * d + 1] + bb[d];
        s[d][1] = idx_bits.out[2 * d] - bb[d];
        s[d][2] = idx_bits.out[2 * d + 1] - bb[d];
        s[d][3] = bb[d];
    }

    // Frontier pin.
    for (var d = 0; d < DEPTH; d++) {
        for (var k = 0; k < 3; k++) {
            var read = 0;
            for (var r = k + 1; r < 4; r++) {
                read += s[d][r];
            }
            (1 - read) * frontier_in[d][k] === 0;
        }
    }

    // Old root.
    signal old_node[DEPTH + 1];
    signal old_prod[DEPTH][4];
    component old_h[DEPTH];
    old_node[0] <== 0;
    for (var d = 0; d < DEPTH; d++) {
        old_h[d] = Poseidon(5);
        old_h[d].inputs[0] <== tag;
        var zero = EMPTY_SUBTREE(d);
        var below = 0;
        for (var k = 0; k < 4; k++) {
            old_prod[d][k] <== s[d][k] * old_node[d];
            var child = old_prod[d][k] + below * zero;
            if (k < 3) {
                child += frontier_in[d][k];
            }
            old_h[d].inputs[k + 1] <== child;
            below += s[d][k];
        }
        old_node[d + 1] <== old_h[d].out;
    }
    old_root <== old_node[DEPTH];

    // New root: window widths and their offsets into the flat node array.
    var W[DEPTH + 1];
    var OFF[DEPTH + 1];
    var NODES = 0;
    for (var d = 0; d <= DEPTH; d++) {
        W[d] = BATCH_WINDOW(DEPTH, MAX_L, d);
        OFF[d] = NODES;
        NODES += W[d];
    }
    assert(W[DEPTH] == 1);

    signal node[NODES];
    for (var t = 0; t < MAX_L; t++) {
        node[OFF[0] + t] <== active[t] * leaves[t];
    }

    // One product per child a digit reads from a lower window node; the
    // frontier and the empty subtree enter linearly.
    var NPROD = BATCH_NPROD(DEPTH, MAX_L);
    signal prod[NPROD];
    component h[NODES - W[0]];
    var pi = 0;

    for (var d = 0; d < DEPTH; d++) {
        var zero = EMPTY_SUBTREE(d);
        for (var j = 0; j < W[d + 1]; j++) {
            var hi = OFF[d + 1] - W[0] + j;
            h[hi] = Poseidon(5);
            h[hi].inputs[0] <== tag;

            for (var k = 0; k < 4; k++) {
                // Some digit reads the frontier exactly when 4j + k < 3.
                var child = 0;
                if (4 * j + k < 3) {
                    child += frontier_in[d][k];
                }
                for (var r = 0; r < 4; r++) {
                    var src = BATCH_SRC(W[d], j, k, r);
                    if (src == W[d]) {
                        child += s[d][r] * zero;
                    } else if (src >= 0) {
                        prod[pi] <== s[d][r] * node[OFF[d] + src];
                        child += prod[pi];
                        pi++;
                    }
                }
                h[hi].inputs[k + 1] <== child;
            }
            node[OFF[d + 1] + j] <== h[hi].out;
        }
    }
    assert(pi == NPROD);

    new_root <== node[OFF[DEPTH]];
}
