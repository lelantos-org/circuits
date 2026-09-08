pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/poseidon.circom";
include "../../node_modules/circomlib/circuits/bitify.circom";
include "tags.circom";
include "common.circom";

// Rebuild the root of a lazily-materialized tree from its frontier and
// start_index, binding frontier_in to the public old_root.
//
// Per level d, with digit = (start_index >> 2d) % 4:
//   k <  digit : frontier_in[d][k]   (filled left sibling)
//   k == digit : cur[d]              (running rebuild)
//   k >  digit : zeros[d]            (empty right subtree)
// cur[0] = 0, cur[d+1] = Poseidon(TAG_MERKLE, c0..c3), root = cur[DEPTH].
//
// start_index_bits is booleanized here rather than assumed boolean. The
// selectors are products of the two bits and s[d][0..3] sums to 1 for any field
// values — b0 = 2, b1 = 0 gives (-1, 2, 0, 0) — so the one-hot shape alone
// does not constrain them. Off the boolean cube each child slot becomes an
// affine combination of cur[d], frontier_in[d][*] and zeros[d], which admits an
// old_root for a frontier the tree does not hold.
//
// The caller decomposes start_index and passes the bits, rather than this
// template taking start_index directly, because that same Num2Bits carries the
// capacity bound start_index < 4^DEPTH at the call site that relies on it.
template FrontierRoot(DEPTH) {
    signal input start_index_bits[2 * DEPTH];
    signal input frontier_in[DEPTH][3];
    signal output root;

    component zh = EmptySubtreeHashes(DEPTH);

    // Per-level digit selectors s[d][k] = 1 iff digit_d == k.
    signal b0[DEPTH];
    signal b1[DEPTH];
    signal bb[DEPTH];
    signal s[DEPTH][4];

    // Children, split into the frontier / cur / zeros contributions each slot can
    // receive. Slot 0 is never a zeros slot and slot 3 is never a frontier slot.
    signal c[DEPTH][4];
    signal c0_eq[DEPTH];
    signal c0_post[DEPTH];
    signal c1_pre[DEPTH];
    signal c1_eq[DEPTH];
    signal c1_post[DEPTH];
    signal c2_pre[DEPTH];
    signal c2_eq[DEPTH];
    signal c2_post[DEPTH];
    signal c3_pre[DEPTH];
    signal c3_eq[DEPTH];

    signal cur[DEPTH + 1];
    component h[DEPTH];
    cur[0] <== 0;

    for (var d = 0; d < DEPTH; d++) {
        b0[d] <== start_index_bits[2 * d];
        b1[d] <== start_index_bits[2 * d + 1];
        b0[d] * (b0[d] - 1) === 0;
        b1[d] * (b1[d] - 1) === 0;
        bb[d] <== b0[d] * b1[d];

        s[d][0] <== 1 - b0[d] - b1[d] + bb[d];
        s[d][1] <== b0[d] - bb[d];
        s[d][2] <== b1[d] - bb[d];
        s[d][3] <== bb[d];

        // Slot 0: digit == 0 ⇒ cur, digit > 0 ⇒ frontier_in[d][0].
        c0_eq[d]   <== s[d][0] * cur[d];
        c0_post[d] <== (s[d][1] + s[d][2] + s[d][3]) * frontier_in[d][0];
        c[d][0] <== c0_eq[d] + c0_post[d];

        // Slot 1: digit < 1 ⇒ zeros, == 1 ⇒ cur, > 1 ⇒ frontier_in[d][1].
        c1_pre[d]  <== s[d][0] * zh.zeros[d];
        c1_eq[d]   <== s[d][1] * cur[d];
        c1_post[d] <== (s[d][2] + s[d][3]) * frontier_in[d][1];
        c[d][1] <== c1_pre[d] + c1_eq[d] + c1_post[d];

        // Slot 2: digit < 2 ⇒ zeros, == 2 ⇒ cur, > 2 ⇒ frontier_in[d][2].
        c2_pre[d]  <== (s[d][0] + s[d][1]) * zh.zeros[d];
        c2_eq[d]   <== s[d][2] * cur[d];
        c2_post[d] <== s[d][3] * frontier_in[d][2];
        c[d][2] <== c2_pre[d] + c2_eq[d] + c2_post[d];

        // Slot 3: digit < 3 ⇒ zeros, == 3 ⇒ cur.
        c3_pre[d] <== (s[d][0] + s[d][1] + s[d][2]) * zh.zeros[d];
        c3_eq[d]  <== s[d][3] * cur[d];
        c[d][3] <== c3_pre[d] + c3_eq[d];

        h[d] = Poseidon(5);
        // Hoisted through a `var` rather than assigned straight from the
        // call; see tags.circom.
        var tag = TAG_MERKLE();
        h[d].inputs[0] <== tag;
        h[d].inputs[1] <== c[d][0];
        h[d].inputs[2] <== c[d][1];
        h[d].inputs[3] <== c[d][2];
        h[d].inputs[4] <== c[d][3];
        cur[d + 1] <== h[d].out;
    }

    root <== cur[DEPTH];
}
