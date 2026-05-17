pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/poseidon.circom";
include "../../node_modules/circomlib/circuits/bitify.circom";
include "tags.circom";
include "common.circom";

// FrontierRoot: rebuild lazy-root from frontier + start_index.
//
// Binds prover-supplied frontier_in to public old_root. Without this binding
// a relayer could pair any frontier with oldRoot == currentRoot() and produce
// a new_root from forged state (permanent pool DoS).
//
// Per level d, digit = (start_index >> 2d) % 4:
//   k <  digit : frontier_in[d][k]   (filled left sibling)
//   k == digit : cur[d]              (running rebuild from below)
//   k >  digit : zeros[d]            (empty right subtree)
// cur[0] = 0; cur[d+1] = Poseidon(TAG_MERKLE, c0..c3); root = cur[DEPTH].
// Cost ≈ 8.7k constraints @ DEPTH=10.
template FrontierRoot(DEPTH) {
    // Bit decomposition supplied by caller (reuses parent's Num2Bits).
    signal input start_index_bits[2 * DEPTH];
    signal input frontier_in[DEPTH][3];
    signal output root;

    component zh = EmptySubtreeHashes(DEPTH);

    // Per-level digit selectors s[d][k] = 1 iff digit_d == k.
    signal b0[DEPTH];
    signal b1[DEPTH];
    signal bb[DEPTH];
    signal s[DEPTH][4];

    // Children split into pre (frontier), eq (cur), post (zeros) subterms.
    // Slot 0 has no pre; slot 3 has no post.
    signal c[DEPTH][4];
    signal c_pre[DEPTH][4];
    signal c_eq[DEPTH][4];
    signal c_post[DEPTH][4];

    signal cur[DEPTH + 1];
    component h[DEPTH];
    cur[0] <== 0;

    for (var d = 0; d < DEPTH; d++) {
        b0[d] <== start_index_bits[2 * d];
        b1[d] <== start_index_bits[2 * d + 1];
        bb[d] <== b0[d] * b1[d];

        s[d][0] <== 1 - b0[d] - b1[d] + bb[d];
        s[d][1] <== b0[d] - bb[d];
        s[d][2] <== b1[d] - bb[d];
        s[d][3] <== bb[d];

        // Slot 0: digit == 0 ⇒ cur; digit > 0 ⇒ frontier_in[d][0].
        c_pre[d][0] <== 0;
        c_eq[d][0]  <== s[d][0] * cur[d];
        c_post[d][0] <== (s[d][1] + s[d][2] + s[d][3]) * frontier_in[d][0];
        c[d][0] <== c_eq[d][0] + c_post[d][0];

        // Slot 1: digit<1 ⇒ zeros; ==1 ⇒ cur; >1 ⇒ f[1].
        c_pre[d][1] <== s[d][0] * zh.zeros[d];
        c_eq[d][1]  <== s[d][1] * cur[d];
        c_post[d][1] <== (s[d][2] + s[d][3]) * frontier_in[d][1];
        c[d][1] <== c_pre[d][1] + c_eq[d][1] + c_post[d][1];

        // Slot 2: digit<2 ⇒ zeros; ==2 ⇒ cur; >2 ⇒ f[2].
        c_pre[d][2] <== (s[d][0] + s[d][1]) * zh.zeros[d];
        c_eq[d][2]  <== s[d][2] * cur[d];
        c_post[d][2] <== s[d][3] * frontier_in[d][2];
        c[d][2] <== c_pre[d][2] + c_eq[d][2] + c_post[d][2];

        // Slot 3: digit<3 ⇒ zeros; ==3 ⇒ cur.
        c_pre[d][3] <== (s[d][0] + s[d][1] + s[d][2]) * zh.zeros[d];
        c_eq[d][3]  <== s[d][3] * cur[d];
        c_post[d][3] <== 0;
        c[d][3] <== c_pre[d][3] + c_eq[d][3];

        h[d] = Poseidon(5);
        h[d].inputs[0] <== TAG_MERKLE();
        h[d].inputs[1] <== c[d][0];
        h[d].inputs[2] <== c[d][1];
        h[d].inputs[3] <== c[d][2];
        h[d].inputs[4] <== c[d][3];
        cur[d + 1] <== h[d].out;
    }

    root <== cur[DEPTH];
}
