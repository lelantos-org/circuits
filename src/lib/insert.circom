pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/poseidon.circom";
include "../../node_modules/circomlib/circuits/bitify.circom";
include "tags.circom";

// Quaternary (arity-4) incremental insert. Mirrors the on-chain
// CommitmentTree._insert semantics from the Solidity v1 implementation but
// inside the circuit so the relayer can prove a tree advancement off-chain.
//
// Slot-fill table at each level given digit `slot` ∈ {0,1,2,3}:
//
//                      slot 0     slot 1     slot 2     slot 3
//   c0                 cur        f[0]       f[0]       f[0]
//   c1                 z          cur        f[1]       f[1]
//   c2                 z          z          cur        f[2]
//   c3                 z          z          z          cur
//
// where `cur` is the running per-level node value (leaf at level 0), `f[i]`
// are the current frontier siblings at this level, and `z = zeros[level]` is
// the empty-subtree hash.
//
// Frontier writes (slots 0..2 only — slot 3 needs no write because the parent
// advances and a fresh sibling group begins above):
//   frontier_out[level][s] = (slot == s) ? cur : frontier_in[level][s]
//
// `idx_digit[level]` is the quaternary digit of the leaf-index at `level`.
// Each digit is range-checked to {0..3} via Num2Bits(2) here.
template QuaternaryInsert(DEPTH) {
    signal input leaf;
    signal input idx_digit[DEPTH];
    signal input frontier_in[DEPTH][3];

    signal output root;
    signal output frontier_out[DEPTH][3];

    // Precompute zero-subtree roots at each level.
    component zh[DEPTH];
    signal zeros[DEPTH + 1];
    zeros[0] <== 0;
    for (var i = 0; i < DEPTH; i++) {
        zh[i] = Poseidon(5);
        zh[i].inputs[0] <== TAG_MERKLE();
        zh[i].inputs[1] <== zeros[i];
        zh[i].inputs[2] <== zeros[i];
        zh[i].inputs[3] <== zeros[i];
        zh[i].inputs[4] <== zeros[i];
        zeros[i + 1] <== zh[i].out;
    }

    // Per-level component + signal arrays declared up front (Circom 2.x
    // doesn't allow signal declarations inside loop bodies).
    component slot_bits[DEPTH];
    component h[DEPTH];
    signal cur[DEPTH + 1];

    signal b0[DEPTH];
    signal b1[DEPTH];
    signal bb[DEPTH];
    signal s0[DEPTH];
    signal s1[DEPTH];
    signal s2[DEPTH];
    signal s3[DEPTH];

    signal c0[DEPTH];
    signal c1[DEPTH];
    signal c2[DEPTH];
    signal c3[DEPTH];

    signal c0_a[DEPTH];
    signal c0_b[DEPTH];
    signal c1_a[DEPTH];
    signal c1_b[DEPTH];
    signal c1_c[DEPTH];
    signal c2_a[DEPTH];
    signal c2_b[DEPTH];
    signal c2_c[DEPTH];
    signal c3_a[DEPTH];
    signal c3_b[DEPTH];

    signal w0_a[DEPTH];
    signal w0_b[DEPTH];
    signal w1_a[DEPTH];
    signal w1_b[DEPTH];
    signal w2_a[DEPTH];
    signal w2_b[DEPTH];

    cur[0] <== leaf;

    for (var lvl = 0; lvl < DEPTH; lvl++) {
        // Range-check digit to {0..3}.
        slot_bits[lvl] = Num2Bits(2);
        slot_bits[lvl].in <== idx_digit[lvl];

        b0[lvl] <== slot_bits[lvl].out[0];
        b1[lvl] <== slot_bits[lvl].out[1];
        bb[lvl] <== b0[lvl] * b1[lvl];

        // Selectors: s_k = 1 iff slot == k.
        s0[lvl] <== 1 - b0[lvl] - b1[lvl] + bb[lvl];  // (1-b0)*(1-b1)
        s1[lvl] <== b0[lvl] - bb[lvl];                 // b0*(1-b1)
        s2[lvl] <== b1[lvl] - bb[lvl];                 // (1-b0)*b1
        s3[lvl] <== bb[lvl];                            // b0*b1

        // c0 = s0*cur + (1-s0)*f[0]
        c0_a[lvl] <== s0[lvl] * cur[lvl];
        c0_b[lvl] <== (1 - s0[lvl]) * frontier_in[lvl][0];
        c0[lvl] <== c0_a[lvl] + c0_b[lvl];

        // c1 = s0*z + s1*cur + (s2+s3)*f[1]
        c1_a[lvl] <== s0[lvl] * zeros[lvl];
        c1_b[lvl] <== s1[lvl] * cur[lvl];
        c1_c[lvl] <== (s2[lvl] + s3[lvl]) * frontier_in[lvl][1];
        c1[lvl] <== c1_a[lvl] + c1_b[lvl] + c1_c[lvl];

        // c2 = (s0+s1)*z + s2*cur + s3*f[2]
        c2_a[lvl] <== (s0[lvl] + s1[lvl]) * zeros[lvl];
        c2_b[lvl] <== s2[lvl] * cur[lvl];
        c2_c[lvl] <== s3[lvl] * frontier_in[lvl][2];
        c2[lvl] <== c2_a[lvl] + c2_b[lvl] + c2_c[lvl];

        // c3 = (s0+s1+s2)*z + s3*cur
        c3_a[lvl] <== (s0[lvl] + s1[lvl] + s2[lvl]) * zeros[lvl];
        c3_b[lvl] <== s3[lvl] * cur[lvl];
        c3[lvl] <== c3_a[lvl] + c3_b[lvl];

        // Hash level node.
        h[lvl] = Poseidon(5);
        h[lvl].inputs[0] <== TAG_MERKLE();
        h[lvl].inputs[1] <== c0[lvl];
        h[lvl].inputs[2] <== c1[lvl];
        h[lvl].inputs[3] <== c2[lvl];
        h[lvl].inputs[4] <== c3[lvl];
        cur[lvl + 1] <== h[lvl].out;

        // Frontier writes (slots 0..2).
        w0_a[lvl] <== s0[lvl] * cur[lvl];
        w0_b[lvl] <== (1 - s0[lvl]) * frontier_in[lvl][0];
        frontier_out[lvl][0] <== w0_a[lvl] + w0_b[lvl];

        w1_a[lvl] <== s1[lvl] * cur[lvl];
        w1_b[lvl] <== (1 - s1[lvl]) * frontier_in[lvl][1];
        frontier_out[lvl][1] <== w1_a[lvl] + w1_b[lvl];

        w2_a[lvl] <== s2[lvl] * cur[lvl];
        w2_b[lvl] <== (1 - s2[lvl]) * frontier_in[lvl][2];
        frontier_out[lvl][2] <== w2_a[lvl] + w2_b[lvl];
    }

    root <== cur[DEPTH];
}
