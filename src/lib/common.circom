pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/poseidon.circom";
include "../../node_modules/circomlib/circuits/bitify.circom";
include "tags.circom";

// 2-bit quaternary digit decomposition + one-hot selectors.
//   path_index ∈ {0..3} → bits[0..1] (LSB-first) + s[k] = 1 iff path_index == k.
//   s[0]=(1-b0)(1-b1), s[1]=b0(1-b1), s[2]=(1-b0)b1, s[3]=b0·b1.
// Cost: 1 quadratic (bb = b0·b1); rest linear. Used by MerkleLevel4 and
// QuaternaryInsertLevel.
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

// Empty-subtree hash ladder (quaternary, TAG_MERKLE).
//   zeros[0]   = 0
//   zeros[d+1] = Poseidon(TAG_MERKLE, zeros[d]×4)
// Used by QuaternaryInsert (empty siblings) and FrontierRoot (right-of-cursor
// branches). MUST share TAG_MERKLE with MerkleLevel4 to prevent collisions.
template EmptySubtreeHashes(DEPTH) {
    signal output zeros[DEPTH + 1];

    component zh[DEPTH];
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
}
