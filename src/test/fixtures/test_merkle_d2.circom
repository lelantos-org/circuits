pragma circom 2.1.0;

// Test wrapper: exposes MerkleRoot at depth 2 so we can unit-test the
// quaternary tree implementation without going through the full transact circuit.
// 4^2 = 16 leaves — small enough to enumerate every position cheaply.

include "../../lib/merkle.circom";

template TestMerkleRootD2() {
    signal input leaf;
    signal input path_elements[2][3];
    signal input path_indices[2];
    signal output root;

    component mr = MerkleRoot(2);
    mr.leaf <== leaf;
    for (var i = 0; i < 2; i++) {
        mr.path_elements[i][0] <== path_elements[i][0];
        mr.path_elements[i][1] <== path_elements[i][1];
        mr.path_elements[i][2] <== path_elements[i][2];
        mr.path_indices[i] <== path_indices[i];
    }
    root <== mr.root;
}

component main = TestMerkleRootD2();
