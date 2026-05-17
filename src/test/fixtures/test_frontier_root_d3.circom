pragma circom 2.2.3;

// Test wrapper: FrontierRoot at DEPTH=3 (64 leaves). Wrapper decomposes
// scalar start_index into 6 bits.

include "../../../node_modules/circomlib/circuits/bitify.circom";
include "../../lib/frontier_root.circom";

template TestFrontierRootD3() {
    signal input start_index;
    signal input frontier_in[3][3];
    signal output root;

    component bits = Num2Bits(6);
    bits.in <== start_index;

    component fr = FrontierRoot(3);
    for (var k = 0; k < 6; k++) {
        fr.start_index_bits[k] <== bits.out[k];
    }
    for (var d = 0; d < 3; d++) {
        for (var s = 0; s < 3; s++) {
            fr.frontier_in[d][s] <== frontier_in[d][s];
        }
    }
    root <== fr.root;
}

component main = TestFrontierRootD3();
