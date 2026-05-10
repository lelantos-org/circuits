pragma circom 2.2.3;

// Test wrapper: depth-3 quaternary FrontierRoot (4^3 = 64 leaves). Small
// enough to enumerate every per-level digit, large enough to exercise all
// pre/eq/post branches at multiple levels simultaneously.
//
// Accepts `start_index` as a scalar; wrapper Num2Bits(6) decomposes into
// the 2·DEPTH bits FrontierRoot expects.

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
