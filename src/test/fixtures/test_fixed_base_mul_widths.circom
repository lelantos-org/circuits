pragma circom 2.2.3;

// Test wrapper: FixedBaseMul at widths that exercise the branches the 252-bit
// production instance never reaches.
//
//   4 bits -> nWindows == 1, the branch that bypasses the accumulator entirely
//   6 bits -> nWindows == 2 with the top window zero-padded (6 is not a multiple of 4)
//   8 bits -> nWindows == 2, both full; small enough to enumerate exhaustively

include "../../lib/fixed_base_mul.circom";
include "../../lib/value_commit.circom";

template TestFixedBaseMulWidths() {
    signal input s4;
    signal input s6;
    signal input s8;
    signal output o4[2];
    signal output o6[2];
    signal output o8[2];

    var H[2];
    H[0] = H_BASE_X();
    H[1] = H_BASE_Y();

    component m4 = FixedBaseMul(4, H);
    m4.scalar <== s4;
    o4[0] <== m4.out[0];
    o4[1] <== m4.out[1];

    component m6 = FixedBaseMul(6, H);
    m6.scalar <== s6;
    o6[0] <== m6.out[0];
    o6[1] <== m6.out[1];

    component m8 = FixedBaseMul(8, H);
    m8.scalar <== s8;
    o8[0] <== m8.out[0];
    o8[1] <== m8.out[1];
}

component main = TestFixedBaseMulWidths();
