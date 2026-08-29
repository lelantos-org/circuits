pragma circom 2.2.3;

// Test wrapper exposing circomlib's EscalarMulFix and this repo's FixedBaseMul
// side by side, so a test can compare them over arbitrary scalars.
//
// `vectors/` pins their equality for the specific witnesses it carries; this
// fixture covers the general case. Identical group elements mean identical
// cv, cv_dep, leaves and roots.

include "../../src/lib/fixed_base_mul.circom";
include "../../src/lib/value_commit.circom";
include "../../node_modules/circomlib/circuits/bitify.circom";
include "../../node_modules/circomlib/circuits/escalarmulfix.circom";

template TestFixedBaseMulReference() {
    signal input scalar;
    signal output circomlib[2];
    signal output windowed[2];

    var H[2];
    H[0] = H_BASE_X();
    H[1] = H_BASE_Y();

    // circomlib's fixed-base gadget at its native 253-bit width.
    component bits = Num2Bits(253);
    bits.in <== scalar;
    component ref = EscalarMulFix(253, H);
    for (var i = 0; i < 253; i++) {
        ref.e[i] <== bits.out[i];
    }
    circomlib[0] <== ref.out[0];
    circomlib[1] <== ref.out[1];

    component win = FixedBaseMul(RCV_BITS(), H);
    win.scalar <== scalar;
    windowed[0] <== win.out[0];
    windowed[1] <== win.out[1];
}

component main = TestFixedBaseMulReference();
