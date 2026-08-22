pragma circom 2.2.3;

// Test wrapper exposing circomlib's EscalarMulFix and FixedBaseMul side by
// side, so a test can compare them over arbitrary scalars.
//
// `vectors/` pins their equality for the specific witnesses it carries; this
// fixture covers the general case. Identical group elements mean identical
// cv, cv_dep, leaves and roots.

include "../../lib/fixed_base_mul.circom";
include "../../lib/value_commit.circom";
include "../../../node_modules/circomlib/circuits/bitify.circom";
include "../../../node_modules/circomlib/circuits/escalarmulfix.circom";

template TestFixedBaseMulLegacy() {
    signal input scalar;
    signal output legacy[2];
    signal output current[2];

    var H[2];
    H[0] = H_BASE_X();
    H[1] = H_BASE_Y();

    // Exactly the old MulH body: Num2Bits(253) + EscalarMulFix(253, H).
    component bits = Num2Bits(253);
    bits.in <== scalar;
    component old = EscalarMulFix(253, H);
    for (var i = 0; i < 253; i++) {
        old.e[i] <== bits.out[i];
    }
    legacy[0] <== old.out[0];
    legacy[1] <== old.out[1];

    component now = FixedBaseMul(RCV_BITS(), H);
    now.scalar <== scalar;
    current[0] <== now.out[0];
    current[1] <== now.out[1];
}

component main = TestFixedBaseMulLegacy();
