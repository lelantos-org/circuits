pragma circom 2.2.3;

// Test wrapper: FixedBaseMul at the width and base MulH uses (RCV_BITS, H).

include "../../lib/fixed_base_mul.circom";
include "../../lib/value_commit.circom";

template TestFixedBaseMulH() {
    signal input scalar;
    signal output out[2];

    var H[2];
    H[0] = H_BASE_X();
    H[1] = H_BASE_Y();

    component mul = FixedBaseMul(RCV_BITS(), H);
    mul.scalar <== scalar;

    out[0] <== mul.out[0];
    out[1] <== mul.out[1];
}

component main = TestFixedBaseMulH();
