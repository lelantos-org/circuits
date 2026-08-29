pragma circom 2.2.3;

// Test wrapper for the raw bit interface, with no booleanity constraint on the
// input. Production does not use it this way: MulH goes through FixedBaseMul,
// which owns its Num2Bits. The template is public, so this pins the behaviour
// when a caller ignores that contract.

include "../../src/lib/fixed_base_mul.circom";
include "../../src/lib/value_commit.circom";

template TestFixedBaseMulBits() {
    signal input e[252];
    signal output out[2];

    var H[2];
    H[0] = H_BASE_X();
    H[1] = H_BASE_Y();

    component mul = FixedBaseMulBits(RCV_BITS(), fixedBaseCoefs(H));
    for (var i = 0; i < 252; i++) {
        mul.e[i] <== e[i];
    }
    out[0] <== mul.out[0];
    out[1] <== mul.out[1];
}

component main = TestFixedBaseMulBits();
