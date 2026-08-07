pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/bitify.circom";
include "../../node_modules/circomlib/circuits/babyjub.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";
include "../../node_modules/circomlib/circuits/escalarmulany.circom";
include "../../node_modules/circomlib/circuits/escalarmulfix.circom";

// Baby-Jubjub value commitments: cv = value·gen + rcv·H.
//   gen — HashToAssetGen output, or the transparent-bucket point.
//   rcv — 253-bit blinder.
// H is Pedersen BASE[2] and gen derives from BASE[0], so their images are
// disjoint.

function H_BASE_X() {
    return 5802099305472655231388284418920769829666717045250560929368476121199858275951;
}
function H_BASE_Y() {
    return 5980429700218124965372158798884772646841287887664001482443826541541529227896;
}

// Variable-base scalar multiplication value·gen, bits LSB-first from
// RangeCheck64. value = 0 yields the identity (0, 1).
template ValueScalarMul() {
    signal input bits[64];
    signal input gen[2];
    signal output out[2];

    component mul = EscalarMulAny(64);
    for (var i = 0; i < 64; i++) {
        mul.e[i] <== bits[i];
    }
    mul.p[0] <== gen[0];
    mul.p[1] <== gen[1];

    out[0] <== mul.out[0];
    out[1] <== mul.out[1];
}

// Fixed-base scalar multiplication rcv·H with a 253-bit scalar.
template MulH() {
    signal input scalar;
    signal output out[2];

    var H[2];
    H[0] = H_BASE_X();
    H[1] = H_BASE_Y();

    component bits = Num2Bits(253);
    bits.in <== scalar;

    component mul = EscalarMulFix(253, H);
    for (var i = 0; i < 253; i++) {
        mul.e[i] <== bits.out[i];
    }
    out[0] <== mul.out[0];
    out[1] <== mul.out[1];
}

// cv = value·gen + rcv·H. rH is exposed for PerAssetPointBalance.
template ValueCommit() {
    signal input bits[64];
    signal input gen[2];
    signal input rcv;
    signal output cv[2];
    signal output rH[2];

    component vt = ValueScalarMul();
    for (var i = 0; i < 64; i++) {
        vt.bits[i] <== bits[i];
    }
    vt.gen[0] <== gen[0];
    vt.gen[1] <== gen[1];

    component rHmul = MulH();
    rHmul.scalar <== rcv;

    component add = BabyAdd();
    add.x1 <== vt.out[0];
    add.y1 <== vt.out[1];
    add.x2 <== rHmul.out[0];
    add.y2 <== rHmul.out[1];

    cv[0] <== add.xout;
    cv[1] <== add.yout;
    rH[0] <== rHmul.out[0];
    rH[1] <== rHmul.out[1];
}

// Chained Edwards point sum. PointSum(0) is the identity (0, 1).
template PointSum(N) {
    signal input pts[N][2];
    signal output out[2];

    if (N == 0) {
        out[0] <== 0;
        out[1] <== 1;
    } else if (N == 1) {
        out[0] <== pts[0][0];
        out[1] <== pts[0][1];
    } else {
        component adders[N - 1];
        for (var i = 0; i < N - 1; i++) {
            adders[i] = BabyAdd();
            if (i == 0) {
                adders[i].x1 <== pts[0][0];
                adders[i].y1 <== pts[0][1];
            } else {
                adders[i].x1 <== adders[i - 1].xout;
                adders[i].y1 <== adders[i - 1].yout;
            }
            adders[i].x2 <== pts[i + 1][0];
            adders[i].y2 <== pts[i + 1][1];
        }
        out[0] <== adders[N - 2].xout;
        out[1] <== adders[N - 2].yout;
    }
}
