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

// Two commitments to the SAME (value, gen) under independent blinders, sharing
// one variable-base scalar multiplication:
//   cv     = value·gen + rcv·H
//   cv_dep = value·gen + rcv_dep·H
//
// Every note needs exactly this pair: `cv` is the per-spend re-randomisation
// published in the transaction, `cv_dep` is the note's permanent blinding that
// reproduces its committed leaf. The two blinders MUST stay independent — if
// rcv == rcv_dep then in_cv at spend time equals the leaf's cv_dep and an
// observer learns which leaf was spent.
//
// The value·gen term is identical across the two, so it is computed once and
// each blinder added to it, saving one EscalarMulAny(64) per note slot.
//
// rH / rH_dep are exposed for PerAssetPointBalance.
template ValueCommitPair() {
    signal input bits[64];
    signal input gen[2];
    signal input rcv;
    signal input rcv_dep;
    signal output cv[2];
    signal output rH[2];
    signal output cv_dep[2];
    signal output rH_dep[2];

    // The shared term, computed once.
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

    component rHmul_dep = MulH();
    rHmul_dep.scalar <== rcv_dep;

    component add_dep = BabyAdd();
    add_dep.x1 <== vt.out[0];
    add_dep.y1 <== vt.out[1];
    add_dep.x2 <== rHmul_dep.out[0];
    add_dep.y2 <== rHmul_dep.out[1];

    cv_dep[0] <== add_dep.xout;
    cv_dep[1] <== add_dep.yout;
    rH_dep[0] <== rHmul_dep.out[0];
    rH_dep[1] <== rHmul_dep.out[1];
}

// cv = value·gen + rcv·H. rH is exposed for PerAssetPointBalance.
// Single-blinder form, used where only one commitment is needed.
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
