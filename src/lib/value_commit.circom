pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/bitify.circom";
include "../../node_modules/circomlib/circuits/babyjub.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";
include "../../node_modules/circomlib/circuits/escalarmulany.circom";
include "../../node_modules/circomlib/circuits/escalarmulfix.circom";

// Sapling-style value commitment over Baby-Jubjub:
//   cv = value * AssetGen + rcv * H
//
// Inputs:
//   value (≤ 2^64, range-checked outside this lib)
//   gen[2] = AssetGen (Edwards point; output of HashToAssetGen for per-note
//                      assets, or witnessed point for the public bucket)
//   rcv (253-bit blinding scalar)
//
// H is a fixed Baby-Jubjub generator independent of any AssetGen output.
// HashToAssetGen runs circomlib Pedersen on 72 bits (TAG_ASSET || asset_id),
// which compiles into 1 segment and consumes Pedersen BASE[0]. We pick
// H = BASE[2]: outside the image of HashToAssetGen and therefore independent.

function H_BASE_X() {
    return 5802099305472655231388284418920769829666717045250560929368476121199858275951;
}
function H_BASE_Y() {
    return 5980429700218124965372158798884772646841287887664001482443826541541529227896;
}

// Variable-base scalar multiplication value · gen.
// Scalar consumed as pre-decomposed 64 bits LSB-first; the caller MUST run
// `RangeCheck64` on the originating value and pipe its `bits` output here.
// Threading the bits avoids a redundant Num2Bits(64) per scalar mul (~64
// constraints saved per call × 6 call sites in Transact(_,2,2) ≈ ~380
// constraints).
//
// EscalarMulAny handles scalar=0 → identity (0,1) and gracefully accepts the
// identity as a base. Dummy notes (value=0) therefore contribute identity to
// any subsequent point sum, which is the additive neutral element on Edwards.
//
// Cost ≈ 2k constraints (one segment, 64 bits).
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

// Fixed-base scalar multiplication rcv · H. 253-bit scalar; caller decomposes
// rcv elsewhere if it wants a tighter bound. Used both per-note (rcv) and
// once over the rcv_delta in the balance check.
//
// Cost ≈ 3k constraints.
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

// cv = value · gen + rcv · H. Sapling-style hiding value commitment.
// Public output of the transact circuit so off-chain auditors can verify
// per-asset balance without redoing the SNARK. Also exposes the rcv·H
// component so the balance check can sum rH points across notes (avoids the
// scalar-sum-can-be-negative trap of working with `Σrcv_in − Σrcv_out` in
// field arithmetic).
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

// Chained Edwards point sum over N points. PointSum(0).out is the identity
// (0,1). BabyAdd is complete on the prime-order subgroup our points live in.
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
