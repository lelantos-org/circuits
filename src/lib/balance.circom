pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/bitify.circom";
include "../../node_modules/circomlib/circuits/babyjub.circom";
include "value_commit.circom";

// Range checks, dummy bookkeeping, and per-asset point-balance check.

// 64-bit range check on a private value. Prevents field-wrap attacks on
// Σ value_in − Σ value_out. Exposes bits LSB-first so callers can thread
// them into ValueScalarMul / ValueCommit without a second Num2Bits(64).
template RangeCheck64() {
    signal input v;
    signal output bits[64];
    component n2b = Num2Bits(64);
    n2b.in <== v;
    for (var i = 0; i < 64; i++) {
        bits[i] <== n2b.out[i];
    }
}

// Dummy bookkeeping: dummy[i] ∈ {0,1} and dummy[i] = 1 ⇒ value[i] = 0.
template DummyZeroValue(N) {
    signal input dummy[N];
    signal input value[N];
    for (var i = 0; i < N; i++) {
        dummy[i] * (dummy[i] - 1) === 0;
        dummy[i] * value[i] === 0;
    }
}

// Per-asset value-balance via Edwards point equality:
//   Σ in_cv + public_in·V^pub + Σ out_rH  ==  Σ out_cv + public_out·V^pub + Σ in_rH
//
// Substituting cv = value·V + rcv·H makes rcv·H cancel, leaving per-asset
// value conservation. Summing rH points instead of representing
// Σrcv_in − Σrcv_out as a scalar avoids 254-bit field wrap when out_rcv > in_rcv.
template PerAssetPointBalance(N_IN, N_OUT) {
    signal input in_cv[N_IN][2];
    signal input out_cv[N_OUT][2];
    signal input in_rH[N_IN][2];
    signal input out_rH[N_OUT][2];
    signal input pub_in_pt[2];
    signal input pub_out_pt[2];

    // LHS: Σ in_cv ⊕ pub_in_pt ⊕ Σ out_rH
    component lhs = PointSum(N_IN + 1 + N_OUT);
    var idx;
    idx = 0;
    for (var i = 0; i < N_IN; i++) {
        lhs.pts[idx][0] <== in_cv[i][0];
        lhs.pts[idx][1] <== in_cv[i][1];
        idx++;
    }
    lhs.pts[idx][0] <== pub_in_pt[0];
    lhs.pts[idx][1] <== pub_in_pt[1];
    idx++;
    for (var j = 0; j < N_OUT; j++) {
        lhs.pts[idx][0] <== out_rH[j][0];
        lhs.pts[idx][1] <== out_rH[j][1];
        idx++;
    }

    // RHS: Σ out_cv ⊕ pub_out_pt ⊕ Σ in_rH
    component rhs = PointSum(N_OUT + 1 + N_IN);
    idx = 0;
    for (var j = 0; j < N_OUT; j++) {
        rhs.pts[idx][0] <== out_cv[j][0];
        rhs.pts[idx][1] <== out_cv[j][1];
        idx++;
    }
    rhs.pts[idx][0] <== pub_out_pt[0];
    rhs.pts[idx][1] <== pub_out_pt[1];
    idx++;
    for (var i = 0; i < N_IN; i++) {
        rhs.pts[idx][0] <== in_rH[i][0];
        rhs.pts[idx][1] <== in_rH[i][1];
        idx++;
    }

    lhs.out[0] === rhs.out[0];
    lhs.out[1] === rhs.out[1];
}
