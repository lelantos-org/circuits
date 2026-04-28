pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/bitify.circom";
include "../../node_modules/circomlib/circuits/babyjub.circom";
include "value_commit.circom";

// Range checks, dummy bookkeeping, and per-asset point-balance check.

// 64-bit range check on a private value. Without this on private signals the
// prover could balance via field-overflow tricks the verifier cannot see.
//
// Exposes the 64 bits LSB-first so callers can thread them straight into
// `ValueScalarMul` / `ValueCommit` and avoid a redundant Num2Bits(64) per
// note. Net: 2 × Num2Bits(64) collapsed to 1 per spent / output / public-
// bucket scalar mul.
template RangeCheck64() {
    signal input v;
    signal output bits[64];
    component n2b = Num2Bits(64);
    n2b.in <== v;
    for (var i = 0; i < 64; i++) {
        bits[i] <== n2b.out[i];
    }
}

// Dummy bookkeeping. Single chokepoint that enforces:
//   1. dummy[i] is boolean: dummy[i] * (dummy[i] - 1) === 0.
//   2. dummy[i] == 1 ⇒ value[i] == 0: dummy[i] * value[i] === 0.
template DummyZeroValue(N) {
    signal input dummy[N];
    signal input value[N];
    for (var i = 0; i < N; i++) {
        dummy[i] * (dummy[i] - 1) === 0;
        dummy[i] * value[i] === 0;
    }
}

// Per-asset value-balance check via Edwards point equality.
//
// Substitute cv_in_i = value_in_i·V_i + rcv_in_i·H and rearrange so the
// rcv·H components cancel:
//
//   Σ in_cv  + public_in · V^pub  + Σ out_rH
//      ==
//   Σ out_cv + public_out · V^pub + Σ in_rH
//
// Equivalent to per-asset value conservation:
//   Σ value_in_i · V_i + public_in · V^pub
//      == Σ value_out_j · V_j + public_out · V^pub
//
// Working with point sums of rH (already computed inside ValueCommit)
// sidesteps the trap of representing `Σrcv_in − Σrcv_out` as a single field
// scalar — that difference can wrap into a 254-bit field element when
// out_rcv > in_rcv, breaking the 253-bit Num2Bits decomposition that a fixed
// scalar mul would need.
//
// Inputs:
//   in_cv[N_IN][2], out_cv[N_OUT][2]    — per-note value commitments
//   in_rH[N_IN][2], out_rH[N_OUT][2]    — per-note rcv·H components
//   pub_in_pt[2], pub_out_pt[2]         — public_in / out · V^pub
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
