pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/bitify.circom";
include "../../node_modules/circomlib/circuits/babyjub.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";
include "value_commit.circom";

// Range checks, dummy bookkeeping, and value conservation.

// 64-bit range check. Bits are LSB-first, reused by ValueScalarMul / ValueCommit.
template RangeCheck64() {
    signal input v;
    signal output bits[64];
    component n2b = Num2Bits(64);
    n2b.in <== v;
    for (var i = 0; i < 64; i++) {
        bits[i] <== n2b.out[i];
    }
}

// value·gen with value range-checked to 64 bits. Used for the transparent
// bucket in the transact circuits and for per-pair deposit binding in
// tree_update_batch.
template ValueTimesGen() {
    signal input value;
    signal input gen[2];
    signal output out[2];

    component rng = RangeCheck64();
    rng.v <== value;

    component mul = ValueScalarMul();
    for (var i = 0; i < 64; i++) {
        mul.bits[i] <== rng.bits[i];
    }
    mul.gen[0] <== gen[0];
    mul.gen[1] <== gen[1];

    out[0] <== mul.out[0];
    out[1] <== mul.out[1];
}

// dummy[i] ∈ {0,1} and dummy[i] = 1 ⇒ value[i] = 0.
template DummyZeroValue(N) {
    signal input dummy[N];
    signal input value[N];
    for (var i = 0; i < N; i++) {
        dummy[i] * (dummy[i] - 1) === 0;
        dummy[i] * value[i] === 0;
    }
}

// Explicit per-asset value conservation — the binding balance check.
// PerAssetPointBalance below is defense in depth and is not a substitute.
//
// The point equality alone does not imply conservation. HashToAssetGen is
// circomlib Pedersen over a 72-bit message, which fits in a single segment and
// so reduces to m(asset_id)·BASE[0] for a publicly computable integer m(·).
// Every asset generator therefore lies in the same prime-order group with known
// relative discrete logs. m(·) is ~2^85 and affine in the low nibbles of
// asset_id, so V^1 + V^3 == 2·V^2 exactly, and the point equality is satisfied
// by spending X of asset 1 plus X of asset 3 to mint 2X of asset 2.
//
// This check makes no group-theoretic assumption. For every asset id c present
// in the transaction:
//
//   Σ_i in_value[i]·[in_asset[i] == c]  + public_in ·[public_asset_id == c]
//     == Σ_j out_value[j]·[out_asset[j] == c] + public_out·[public_asset_id == c]
//
// Candidates = {in_asset[*], out_asset[*], public_asset_id}. Any asset outside
// that set contributes zero to both sides, so covering the candidates covers
// every asset present. Dummy inputs carry value 0 (DummyZeroValue) and are
// neutral regardless of the asset_id they declare.
//
// PRECONDITION (soundness-critical): every value passed in must already be
// 64-bit range-checked by the caller. SpentNote / OutputNote apply RangeCheck64
// to in_value / out_value, and the transact circuit applies it to public_in /
// public_out. With at most N_IN+1 terms below 2^64 per side the sums stay under
// 2^66, far below the modulus, so these are exact integer equalities that cannot
// be satisfied by wrapping. Removing a range check breaks this.
template PerAssetValueBalance(N_IN, N_OUT) {
    signal input in_asset[N_IN];
    signal input in_value[N_IN];
    signal input out_asset[N_OUT];
    signal input out_value[N_OUT];
    signal input public_asset_id;
    signal input public_in;
    signal input public_out;

    var N_CAND = N_IN + N_OUT + 1;
    signal cand[N_CAND];
    for (var i = 0; i < N_IN; i++) {
        cand[i] <== in_asset[i];
    }
    for (var j = 0; j < N_OUT; j++) {
        cand[N_IN + j] <== out_asset[j];
    }
    cand[N_IN + N_OUT] <== public_asset_id;

    component pub_eq[N_CAND];
    component in_eq[N_CAND][N_IN];
    component out_eq[N_CAND][N_OUT];
    signal in_term[N_CAND][N_IN];
    signal out_term[N_CAND][N_OUT];
    signal lhs[N_CAND][N_IN + 1];
    signal rhs[N_CAND][N_OUT + 1];

    for (var c = 0; c < N_CAND; c++) {
        pub_eq[c] = IsEqual();
        pub_eq[c].in[0] <== public_asset_id;
        pub_eq[c].in[1] <== cand[c];

        // Transparent bucket contributes to whichever side it sits on.
        lhs[c][0] <== public_in  * pub_eq[c].out;
        rhs[c][0] <== public_out * pub_eq[c].out;

        for (var i = 0; i < N_IN; i++) {
            in_eq[c][i] = IsEqual();
            in_eq[c][i].in[0] <== in_asset[i];
            in_eq[c][i].in[1] <== cand[c];
            in_term[c][i] <== in_value[i] * in_eq[c][i].out;
            lhs[c][i + 1] <== lhs[c][i] + in_term[c][i];
        }
        for (var j = 0; j < N_OUT; j++) {
            out_eq[c][j] = IsEqual();
            out_eq[c][j].in[0] <== out_asset[j];
            out_eq[c][j].in[1] <== cand[c];
            out_term[c][j] <== out_value[j] * out_eq[c][j].out;
            rhs[c][j + 1] <== rhs[c][j] + out_term[c][j];
        }

        lhs[c][N_IN] === rhs[c][N_OUT];
    }
}

// Value balance via Edwards point equality:
//   Σ in_cv + pub_in·V^pub + Σ out_rH  ==  Σ out_cv + pub_out·V^pub + Σ in_rH
// Summing the rH points avoids a Σrcv_in − Σrcv_out field wrap.
//
// Defense in depth only: see PerAssetValueBalance above for why this equation
// does not by itself imply per-asset conservation. It holds for every honest
// transaction and keeps cv a meaningful on-chain value commitment.
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
