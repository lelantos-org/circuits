pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/bitify.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";

// Range checks, dummy bookkeeping, and value conservation.

// 64-bit range check. Applied to every value and every asset id: the first
// keeps the conservation sums below the modulus (PerAssetValueBalance), and the
// pair makes NoteCommitment's packing injective.
template RangeCheck64() {
    signal input v;
    component n2b = Num2Bits(64);
    n2b.in <== v;
}

// dummy[i] != 0 ⇒ value[i] = 0. The caller makes dummy[i] boolean: SpentNote
// does, through MerkleProofOrDummy.
template DummyZeroValue(N) {
    signal input dummy[N];
    signal input value[N];
    for (var i = 0; i < N; i++) {
        dummy[i] * value[i] === 0;
    }
}

// Per-asset value conservation. For every asset id c in
// {in_asset[*], out_asset[*], public_asset_id}:
//
//   Σ_i in_value[i]·[in_asset[i] == c]
//     == Σ_j out_value[j]·[out_asset[j] == c] + public_out·[public_asset_id == c]
//
// Any other asset contributes zero to both sides. The transparent amount is on
// the output side only: a transact proof never moves tokens in. Dummy inputs
// carry value 0 (DummyZeroValue), whatever asset_id they declare.
//
// Precondition: the caller 64-bit range-checks every value (SpentNote and
// OutputNote for in_value and out_value, the transact circuit for public_out).
// Each side then sums at most max(N_IN, N_OUT + 1) terms below 2^64, so the
// equalities hold over the integers, without field wraparound.
template PerAssetValueBalance(N_IN, N_OUT) {
    signal input in_asset[N_IN];
    signal input in_value[N_IN];
    signal input out_asset[N_OUT];
    signal input out_value[N_OUT];
    signal input public_asset_id;
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

        lhs[c][0] <== 0;
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
