pragma circom 2.2.3;

// Horner evaluation y = Σ_{k<N} c[k]·z^k.
// Compresses N logical public inputs into the pair (z, y); two distinct
// coefficient vectors collide with probability at most (N-1)/p.
// Coefficient ordering must match contracts/src/lib/PubInputs.sol.
template PolyEval(N) {
    signal input coeffs[N];
    signal input z;
    signal output y;

    signal acc[N + 1];
    acc[0] <== 0;
    for (var i = N; i > 0; i--) {
        acc[N - i + 1] <== acc[N - i] * z + coeffs[i - 1];
    }
    y <== acc[N];
}

// Transact public-input compressor for arbitrary (N_IN, N_OUT).
// Layout, which must match the corresponding PubInputs.sol :: compress overload:
//   [0]                        merkle_root
//   [1 .. 1+N_IN)              nullifier[N_IN]
//   [1+N_IN .. 1+N_IN+N_OUT)   out_cm[N_OUT]
//   next 3                     public_asset_id, public_in, public_out
//   next 2·N_IN                in_cv[N_IN][2]  (row-major)
//   next 2·N_OUT               out_cv[N_OUT][2]
//   next 4                     recipient, chain_id, payer, relayer
//   next 2·N_OUT               out_cv_dep[N_OUT][2]
//   next 3·N_OUT               (clue_Rx, clue_Ry, clue_bits) per output
// Total = 8 + 3·N_IN + 8·N_OUT.
template TransactCompressN(N_IN, N_OUT) {
    var PI_PER_OUT = 3;
    var N = 8 + 3 * N_IN + 5 * N_OUT + PI_PER_OUT * N_OUT;

    signal input z;
    signal input merkle_root;
    signal input nullifier[N_IN];
    signal input out_cm[N_OUT];
    signal input public_asset_id;
    signal input public_in;
    signal input public_out;
    signal input in_cv[N_IN][2];
    signal input out_cv[N_OUT][2];
    signal input recipient_address;
    signal input chain_id;
    signal input payer_address;
    signal input relayer_address;
    signal input out_cv_dep[N_OUT][2];
    signal input out_clue_Rx[N_OUT];
    signal input out_clue_Ry[N_OUT];
    signal input out_clue_bits[N_OUT];

    signal output y;

    component pe = PolyEval(N);
    pe.coeffs[0] <== merkle_root;

    var off = 1;
    for (var i = 0; i < N_IN; i++) {
        pe.coeffs[off + i] <== nullifier[i];
    }
    off = off + N_IN;
    for (var j = 0; j < N_OUT; j++) {
        pe.coeffs[off + j] <== out_cm[j];
    }
    off = off + N_OUT;
    pe.coeffs[off + 0] <== public_asset_id;
    pe.coeffs[off + 1] <== public_in;
    pe.coeffs[off + 2] <== public_out;
    off = off + 3;
    for (var i = 0; i < N_IN; i++) {
        pe.coeffs[off + 2 * i + 0] <== in_cv[i][0];
        pe.coeffs[off + 2 * i + 1] <== in_cv[i][1];
    }
    off = off + 2 * N_IN;
    for (var j = 0; j < N_OUT; j++) {
        pe.coeffs[off + 2 * j + 0] <== out_cv[j][0];
        pe.coeffs[off + 2 * j + 1] <== out_cv[j][1];
    }
    off = off + 2 * N_OUT;
    pe.coeffs[off + 0] <== recipient_address;
    pe.coeffs[off + 1] <== chain_id;
    pe.coeffs[off + 2] <== payer_address;
    pe.coeffs[off + 3] <== relayer_address;
    off = off + 4;
    for (var j = 0; j < N_OUT; j++) {
        pe.coeffs[off + 2 * j + 0] <== out_cv_dep[j][0];
        pe.coeffs[off + 2 * j + 1] <== out_cv_dep[j][1];
    }
    off = off + 2 * N_OUT;
    for (var j = 0; j < N_OUT; j++) {
        pe.coeffs[off + PI_PER_OUT * j + 0] <== out_clue_Rx[j];
        pe.coeffs[off + PI_PER_OUT * j + 1] <== out_clue_Ry[j];
        pe.coeffs[off + PI_PER_OUT * j + 2] <== out_clue_bits[j];
    }
    pe.z <== z;
    y <== pe.y;
}

// TreeUpdateBatch public-input compressor: 4 + 9·MAX_N coefficients → (z, y).
// Layout must match PubInputs.sol :: compress(TreeUpdateBatch).
template BatchCompress(MAX_N) {
    var N = 4 + 9 * MAX_N;

    signal input z;
    signal input old_root;
    signal input new_root;
    signal input start_index;
    signal input actual_count;
    signal input cms[2 * MAX_N];
    signal input cv_dep[2 * MAX_N][2];
    signal input pair_asset[MAX_N];
    signal input pair_public_in[MAX_N];
    signal input is_deposit[MAX_N];

    signal output y;

    component pe = PolyEval(N);
    pe.coeffs[0] <== old_root;
    pe.coeffs[1] <== new_root;
    pe.coeffs[2] <== start_index;
    pe.coeffs[3] <== actual_count;

    var off = 4;
    for (var i = 0; i < 2 * MAX_N; i++) {
        pe.coeffs[off + i] <== cms[i];
    }
    off = off + 2 * MAX_N;
    for (var i = 0; i < 2 * MAX_N; i++) {
        pe.coeffs[off + 2 * i + 0] <== cv_dep[i][0];
        pe.coeffs[off + 2 * i + 1] <== cv_dep[i][1];
    }
    off = off + 4 * MAX_N;
    for (var i = 0; i < MAX_N; i++) {
        pe.coeffs[off + i] <== pair_asset[i];
    }
    off = off + MAX_N;
    for (var i = 0; i < MAX_N; i++) {
        pe.coeffs[off + i] <== pair_public_in[i];
    }
    off = off + MAX_N;
    for (var i = 0; i < MAX_N; i++) {
        pe.coeffs[off + i] <== is_deposit[i];
    }
    pe.z <== z;
    y <== pe.y;
}
