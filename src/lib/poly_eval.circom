pragma circom 2.2.3;

// Horner-form polynomial evaluation: y = Σ c[k]·z^k for k ∈ [0, N).
// Compresses N logical PIs into a single (z, y) pair. Schwartz–Zippel:
// collision prob ≤ (N-1)/p over BN254 scalar — negligible.
// Coefficient ordering MUST match contracts/src/lib/PubInputs.sol byte-for-byte.
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

// Transact PI compressor: 24 base + 3·N_OUT clue coeffs → (z, y).
// Layout MUST match PubInputs.sol :: compress(Transact, aux). Slot layout
// documented in src/2x2.circom header.
template TransactCompress(N_OUT) {
    var PI_BASE = 24;          // 20 base + 4 cv_dep coords
    var PI_PER_OUT = 3;        // (clueRx, clueRy, clueBits)
    var N = PI_BASE + PI_PER_OUT * N_OUT;

    signal input z;

    // Base 24 logical PIs.
    signal input merkle_root;
    signal input nullifier[2];
    signal input out_cm[2];
    signal input public_asset_id;
    signal input public_in;
    signal input public_out;
    signal input in_cv[2][2];
    signal input out_cv[2][2];
    signal input recipient_address;
    signal input chain_id;
    signal input payer_address;
    signal input relayer_address;
    signal input out_cv_dep[2][2];

    // Per-output clue PIs.
    signal input out_clue_Rx[N_OUT];
    signal input out_clue_Ry[N_OUT];
    signal input out_clue_bits[N_OUT];

    signal output y;

    component pe = PolyEval(N);
    pe.coeffs[ 0] <== merkle_root;
    pe.coeffs[ 1] <== nullifier[0];
    pe.coeffs[ 2] <== nullifier[1];
    pe.coeffs[ 3] <== out_cm[0];
    pe.coeffs[ 4] <== out_cm[1];
    pe.coeffs[ 5] <== public_asset_id;
    pe.coeffs[ 6] <== public_in;
    pe.coeffs[ 7] <== public_out;
    pe.coeffs[ 8] <== in_cv[0][0];
    pe.coeffs[ 9] <== in_cv[0][1];
    pe.coeffs[10] <== in_cv[1][0];
    pe.coeffs[11] <== in_cv[1][1];
    pe.coeffs[12] <== out_cv[0][0];
    pe.coeffs[13] <== out_cv[0][1];
    pe.coeffs[14] <== out_cv[1][0];
    pe.coeffs[15] <== out_cv[1][1];
    pe.coeffs[16] <== recipient_address;
    pe.coeffs[17] <== chain_id;
    pe.coeffs[18] <== payer_address;
    pe.coeffs[19] <== relayer_address;
    pe.coeffs[20] <== out_cv_dep[0][0];
    pe.coeffs[21] <== out_cv_dep[0][1];
    pe.coeffs[22] <== out_cv_dep[1][0];
    pe.coeffs[23] <== out_cv_dep[1][1];
    for (var j = 0; j < N_OUT; j++) {
        pe.coeffs[PI_BASE + PI_PER_OUT * j + 0] <== out_clue_Rx[j];
        pe.coeffs[PI_BASE + PI_PER_OUT * j + 1] <== out_clue_Ry[j];
        pe.coeffs[PI_BASE + PI_PER_OUT * j + 2] <== out_clue_bits[j];
    }
    pe.z <== z;
    y <== pe.y;
}

// TreeUpdateBatch PI compressor: 4 + 9·MAX_N coeffs → (z, y).
// Layout MUST match PubInputs.sol :: compress(TreeUpdateBatch); slot layout
// in tree_update_batch.circom header.
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
