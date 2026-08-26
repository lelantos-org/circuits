pragma circom 2.2.3;

// Horner evaluation y = Σ_{k<N} c[k]·z^k.
// Compresses N logical public inputs into the public signals (y, z), in that
// order; two distinct coefficient vectors collide with probability at most
// (N-1)/p. Coefficient ordering must match contracts/src/lib/PubInputs.sol.
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
//   last 1                     out_aux_digest
// Total = 9 + 3·N_IN + 8·N_OUT.
//
// out_aux_digest binds the encrypted-note payload the relayer carries in
// calldata: keccak256(abi.encode(aux)) mod r over the full AuxValidation.Output
// array. Without it only the three clue fields per output are bound, so a
// relayer could keep the FMD clue intact — proof still verifies, recipient
// still flags the note — while corrupting ephPub/ciphertext, leaving the
// recipient unable to decrypt the opening of a note whose inputs are already
// spent. It is appended after the clue block so slots
// 0..(8+3·N_IN+8·N_OUT-1) keep their indices.
template TransactCompressN(N_IN, N_OUT) {
    var PI_PER_OUT = 3;
    var N = 9 + 3 * N_IN + 5 * N_OUT + PI_PER_OUT * N_OUT;

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
    signal input out_aux_digest;

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
    off = off + PI_PER_OUT * N_OUT;
    pe.coeffs[off] <== out_aux_digest;
    pe.z <== z;
    y <== pe.y;
}

// TreeUpdateBatch public-input compressor: 4 + 6·MAX_L coefficients → (y, z).
// Layout must match PubInputs.sol :: compress(TreeUpdateBatch).
//
// Every array is indexed by leaf slot: a batch commits to actual_count
// individual leaves, so the deposit-binding fields (leaf_asset, leaf_public_in,
// is_deposit) are MAX_L wide.
//
// The two uint64 blocks (leaf_asset, leaf_public_in) are adjacent and the uint8
// block (is_deposit) follows them, so PubInputs.compress can re-mask the
// sub-word members with two contiguous loops over the copied calldata.
template BatchCompress(MAX_L) {
    var N = 4 + 6 * MAX_L;

    signal input z;
    signal input old_root;
    signal input new_root;
    signal input start_index;
    signal input actual_count;
    signal input cms[MAX_L];
    signal input cv_dep[MAX_L][2];
    signal input leaf_asset[MAX_L];
    signal input leaf_public_in[MAX_L];
    signal input is_deposit[MAX_L];

    signal output y;

    component pe = PolyEval(N);
    pe.coeffs[0] <== old_root;
    pe.coeffs[1] <== new_root;
    pe.coeffs[2] <== start_index;
    pe.coeffs[3] <== actual_count;

    var off = 4;
    for (var k = 0; k < MAX_L; k++) {
        pe.coeffs[off + k] <== cms[k];
    }
    off = off + MAX_L;
    for (var k = 0; k < MAX_L; k++) {
        pe.coeffs[off + 2 * k + 0] <== cv_dep[k][0];
        pe.coeffs[off + 2 * k + 1] <== cv_dep[k][1];
    }
    off = off + 2 * MAX_L;
    for (var k = 0; k < MAX_L; k++) {
        pe.coeffs[off + k] <== leaf_asset[k];
    }
    off = off + MAX_L;
    for (var k = 0; k < MAX_L; k++) {
        pe.coeffs[off + k] <== leaf_public_in[k];
    }
    off = off + MAX_L;
    for (var k = 0; k < MAX_L; k++) {
        pe.coeffs[off + k] <== is_deposit[k];
    }
    pe.z <== z;
    y <== pe.y;
}
