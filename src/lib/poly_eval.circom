pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/comparators.circom";
include "../../node_modules/circomlib/circuits/poseidon.circom";
include "tags.circom";

// Horner evaluation y = Σ_{k<N} c[k]·z^k.
// Compresses N logical public inputs into the public signals (y, z), in that
// order. Coefficient ordering must match contracts/src/lib/PubInputs.sol.
//
// `z` is derived from prover-authored calldata, so the prover reads it before
// choosing a witness and the evaluation alone binds nothing. Both consumers
// (TransactCompressN, BatchCompress) also output a CoeffDigest of their
// coefficients, which the contract hashes into z; see TransactCompressN.
//
// z != 0 is enforced here. At z = 0 the Horner chain reduces to y === coeffs[0]
// and the remaining N-1 coefficients do not affect y.
template PolyEval(N) {
    signal input coeffs[N];
    signal input z;
    signal output y;

    component z_nz = IsZero();
    z_nz.in <== z;
    z_nz.out === 0;

    signal acc[N + 1];
    acc[0] <== 0;
    for (var i = N; i > 0; i--) {
        acc[N - i + 1] <== acc[N - i] * z + coeffs[i - 1];
    }
    y <== acc[N];
}

// Commitment to M field elements: a Poseidon(5) fold, four words per block.
//
//   h_0     = Poseidon(TAG_DIGEST, in[0..3])
//   h_{b+1} = Poseidon(h_b,        in[4b+4 .. 4b+7])
//
// The last block is zero-padded. M is a template parameter, so the padding is
// not ambiguous. TAG_DIGEST separates block 0 from a Merkle node (TAG_MERKLE).
// Binding reduces to collision resistance of Poseidon(5).
template CoeffDigest(M) {
    assert(M >= 1);
    var BLOCKS = (M + 3) \ 4;

    signal input in[M];
    signal output out;

    component h[BLOCKS];
    for (var b = 0; b < BLOCKS; b++) {
        h[b] = Poseidon(5);
        if (b == 0) {
            // Hoisted through a `var`; see tags.circom.
            var tag = TAG_DIGEST();
            h[b].inputs[0] <== tag;
        } else {
            h[b].inputs[0] <== h[b - 1].out;
        }
        for (var i = 0; i < 4; i++) {
            if (4 * b + i < M) {
                h[b].inputs[1 + i] <== in[4 * b + i];
            } else {
                h[b].inputs[1 + i] <== 0;
            }
        }
    }
    out <== h[BLOCKS - 1].out;
}

// Transact public-input compressor for arbitrary (N_IN, N_OUT).
// Coefficient layout, which must match the corresponding
// PubInputs.sol :: compress overload:
//   [0]                        merkle_root
//   [1 .. 1+N_IN)              nullifier[N_IN]
//   [1+N_IN .. 1+N_IN+N_OUT)   out_cm[N_OUT]
//   next 2                     public_asset_id, public_out
// Total = 3 + N_IN + N_OUT.
//
// Outputs y, the evaluation, and digest, the CoeffDigest of the same
// coefficients in the same order. The instantiating circuit exposes both as
// public signals.
//
// Binding. The contract reads the digest word d from calldata, derives
// z = keccak(coefficients, d, challenge-only words), computes y over the
// calldata coefficients c, and verifies against (y, d, z). The proof shows a
// witness w with CoeffDigest(w) == d and Σ w_k·z^k == y. d is in the preimage
// of z, so under collision resistance of Poseidon(5) w is fixed before z. If
// w != c, two distinct polynomials of degree < N agree at a random z with
// probability at most (N - 1)/r, taking keccak256 as a random oracle.
//
// Conditions on the consumer:
//   * d is passed to the verifier as the digest public signal, unmodified;
//   * d and every coefficient are in the keccak preimage of z.
// d is not a coefficient: it is not evaluated into y.
//
// Each coefficient is also constrained outside this template: the root and
// nullifiers by SpentNote, the commitments by OutputNote, the two public
// scalars by RangeCheck64 and PerAssetValueBalance.
//
// recipient_address, chain_id, payer_address, relayer_address, intent_hash,
// out_aux_digest and the 3·N_OUT FMD clue fields are not signals of the
// circuit and are therefore not coefficients. PubInputs.sol binds them by
// including them in the keccak preimage of z.
template TransactCompressN(N_IN, N_OUT) {
    var N = 3 + N_IN + N_OUT;

    signal input z;
    signal input merkle_root;
    signal input nullifier[N_IN];
    signal input out_cm[N_OUT];
    signal input public_asset_id;
    signal input public_out;

    signal output y;
    signal output digest;

    // The ordered coefficients, once: they feed both the digest and the
    // polynomial, so the two cannot disagree on order.
    signal prefix[N];
    prefix[0] <== merkle_root;

    var off = 1;
    for (var i = 0; i < N_IN; i++) {
        prefix[off + i] <== nullifier[i];
    }
    off = off + N_IN;
    for (var j = 0; j < N_OUT; j++) {
        prefix[off + j] <== out_cm[j];
    }
    off = off + N_OUT;
    prefix[off + 0] <== public_asset_id;
    prefix[off + 1] <== public_out;

    component dg = CoeffDigest(N);
    for (var k = 0; k < N; k++) {
        dg.in[k] <== prefix[k];
    }
    digest <== dg.out;

    component pe = PolyEval(N);
    for (var k = 0; k < N; k++) {
        pe.coeffs[k] <== prefix[k];
    }
    pe.z <== z;
    y <== pe.y;
}

// TreeUpdateBatch public-input compressor: 4 + 4·MAX_L coefficients to
// (y, digest, z). Layout must match PubInputs.sol :: compress(TreeUpdateBatch).
//
// Every array is indexed by leaf slot. Every word is a signal of
// TreeUpdateBatch, so every word is a coefficient: a signal hashed into z
// without being evaluated is not bound to calldata.
//
// digest is the CoeffDigest of all the coefficients, in layout order, and is a
// public signal; binding is as in TransactCompressN. new_root cannot serve as
// that commitment: a zero leaf is the empty leaf, so a run with a trailing zero
// leaf and a shorter run have the same roots.
//
// The two uint64 blocks (leaf_asset, leaf_public_in) are adjacent and the uint8
// block (is_deposit) follows them, so PubInputs.compress re-masks the sub-word
// members with two contiguous loops.
template BatchCompress(MAX_L) {
    var N = 4 + 4 * MAX_L;

    signal input z;
    signal input old_root;
    signal input new_root;
    signal input start_index;
    signal input actual_count;
    signal input cms[MAX_L];
    signal input leaf_asset[MAX_L];
    signal input leaf_public_in[MAX_L];
    signal input is_deposit[MAX_L];

    signal output y;
    signal output digest;

    signal coeffs[N];
    coeffs[0] <== old_root;
    coeffs[1] <== new_root;
    coeffs[2] <== start_index;
    coeffs[3] <== actual_count;

    var off = 4;
    for (var k = 0; k < MAX_L; k++) {
        coeffs[off + k] <== cms[k];
    }
    off = off + MAX_L;
    for (var k = 0; k < MAX_L; k++) {
        coeffs[off + k] <== leaf_asset[k];
    }
    off = off + MAX_L;
    for (var k = 0; k < MAX_L; k++) {
        coeffs[off + k] <== leaf_public_in[k];
    }
    off = off + MAX_L;
    for (var k = 0; k < MAX_L; k++) {
        coeffs[off + k] <== is_deposit[k];
    }

    component dg = CoeffDigest(N);
    for (var k = 0; k < N; k++) {
        dg.in[k] <== coeffs[k];
    }
    digest <== dg.out;

    component pe = PolyEval(N);
    for (var k = 0; k < N; k++) {
        pe.coeffs[k] <== coeffs[k];
    }
    pe.z <== z;
    y <== pe.y;
}
