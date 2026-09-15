pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/comparators.circom";

// Horner evaluation y = Σ_{k<N} c[k]·z^k.
// Compresses N logical public inputs into the public signals (y, z), in that
// order. Coefficient ordering must match contracts/src/lib/PubInputs.sol.
//
// Binding condition: every coefficient must be pinned by a constraint elsewhere
// in the circuit. `z` is a circuit input derived from prover-authored calldata,
// so the prover reads it before choosing a witness. The Schwartz-Zippel bound
// requires the coefficient vector fixed before the challenge and does not apply
// in that order. PolyEval is affine in each coefficient with slope z^k, so an
// unpinned coefficient is one linear equation in one unknown: solving it makes
// y match the contract's value for an unrelated witness.
//
// z != 0 is enforced here. At z = 0 the Horner chain reduces to y === coeffs[0]
// and the remaining N-1 coefficients do not affect the public signals. The
// consumer derives z as keccak256(challenge) mod r, which is 0 only with
// negligible probability; the circuit rejects z = 0 independently of that
// derivation.
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

// Transact public-input compressor for arbitrary (N_IN, N_OUT).
// Layout, which must match the corresponding PubInputs.sol :: compress overload:
//   [0]                        merkle_root
//   [1 .. 1+N_IN)              nullifier[N_IN]
//   [1+N_IN .. 1+N_IN+N_OUT)   out_cm[N_OUT]
//   next 3                     public_asset_id, public_in, public_out
//   next 2·N_IN                in_cv[N_IN][2]  (row-major)
//   next 2·N_OUT               out_cv[N_OUT][2]
//   next 2·N_OUT               out_cv_dep[N_OUT][2]
// Total = 4 + 3·N_IN + 5·N_OUT.
//
// Each coefficient is pinned by a constraint outside this template: the root
// and nullifiers by SpentNote, the commitments by Poseidon, the value
// commitments by ValueCommit, the three public scalars by RangeCheck64 and
// PerAssetValueBalance.
//
// recipient_address, chain_id, payer_address, relayer_address, intent_hash,
// out_aux_digest and the 3·N_OUT FMD clue fields have no in-circuit constraint
// and are therefore not coefficients. PubInputs.sol includes them in the keccak
// preimage of z, so altering any of them changes z, hence y, and invalidates
// the proof.
//
// A new coefficient must be wired in here and pinned by a constraint elsewhere;
// a value with no such constraint belongs in the challenge preimage instead.
template TransactCompressN(N_IN, N_OUT) {
    var N = 4 + 3 * N_IN + 5 * N_OUT;

    signal input z;
    signal input merkle_root;
    signal input nullifier[N_IN];
    signal input out_cm[N_OUT];
    signal input public_asset_id;
    signal input public_in;
    signal input public_out;
    signal input in_cv[N_IN][2];
    signal input out_cv[N_OUT][2];
    signal input out_cv_dep[N_OUT][2];

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
    for (var j = 0; j < N_OUT; j++) {
        pe.coeffs[off + 2 * j + 0] <== out_cv_dep[j][0];
        pe.coeffs[off + 2 * j + 1] <== out_cv_dep[j][1];
    }
    pe.z <== z;
    y <== pe.y;
}

// TreeUpdateBatch public-input compressor: 4 + 6·MAX_L coefficients to (y, z).
// Layout must match PubInputs.sol :: compress(TreeUpdateBatch).
//
// Every array is indexed by leaf slot, so the deposit-binding fields
// (leaf_asset, leaf_public_in, is_deposit) are MAX_L wide. All three are
// coefficients: the challenge preimage and the coefficient vector are the same
// 4 + 6·MAX_L words, and PubInputs.compress evaluates the whole span.
//
// What pins them. PolyEval requires every coefficient to be pinned by a
// constraint elsewhere, because the prover reads `z` before choosing a witness
// (see PolyEval above). For these fields the pin is the gated deposit binding
// in TreeUpdateBatch step 6,
//
//     active_dep[k] · (cv_dep[k] − (leaf_public_in[k]·V^leaf_asset[k] + rcv[k]·H)) === 0
//
// which pins leaf_public_in[k] and leaf_asset[k] against cv_dep[k] under the
// discrete-log hardness of the Jubjub subgroup: changing either operand
// requires a compensating cv_dep, itself two coefficients.
//
// At leaf_public_in[k] == 0 the equality degenerates: ValueTimesGen(0, gen) is
// the identity for every gen, so it reduces to cv_dep[k] == rcv[k]·H and
// leaf_asset[k] retains only Num2Bits(64). A range check bounds a coefficient
// without pinning it; four such leaves (fee notes of a flush at fbps = 0) give 4 × 64 = 256
// free bits against a 254-bit modulus, solvable as a small CVP instance.
// TreeUpdateBatch step 6a closes this by requiring leaf_asset[k] == 0 exactly
// when leaf_public_in[k] == 0.
//
// Moving these fields to the challenge preimage instead would be unsound:
// unlike the transact compressor's challenge-only words, they are signals of
// TreeUpdateBatch, and hashing a signal into z binds nothing, since the prover
// reads z first and can choose a witness that disagrees with the calldata it
// was hashed from.
//
// The two uint64 blocks (leaf_asset, leaf_public_in) are adjacent and the uint8
// block (is_deposit) follows them, so PubInputs.compress re-masks the sub-word
// members with two contiguous loops over the copied calldata.
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
