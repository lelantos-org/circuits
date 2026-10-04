pragma circom 2.2.3;

include "spent.circom";
include "output.circom";
include "balance.circom";
include "poly_eval.circom";

// MASP pool: N_IN-input x N_OUT-output multi-asset transact circuit.
// Instantiated by 4x6.circom.
//
// Parameters:
//   DEPTH — Merkle depth; capacity 4^DEPTH leaves.
//   N_IN  — spent-note slots; unused slots are dummies.
//   N_OUT — output-note slots; unused slots are value-0 notes to self.
//
// A note commits to its (asset_id, value) by hash (NoteCommitment), and
// PerAssetValueBalance enforces conservation over asset ids as field elements.
// There is no value commitment and no curve arithmetic.
//
// Per-slot constraints live in SpentNote and OutputNote; this template wires
// them together.
//
// The verifier sees only the public signals (y, digest, z), in that order,
// with y = PolyEval(coeffs, z) and digest = CoeffDigest(coeffs). The coefficient
// layout is TransactCompressN's and must match PubInputs.sol.
//
// Enforced here: in_asset, out_asset, public_asset_id, in_value, out_value and
// public_out are all < 2^64, and public_asset_id == 0 whenever public_out == 0.
//
// Left to the contract: chain_id == block.chainid, recipient_address < 2^160,
// each nullifier[i] unspent, and each out_cm[j] inserted into the commitment
// tree.
//
// Not circuit signals: recipient_address, chain_id, payer_address,
// relayer_address, intent_hash, the per-output FMD clue fields and the
// encrypted-payload digest. The circuit constrains none of them, so they are
// not PolyEval coefficients (see TransactCompressN in poly_eval.circom). They
// bind to the proof through the challenge: PubInputs.sol hashes them into z, so
// altering any of them changes z and therefore y.
template Transact(DEPTH, N_IN, N_OUT) {
    // ===== PUBLIC (verifier-visible) =====
    signal input  z;        // Fiat-Shamir challenge.
    signal output y;        // PolyEval(coeffs, z).
    signal output digest;   // CoeffDigest(coeffs); commits the witness before z.

    // ===== LOGICAL PUBLIC INPUTS (private signals, bound via PolyEval) =====
    signal input merkle_root;
    signal input nullifier[N_IN];
    signal input out_cm[N_OUT];
    signal input public_asset_id;
    signal input public_out;

    // ===== PRIVATE: spent notes =====
    signal input in_asset[N_IN];
    signal input in_value[N_IN];
    signal input in_pk[N_IN];
    signal input in_rho[N_IN];
    signal input in_rcm[N_IN];
    signal input in_nsk[N_IN];
    signal input in_path_elements[N_IN][DEPTH][3];
    signal input in_path_indices[N_IN][DEPTH];
    signal input in_is_dummy[N_IN];

    // ===== PRIVATE: output notes =====
    signal input out_asset[N_OUT];
    signal input out_value[N_OUT];
    signal input out_pk[N_OUT];
    signal input out_rho[N_OUT];
    signal input out_rcm[N_OUT];

    // ----- Spent-note slots -----
    component spent[N_IN];
    component in_dz = DummyZeroValue(N_IN);

    for (var i = 0; i < N_IN; i++) {
        spent[i] = SpentNote(DEPTH);
        spent[i].asset_id <== in_asset[i];
        spent[i].value    <== in_value[i];
        spent[i].pk       <== in_pk[i];
        spent[i].rho      <== in_rho[i];
        spent[i].rcm      <== in_rcm[i];
        spent[i].nsk      <== in_nsk[i];
        spent[i].is_dummy <== in_is_dummy[i];
        for (var d = 0; d < DEPTH; d++) {
            spent[i].path_elements[d][0] <== in_path_elements[i][d][0];
            spent[i].path_elements[d][1] <== in_path_elements[i][d][1];
            spent[i].path_elements[d][2] <== in_path_elements[i][d][2];
            spent[i].path_indices[d]     <== in_path_indices[i][d];
        }
        spent[i].root      <== merkle_root;
        spent[i].nullifier <== nullifier[i];

        // is_dummy == 1 ⇒ value == 0.
        in_dz.dummy[i] <== in_is_dummy[i];
        in_dz.value[i] <== in_value[i];
    }

    // At least one input slot must be real.
    //
    // MerkleProofOrDummy skips the root comparison on a dummy slot, so if every
    // slot is a dummy, no spend constraint reads merkle_root. With one real slot
    // the root is the output of a Poseidon chain over a note the prover owns.
    //
    // This excludes no valid flow: shielding goes through the deposit escrow
    // and tree_update_batch, so an all-dummy transact has nothing to spend and
    // every output at value 0.
    //
    // DummyZeroValue booleanizes is_dummy, so the sum is in [0, N_IN] and a
    // single equality suffices.
    signal dummy_acc[N_IN + 1];
    dummy_acc[0] <== 0;
    for (var i = 0; i < N_IN; i++) {
        dummy_acc[i + 1] <== dummy_acc[i] + in_is_dummy[i];
    }
    component all_dummy = IsEqual();
    all_dummy.in[0] <== dummy_acc[N_IN];
    all_dummy.in[1] <== N_IN;
    all_dummy.out === 0;

    // ----- Output-note slots -----
    // out_rho is pinned to DeriveRho(nullifier[0], j), so no two committed output
    // notes share a rho.
    component out_rho_d[N_OUT];
    component out_note[N_OUT];

    for (var j = 0; j < N_OUT; j++) {
        out_rho_d[j] = DeriveRho();
        out_rho_d[j].nf0   <== nullifier[0];
        out_rho_d[j].index <== j;
        out_rho[j] === out_rho_d[j].rho;

        out_note[j] = OutputNote();
        out_note[j].asset_id <== out_asset[j];
        out_note[j].value    <== out_value[j];
        out_note[j].pk       <== out_pk[j];
        out_note[j].rho      <== out_rho[j];
        out_note[j].rcm      <== out_rcm[j];
        out_note[j].cm       <== out_cm[j];
    }

    // ----- Transparent bucket -----
    // Both words match a uint64 on chain, and public_out is a term of the
    // conservation sums.
    component rng_pub_asset = RangeCheck64();
    rng_pub_asset.v <== public_asset_id;

    component rng_pub_out = RangeCheck64();
    rng_pub_out.v <== public_out;

    // public_out == 0 ⇒ public_asset_id == 0: a transaction that withdraws
    // nothing names no asset. Without this a shielded transfer would have to
    // publish some asset id, and the natural choice is the one it moves.
    //
    // The converse needs no constraint. At public_asset_id == 0 the candidate
    // check for id 0 reads Σ in_value[asset == 0] == Σ out_value[asset == 0]
    // + public_out; outputs reject id 0 and a real input rejects it, so only
    // dummies remain on the left, at value 0, and public_out == 0 follows.
    component pub_out_z = IsZero();
    pub_out_z.in <== public_out;
    pub_out_z.out * public_asset_id === 0;

    // ----- Value conservation -----
    component vbal = PerAssetValueBalance(N_IN, N_OUT);
    for (var i = 0; i < N_IN; i++) {
        vbal.in_asset[i] <== in_asset[i];
        vbal.in_value[i] <== in_value[i];
    }
    for (var j = 0; j < N_OUT; j++) {
        vbal.out_asset[j] <== out_asset[j];
        vbal.out_value[j] <== out_value[j];
    }
    vbal.public_asset_id <== public_asset_id;
    vbal.public_out      <== public_out;

    // ----- Public-input compression → (y, digest, z) -----
    component pe = TransactCompressN(N_IN, N_OUT);
    pe.z <== z;
    pe.merkle_root <== merkle_root;
    for (var i = 0; i < N_IN; i++) {
        pe.nullifier[i] <== nullifier[i];
    }
    for (var j = 0; j < N_OUT; j++) {
        pe.out_cm[j] <== out_cm[j];
    }
    pe.public_asset_id <== public_asset_id;
    pe.public_out      <== public_out;
    y <== pe.y;
    digest <== pe.digest;
}
