pragma circom 2.2.3;

include "lib/transact.circom";

// Transact with 4 shielded inputs and 6 shielded outputs. Logic is in Transact
// (lib/transact.circom).
//
// DEPTH = 11 matches the on-chain CommitmentTree (4^11 = 4,194,304 leaves). An
// unused output slot is a value-0 note that is still inserted, so every spend
// consumes N_OUT leaves.
//
// Challenge preimage that PubInputs.sol :: compress hashes into z; must match
// that overload word for word:
//     [ 0]      merkle_root                  coefficient
//     [ 1.. 4]  nullifier[0..3]              coefficient
//     [ 5..10]  out_cm[0..5]                 coefficient
//     [11]      public_asset_id              coefficient
//     [12]      public_out                   coefficient
//     [13]      digest                       public signal (prover-supplied)
//     [14]      recipient_address            challenge only
//     [15]      chain_id                     challenge only
//     [16]      payer_address                challenge only
//     [17]      relayer_address              challenge only
//     [18]      intent_hash                  challenge only
//     [19..36]  (clue_Rx, clue_Ry, clue_bits) per output   challenge only
//     [37]      out_aux_digest               challenge only (contract recomputes)
// Total = 10 + N_IN + 4*N_OUT = 38 words hashed.
//
// PolyEval evaluates the 13 "coefficient" words [0..12] (3 + N_IN + N_OUT) in
// that order. digest is their Poseidon(5) fold (CoeffDigest in
// lib/poly_eval.circom) and a public output: the contract hashes the calldata
// value into z and passes it to the verifier without recomputing it. The
// verifier takes _pubSignals = [y, digest, z].
//
// The 24 "challenge only" words are not signals of this circuit; hashing them
// into z binds them to the proof. See src/README.md § 2a.
//
// The struct's calldata prefix is 19 words (1 + 4 + 6 + 2 + 1 + 5).
// PubInputs.compress re-masks the uint64 and address words at offsets hardcoded
// in assembly; derive them from this table.
//
// Budget: 2^15 FFT domain at `--O2`; setup uses ptau_16.
//
// The phase-2 setup for this shape has a single contributor and is not
// production-safe.
//
// Consumer-side checks must cover the whole shape: nullifier distinctness over
// all six pairs, and the out_cm cross-binding to tree_update_batch over all six
// outputs.
component main {
    public [ z ]
} = Transact(11, 4, 6);
