pragma circom 2.2.3;

include "lib/transact.circom";

// Transact with 4 shielded inputs and 6 shielded outputs. Logic is in Transact
// (lib/transact.circom).
//
// DEPTH = 11 matches the on-chain CommitmentTree (4^11 = 4,194,304 leaves). An
// unused output slot is a value-0 note that is still inserted, so every spend
// consumes N_OUT leaves.
//
// Six output slots let a withdrawal's change land on the denomination ladder in
// one spend: publicOut must itself be a denomination, and five change slots
// cover most decompositions. Inputs are limited to four because an input slot
// (DEPTH-level Merkle path, key derivation, nullifier) costs about 16.8k
// constraints against 4.9k for an output slot.
//
// Challenge preimage that PubInputs.sol :: compress hashes into z; must match
// that overload word for word:
//     [ 0]      merkle_root                  coefficient
//     [ 1.. 4]  nullifier[0..3]              coefficient
//     [ 5..10]  out_cm[0..5]                 coefficient
//     [11]      public_asset_id              coefficient
//     [12]      public_in                    coefficient
//     [13]      public_out                   coefficient
//     [14..21]  in_cv[0..3][0..1]            coefficient
//     [22..33]  out_cv[0..5][0..1]           coefficient
//     [34..45]  out_cv_dep[0..5][0..1]       coefficient
//     [46]      recipient_address            challenge only
//     [47]      chain_id                     challenge only
//     [48]      payer_address                challenge only
//     [49]      relayer_address              challenge only
//     [50]      intent_hash                  challenge only
//     [51..68]  (clue_Rx, clue_Ry, clue_bits) per output   challenge only
//     [69]      out_aux_digest               challenge only (contract recomputes)
// Total = 10 + 3*N_IN + 8*N_OUT = 70 words hashed.
//
// PolyEval evaluates the 46 "coefficient" words [0..45], a leading run, in that
// order. Total = 4 + 3*N_IN + 5*N_OUT.
//
// The 24 "challenge only" words are not signals of this circuit and are
// unconstrained here; hashing them into z binds them to the proof.
// See src/README.md § 2a.
//
// The struct's calldata prefix is 51 words (1 + 4 + 6 + 3 + 8 + 12 + 12 + 5).
// PubInputs.compress re-masks the uint64 and address words at offsets hardcoded
// in assembly; derive them from this table.
//
// Budget: 2^17 FFT domain, so setup uses ptau_17. tree_update_batch(11, 8) is
// the tighter of the two circuits.
//
// NOTE: the phase-2 setup for this shape is a single-contributor prototype and
// is not production-safe.
//
// Consumer-side checks indexed by input or output must cover the whole shape:
// nullifier distinctness over all six pairs, and the out_cm and out_cv_dep
// cross-bindings to tree_update_batch over all six outputs.
component main {
    public [ z ]
} = Transact(11, 4, 6);
