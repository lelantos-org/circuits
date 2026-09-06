pragma circom 2.2.3;

include "lib/transact.circom";

// Transact at 4 shielded inputs x 6 shielded outputs. Logic is in Transact
// (lib/transact.circom).
//
// DEPTH = 11 matches the on-chain CommitmentTree: 4^11 = 4,194,304 leaves. An
// unused output slot is a real value-0 note with a real Poseidon insertion, so
// a spend consumes N_OUT leaves whether it fills them or not.
//
// Six output slots let a withdrawal's change land on the denomination ladder in
// one spend: the publicOut must itself be a denomination, and five change slots
// cover most decompositions. Inputs stay at four because an input slot carries a
// DEPTH-level Merkle path with its key derivation and nullifier, roughly 16.8k
// constraints against an output slot's 4.9k.
//
// PolyEval coefficient slots. Must match the PubInputs.sol :: compress overload
// for this shape:
//     [ 0]      merkle_root
//     [ 1.. 4]  nullifier[0..3]
//     [ 5..10]  out_cm[0..5]
//     [11]      public_asset_id
//     [12]      public_in
//     [13]      public_out
//     [14..21]  in_cv[0..3][0..1]
//     [22..33]  out_cv[0..5][0..1]
//     [34]      recipient_address
//     [35]      chain_id
//     [36]      payer_address
//     [37]      relayer_address
//     [38..49]  out_cv_dep[0..5][0..1]
//     [50..67]  (clue_Rx, clue_Ry, clue_bits) per output
//     [68]      out_aux_digest           (contract recomputes; never read from calldata)
// Total = 9 + 3*N_IN + 8*N_OUT = 69.
//
// The struct's calldata prefix is 50 words (1 + 4 + 6 + 3 + 8 + 12 + 4 + 12).
// PubInputs.compress re-masks the uint64 and address words at offsets hardcoded
// in assembly; derive them from this table.
//
// Budget: 2^17 FFT domain, so setup fetches ptau_17. tree_update_batch(11, 8) is
// the tighter of the two circuits.
//
// The phase-2 setup for this shape is a single-contributor prototype and is not
// production-safe.
//
// Consumer-side checks indexed by input or output must range over the whole
// shape: pairwise nullifier distinctness over all six pairs, and the out_cm and
// out_cv_dep cross-bindings to tree_update_batch over all six outputs.
component main {
    public [ z ]
} = Transact(11, 4, 6);
