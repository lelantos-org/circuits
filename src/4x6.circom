pragma circom 2.2.3;

include "lib/transact.circom";

// 4-input × 6-output transact circuit. Logic is in Transact (lib/transact.circom).
//
// Six outputs rather than four so that change lands on the withdrawal
// denomination ladder in one spend. A withdrawal's publicOut must be a
// denomination to blend with other users'; change is decomposed greedily onto
// the ladder, and four slots hold at most three ladder pieces plus a dust note,
// so a remainder needing five pieces (4900 = 2000+2000+500+200+200) leaves 400
// off-ladder and requires a follow-up transfer to clear. Five change slots
// cover the great majority of decompositions outright.
//
// Inputs stay at four. An input slot carries a DEPTH-level Merkle path and its
// key derivation and nullifier — roughly 16.8k constraints against an output
// slot's 4.9k — so widening that side costs about 3.4x per slot for reach that
// is not the bottleneck.
//
// DEPTH = 11 matches the on-chain CommitmentTree: 4^11 = 4,194,304 leaves.
// Eleven rather than ten because an unused output slot is a real value-0 note
// with a real Poseidon insertion, not a sentinel: every spend consumes N_OUT
// leaves whether it fills them or not, so six outputs cut pool lifetime from
// 262,144 spends to 174,762. One extra level restores it fourfold for roughly
// 870 constraints per input, which is the cheapest capacity available and only
// free while a ceremony is already being paid for.
//
// PolyEval coefficient slots, which must match the PubInputs.sol :: compress
// overload for this shape:
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
// Total = 9 + 3·N_IN + 8·N_OUT = 69.
//
// The 40-word calldata prefix of the 4x4 layout becomes 50 words here
// (1 + 4 + 6 + 3 + 8 + 12 + 4 + 12), and the uint64 and address words that
// PubInputs.compress re-masks move with it. Those offsets are hardcoded
// assembly in the contract; derive them from this table rather than adapting
// the 4x4 literals by hand.
//
// Budget: this shape does not fit the 2^16 FFT domain. It is budgeted against
// 2^17, so setup fetches ptau_17. The tighter of the two circuits is
// tree_update_batch(11, 8), not this one — measure that first.
//
// Not established for this shape:
//   - a PubInputs.sol compress overload and a deployed verifier.
//   - a phase-2 ceremony beyond the single-contributor prototype.
//
// Consumer-side checks indexed by input or output must range over the whole
// shape: pairwise nullifier distinctness over all six pairs, and the out_cm and
// out_cv_dep cross-bindings to tree_update_batch over all six outputs.
component main {
    public [ z ]
} = Transact(11, 4, 6);
