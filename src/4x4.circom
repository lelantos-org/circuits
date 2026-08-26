pragma circom 2.2.3;

include "lib/transact.circom";

// 4-input × 4-output transact circuit. Logic is in Transact (lib/transact.circom).
// Not the deployed shape (see 3x3.circom); it serves consumers needing four
// shielded slots per side.
//
// DEPTH = 10 matches the on-chain CommitmentTree: 4^10 = 1,048,576 leaves.
//
// PolyEval coefficient slots, which must match a PubInputs.sol :: compress
// overload for this shape. No such overload exists, so this shape is not
// verifiable on-chain:
//     [ 0]      merkle_root
//     [ 1.. 4]  nullifier[0..3]
//     [ 5.. 8]  out_cm[0..3]
//     [ 9]      public_asset_id
//     [10]      public_in
//     [11]      public_out
//     [12..19]  in_cv[0..3][0..1]
//     [20..27]  out_cv[0..3][0..1]
//     [28]      recipient_address
//     [29]      chain_id
//     [30]      payer_address
//     [31]      relayer_address
//     [32..39]  out_cv_dep[0..3][0..1]
//     [40..51]  (clue_Rx, clue_Ry, clue_bits) per output
//     [52]      out_aux_digest           (contract recomputes; never read from calldata)
// Total = 9 + 3·N_IN + 8·N_OUT = 53.
//
// This shape does not fit the 2^16 FFT domain the other two share: its count is
// budgeted in budget.json against a 2^17 domain, so `setup-4x4` fetches its own
// ptau and proving costs roughly twice a 3x3 proof.
//
// Not established for this shape:
//   - a PubInputs.sol compress overload and a deployed verifier.
//   - golden vectors (scripts/vectors/transact.ts) or a Lean layout dump.
//   - a phase-2 ceremony beyond the single-contributor prototype.
//
// Consumer-side checks indexed by input or output must range over the whole
// shape: pairwise nullifier distinctness over all six pairs, and the out_cm and
// out_cv_dep cross-bindings to tree_update_batch over all four outputs.
component main {
    public [ z ]
} = Transact(10, 4, 4);
