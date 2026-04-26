pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/poseidon.circom";
include "../../node_modules/circomlib/circuits/bitify.circom";
include "tags.circom";

// Quaternary (arity-4) Merkle tree. Tradeoff vs binary:
//   - Halves depth at same capacity (4^d == 2^(2d)).
//   - Per level: Poseidon(5) (~867 constraints) vs Poseidon(2) (~517).
//   - Net win because hash count drops 2x while per-hash cost grows ~1.4x.
//   - Same ~46% on-chain Poseidon reduction for inserts.
//
// Path encoding: per level the prover supplies the current node's position
// `path_index` ∈ {0,1,2,3} and three sibling values `siblings[0..2]` filling
// the remaining slots in increasing-slot order.
//
// e.g. path_index = 1 means children become (siblings[0], cur, siblings[1], siblings[2]).

// One Merkle level: hash 4 children where the position of `cur` is selected by
// `path_index` (range-checked to 2 bits = {0..3}).
//
// Slot-fill table (· = consumes next sibling not yet placed):
//                      slot 0     slot 1     slot 2     slot 3
//   path_index=0       cur        sib[0]     sib[1]     sib[2]
//   path_index=1       sib[0]     cur        sib[1]     sib[2]
//   path_index=2       sib[0]     sib[1]     cur        sib[2]
//   path_index=3       sib[0]     sib[1]     sib[2]     cur
//
// Note for c1: when path_index ∈ {2,3} (i.e. s2+s3 == 1), cur sits later in
// the row so sib[1] — not sib[0] — occupies slot 1. Hence `(s2+s3)*sib[1]`
// rather than just `s2*sib[1]`.
template MerkleLevel4() {
    signal input cur;
    signal input siblings[3];
    signal input path_index;
    signal output out;

    // Decompose path_index into 2 bits — range-checks the index to {0..3}.
    component idx_bits = Num2Bits(2);
    idx_bits.in <== path_index;
    signal b0;
    signal b1;
    b0 <== idx_bits.out[0];
    b1 <== idx_bits.out[1];

    // Selectors: s[p] = 1 iff path_index == p. Computed from a single product.
    signal bb;
    bb <== b0 * b1;
    signal s0;
    signal s1;
    signal s2;
    signal s3;
    s0 <== 1 - b0 - b1 + bb;  // (1-b0)*(1-b1)
    s1 <== b0 - bb;            // b0*(1-b1)
    s2 <== b1 - bb;            // (1-b0)*b1
    s3 <== bb;                 // b0*b1

    // Build 4 children per the slot-fill table above.
    signal c0;
    signal c1;
    signal c2;
    signal c3;

    signal c0_cur;
    signal c0_sib;
    c0_cur <== s0 * cur;
    c0_sib <== (1 - s0) * siblings[0];
    c0 <== c0_cur + c0_sib;

    signal c1_cur;
    signal c1_sib0;
    signal c1_sib1;
    c1_cur  <== s1 * cur;
    c1_sib0 <== s0 * siblings[0];
    c1_sib1 <== (s2 + s3) * siblings[1];
    c1 <== c1_cur + c1_sib0 + c1_sib1;

    signal c2_cur;
    signal c2_sib1;
    signal c2_sib2;
    c2_cur  <== s2 * cur;
    c2_sib1 <== (s0 + s1) * siblings[1];
    c2_sib2 <== s3 * siblings[2];
    c2 <== c2_cur + c2_sib1 + c2_sib2;

    signal c3_cur;
    signal c3_sib;
    c3_cur <== s3 * cur;
    c3_sib <== (1 - s3) * siblings[2];
    c3 <== c3_cur + c3_sib;

    // TAG_MERKLE prefix gives explicit domain separation. NoteCommitment also
    // uses Poseidon (arity 4) on different inputs; without an explicit tag a
    // malicious prover could pick an internal-node value colliding with a
    // leaf commitment.
    component h = Poseidon(5);
    h.inputs[0] <== TAG_MERKLE();
    h.inputs[1] <== c0;
    h.inputs[2] <== c1;
    h.inputs[3] <== c2;
    h.inputs[4] <== c3;
    out <== h.out;
}

// Compute Merkle root from leaf + path. Caller checks against expected root.
template MerkleRoot(depth) {
    signal input leaf;
    signal input path_elements[depth][3];
    signal input path_indices[depth];
    signal output root;

    component levels[depth];
    signal cur[depth + 1];
    cur[0] <== leaf;

    for (var i = 0; i < depth; i++) {
        levels[i] = MerkleLevel4();
        levels[i].cur <== cur[i];
        levels[i].siblings[0] <== path_elements[i][0];
        levels[i].siblings[1] <== path_elements[i][1];
        levels[i].siblings[2] <== path_elements[i][2];
        levels[i].path_index <== path_indices[i];
        cur[i + 1] <== levels[i].out;
    }

    root <== cur[depth];
}

// Verify (leaf, path) ∈ tree(root) OR is_dummy == 1.
// Dummy notes skip Merkle inclusion entirely so deposit / pad-input txs work.
template MerkleProofOrDummy(depth) {
    signal input leaf;
    signal input path_elements[depth][3];
    signal input path_indices[depth];
    signal input root;
    signal input is_dummy;

    is_dummy * (is_dummy - 1) === 0;

    component mr = MerkleRoot(depth);
    mr.leaf <== leaf;
    for (var i = 0; i < depth; i++) {
        mr.path_elements[i][0] <== path_elements[i][0];
        mr.path_elements[i][1] <== path_elements[i][1];
        mr.path_elements[i][2] <== path_elements[i][2];
        mr.path_indices[i] <== path_indices[i];
    }

    // (1 - is_dummy) * (computed_root - root) == 0
    signal diff;
    diff <== mr.root - root;
    (1 - is_dummy) * diff === 0;
}
