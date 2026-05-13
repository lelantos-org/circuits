pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/poseidon.circom";
include "../../node_modules/circomlib/circuits/bitify.circom";
include "tags.circom";
include "common.circom";

// Quaternary (arity-4) Merkle tree. Tree capacity = 4^DEPTH leaves; per-level
// hash = Poseidon(5) over (TAG_MERKLE, child[0..3]).
//
// Path encoding: per level the prover supplies the current node's position
// `path_index` ∈ {0,1,2,3} and three sibling values `siblings[0..2]` filling
// the remaining slots in increasing-slot order.
//
// e.g. path_index = 1 ⇒ children = (siblings[0], cur, siblings[1], siblings[2]).

// One Merkle level: hash 4 children where the position of `cur` is selected by
// `path_index` (range-checked to {0..3} via PathIndexSelectors).
//
// Slot-fill table (siblings consumed in increasing-slot order):
//                      slot 0     slot 1     slot 2     slot 3
//   path_index=0       cur        sib[0]     sib[1]     sib[2]
//   path_index=1       sib[0]     cur        sib[1]     sib[2]
//   path_index=2       sib[0]     sib[1]     cur        sib[2]
//   path_index=3       sib[0]     sib[1]     sib[2]     cur
//
// Slot 1 receives sib[0] when path_index=0 and sib[1] when path_index ∈ {2,3}
// (sib[0] already consumed at slot 0). The c1 expression therefore reads
// `s0·sib[0] + (s2+s3)·sib[1]`, not `s0·sib[0] + s2·sib[1]`.
template MerkleLevel4() {
    signal input cur;
    signal input siblings[3];
    signal input path_index;
    signal output out;

    // Range-check path_index ∈ {0..3} and produce one-hot selectors s[k].
    // Shared with QuaternaryInsert via PathIndexSelectors (lib/common.circom).
    component sel = PathIndexSelectors();
    sel.path_index <== path_index;
    signal s0;
    signal s1;
    signal s2;
    signal s3;
    s0 <== sel.s[0];
    s1 <== sel.s[1];
    s2 <== sel.s[2];
    s3 <== sel.s[3];

    // Build 4 children per the slot-fill table above. Each c_k is a sum of
    // products gated by selectors that are mutually exclusive and sum to 1.
    signal c0;
    signal c1;
    signal c2;
    signal c3;

    // slot 0: cur when p=0, else siblings[0] (rows p=1,2,3 all start with sib[0]).
    //   c0 = s0·cur + (1-s0)·sib[0]
    signal c0_cur;
    signal c0_sib;
    c0_cur <== s0 * cur;
    c0_sib <== (1 - s0) * siblings[0];
    c0 <== c0_cur + c0_sib;

    // slot 1: cur when p=1; sib[0] when p=0 (sib[0] not yet consumed);
    // sib[1] when p∈{2,3} (sib[0] already consumed by slot 0).
    //   c1 = s1·cur + s0·sib[0] + (s2+s3)·sib[1]
    signal c1_cur;
    signal c1_sib0;
    signal c1_sib1;
    c1_cur  <== s1 * cur;
    c1_sib0 <== s0 * siblings[0];
    c1_sib1 <== (s2 + s3) * siblings[1];
    c1 <== c1_cur + c1_sib0 + c1_sib1;

    // slot 2: cur when p=2; sib[1] when p∈{0,1} (sib[0],sib[1] are
    // sequentially consumed at slots 0,1); sib[2] when p=3.
    //   c2 = s2·cur + (s0+s1)·sib[1] + s3·sib[2]
    signal c2_cur;
    signal c2_sib1;
    signal c2_sib2;
    c2_cur  <== s2 * cur;
    c2_sib1 <== (s0 + s1) * siblings[1];
    c2_sib2 <== s3 * siblings[2];
    c2 <== c2_cur + c2_sib1 + c2_sib2;

    // slot 3: cur when p=3, else siblings[2] (rows p=0,1,2 all end with sib[2]).
    //   c3 = s3·cur + (1-s3)·sib[2]
    signal c3_cur;
    signal c3_sib;
    c3_cur <== s3 * cur;
    c3_sib <== (1 - s3) * siblings[2];
    c3 <== c3_cur + c3_sib;

    // Domain separation: TAG_MERKLE prefix distinguishes internal-node hashes
    // from NoteCommitment outputs (also Poseidon-based, different arity/tag).
    // Without the tag, an internal-node value could collide with a leaf
    // commitment.
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
// When is_dummy == 1 the inclusion check is skipped.
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
