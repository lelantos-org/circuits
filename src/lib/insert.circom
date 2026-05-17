pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/poseidon.circom";
include "../../node_modules/circomlib/circuits/bitify.circom";
include "tags.circom";
include "common.circom";

// Quaternary (arity-4) incremental insert. Mirrors on-chain
// CommitmentTree._insert so the relayer can prove tree advancement off-chain.
//
// Per-level slot-fill given digit ∈ {0..3} (cur = running node, f = frontier,
// z = zeros[level]):
//                      slot 0     slot 1     slot 2     slot 3
//   c0                 cur        f[0]       f[0]       f[0]
//   c1                 z          cur        f[1]       f[1]
//   c2                 z          z          cur        f[2]
//   c3                 z          z          z          cur
//
// Frontier writes (slots 0..2): frontier_out[k] = (k == digit) ? cur : f[k].
// idx_digit range-checked to {0..3} via PathIndexSelectors.

// One level: parent hash + updated frontier.
template QuaternaryInsertLevel() {
    signal input cur;
    signal input frontier_in[3];
    signal input zero;
    signal input idx_digit;

    signal output cur_next;
    signal output frontier_out[3];

    // s[k] = 1 iff idx_digit == k (also range-checks idx_digit).
    component sel = PathIndexSelectors();
    sel.path_index <== idx_digit;
    signal s0; signal s1; signal s2; signal s3;
    s0 <== sel.s[0];
    s1 <== sel.s[1];
    s2 <== sel.s[2];
    s3 <== sel.s[3];

    // c0 = s0·cur + (1-s0)·f[0]
    signal c0_cur;
    signal c0_sib;
    c0_cur <== s0 * cur;
    c0_sib <== (1 - s0) * frontier_in[0];
    signal c0;
    c0 <== c0_cur + c0_sib;

    // c1 = s0·z + s1·cur + (s2+s3)·f[1]
    signal c1_z;
    signal c1_cur;
    signal c1_sib;
    c1_z   <== s0 * zero;
    c1_cur <== s1 * cur;
    c1_sib <== (s2 + s3) * frontier_in[1];
    signal c1;
    c1 <== c1_z + c1_cur + c1_sib;

    // c2 = (s0+s1)·z + s2·cur + s3·f[2]
    signal c2_z;
    signal c2_cur;
    signal c2_sib;
    c2_z   <== (s0 + s1) * zero;
    c2_cur <== s2 * cur;
    c2_sib <== s3 * frontier_in[2];
    signal c2;
    c2 <== c2_z + c2_cur + c2_sib;

    // c3 = (s0+s1+s2)·z + s3·cur
    signal c3_z;
    signal c3_cur;
    c3_z   <== (s0 + s1 + s2) * zero;
    c3_cur <== s3 * cur;
    signal c3;
    c3 <== c3_z + c3_cur;

    component h = Poseidon(5);
    h.inputs[0] <== TAG_MERKLE();
    h.inputs[1] <== c0;
    h.inputs[2] <== c1;
    h.inputs[3] <== c2;
    h.inputs[4] <== c3;
    cur_next <== h.out;

    // Frontier writes (slots 0..2): out[k] = s[k]·cur + (1-s[k])·f[k].
    signal sk[3];
    sk[0] <== s0;
    sk[1] <== s1;
    sk[2] <== s2;
    signal w_cur[3];
    signal w_sib[3];
    for (var k = 0; k < 3; k++) {
        w_cur[k] <== sk[k] * cur;
        w_sib[k] <== (1 - sk[k]) * frontier_in[k];
        frontier_out[k] <== w_cur[k] + w_sib[k];
    }
}

template QuaternaryInsert(DEPTH) {
    signal input leaf;
    signal input idx_digit[DEPTH];
    signal input frontier_in[DEPTH][3];

    signal output root;
    signal output frontier_out[DEPTH][3];

    component zh = EmptySubtreeHashes(DEPTH);

    component lvl[DEPTH];
    signal cur[DEPTH + 1];
    cur[0] <== leaf;

    for (var i = 0; i < DEPTH; i++) {
        lvl[i] = QuaternaryInsertLevel();
        lvl[i].cur <== cur[i];
        lvl[i].zero <== zh.zeros[i];
        lvl[i].idx_digit <== idx_digit[i];
        for (var k = 0; k < 3; k++) {
            lvl[i].frontier_in[k] <== frontier_in[i][k];
        }
        cur[i + 1] <== lvl[i].cur_next;
        for (var k = 0; k < 3; k++) {
            frontier_out[i][k] <== lvl[i].frontier_out[k];
        }
    }

    root <== cur[DEPTH];
}
