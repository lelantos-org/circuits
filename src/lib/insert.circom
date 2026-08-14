pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/poseidon.circom";
include "../../node_modules/circomlib/circuits/bitify.circom";
include "tags.circom";
include "common.circom";

// Quaternary (arity-4) incremental insert, mirroring the on-chain
// CommitmentTree._insert so the circuit can advance the tree off-chain.
//
// Per level, with digit ∈ {0..3}, cur the running node, f the frontier and
// z = zeros[level]:
//
//                      slot 0     slot 1     slot 2     slot 3
//   digit = 0          cur        z          z          z
//   digit = 1          f[0]       cur        z          z
//   digit = 2          f[0]       f[1]       cur        z
//   digit = 3          f[0]       f[1]       f[2]       cur
//
// Frontier writes cover slots 0..2: frontier_out[k] = (k == digit) ? cur : f[k].
// PathIndexSelectors range-checks idx_digit to {0..3}.

// One level: parent hash plus the updated frontier.
template QuaternaryInsertLevel() {
    signal input cur;
    signal input frontier_in[3];
    signal input zero;
    signal input idx_digit;

    signal output cur_next;
    signal output frontier_out[3];

    // s[k] = 1 iff idx_digit == k; also range-checks idx_digit.
    component sel = PathIndexSelectors();
    sel.path_index <== idx_digit;

    // c0 = s0·cur + (1-s0)·f[0]
    signal c0_cur;
    signal c0_sib;
    signal c0;
    c0_cur <== sel.s[0] * cur;
    c0_sib <== (1 - sel.s[0]) * frontier_in[0];
    c0 <== c0_cur + c0_sib;

    // c1 = s0·z + s1·cur + (s2+s3)·f[1]
    signal c1_z;
    signal c1_cur;
    signal c1_sib;
    signal c1;
    c1_z   <== sel.s[0] * zero;
    c1_cur <== sel.s[1] * cur;
    c1_sib <== (sel.s[2] + sel.s[3]) * frontier_in[1];
    c1 <== c1_z + c1_cur + c1_sib;

    // c2 = (s0+s1)·z + s2·cur + s3·f[2]
    signal c2_z;
    signal c2_cur;
    signal c2_sib;
    signal c2;
    c2_z   <== (sel.s[0] + sel.s[1]) * zero;
    c2_cur <== sel.s[2] * cur;
    c2_sib <== sel.s[3] * frontier_in[2];
    c2 <== c2_z + c2_cur + c2_sib;

    // c3 = (s0+s1+s2)·z + s3·cur
    signal c3_z;
    signal c3_cur;
    signal c3;
    c3_z   <== (sel.s[0] + sel.s[1] + sel.s[2]) * zero;
    c3_cur <== sel.s[3] * cur;
    c3 <== c3_z + c3_cur;

    component h = Poseidon(5);
    h.inputs[0] <== TAG_MERKLE();
    h.inputs[1] <== c0;
    h.inputs[2] <== c1;
    h.inputs[3] <== c2;
    h.inputs[4] <== c3;
    cur_next <== h.out;

    // frontier_out[k] = s[k]·cur + (1-s[k])·f[k] for slots 0..2.
    //
    // s[k]·cur is reused from c0_cur / c1_cur / c2_cur, and (1-s[0])·f[0] from
    // c0_sib, so slot 0 is a pure linear combination. Slots 1..2 need their own
    // sibling products: the child muxes use (s2+s3)·f[1] and s3·f[2], whereas the
    // frontier needs (1-s1)·f[1] and (1-s2)·f[2].
    signal w_sib1;
    signal w_sib2;
    w_sib1 <== (1 - sel.s[1]) * frontier_in[1];
    w_sib2 <== (1 - sel.s[2]) * frontier_in[2];

    frontier_out[0] <== c0_cur + c0_sib;
    frontier_out[1] <== c1_cur + w_sib1;
    frontier_out[2] <== c2_cur + w_sib2;
}

// Insert one leaf, returning the new root and frontier.
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
