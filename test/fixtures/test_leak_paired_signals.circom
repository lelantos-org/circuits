pragma circom 2.2.3;

// DELIBERATELY BROKEN. Negative control for the group search in
// `test/lib/underconstrained.ts`; not part of any circuit under `src/`.
//
// The bug is invisible to a single-signal sweep BY CONSTRUCTION, which is the
// point of the fixture. `a` is pinned as long as `b` holds still — `u === a * x`
// is linear in `a` — and `b` is pinned as long as `a` does. Only the pair moving
// TOGETHER escapes:
//
//     a += t     b -= t     u += t·x     v -= t·x
//
// leaves `u + v` untouched, so the only constraint tying the pair to the input
// still holds, for every t. The whole line satisfies the R1CS, and `out` rides
// along with `u` — so this is a public output taking any value it likes, the
// strongest form of the bug.
template LeakPairedSignals() {
    signal input in;
    signal input x;
    signal output out;

    signal a;
    signal b;

    a <-- in;
    b <-- 0;

    signal u <== a * x;
    signal v <== b * x;

    // The pair's SUM is bound to the input; neither element is bound alone.
    u + v === in * x;

    out <== u;
}

component main { public [ in, x ] } = LeakPairedSignals();
