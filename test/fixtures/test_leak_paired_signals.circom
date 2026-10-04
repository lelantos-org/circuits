pragma circom 2.2.3;

// Deliberately broken. Negative control for the group search in
// `test/lib/underconstrained.ts`; not part of any circuit under `src/`.
//
// The defect is invisible to a single-signal sweep: `a` is pinned while `b` is
// fixed, and `b` while `a` is. Moving the pair together,
//
//     a += t     b -= t     u += t·x     v -= t·x
//
// leaves `u + v` unchanged for every t, so the R1CS stays satisfied and the
// public output `out`, equal to `u`, takes an arbitrary value.
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

    // The pair's sum is bound to the input; neither element is bound alone.
    u + v === in * x;

    out <== u;
}

component main { public [ in, x ] } = LeakPairedSignals();
