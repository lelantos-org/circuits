pragma circom 2.2.3;

// DELIBERATELY BROKEN. Negative control for the sweep in
// `test/lib/underconstrained.ts`; not part of any circuit under `src/`.
//
// `out` is ASSIGNED with `<--` and never constrained. The witness calculator
// still computes `in * in` and every input-level test passes, because the
// generator is doing exactly what the template says. The R1CS contains no
// constraint on `out` at all, so a prover picks it freely — the canonical
// `<--` where `<==` was meant.
template LeakMissingOutputConstraint() {
    signal input in;
    signal output out;

    out <-- in * in;
}

component main { public [ in ] } = LeakMissingOutputConstraint();
