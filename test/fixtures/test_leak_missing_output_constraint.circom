pragma circom 2.2.3;

// Deliberately broken. Negative control for the sweep in
// `test/lib/underconstrained.ts`; not part of any circuit under `src/`.
//
// `out` is assigned with `<--` and never constrained. The witness calculator
// computes `in * in`, so input-level tests pass, but the R1CS has no constraint
// on `out` and a prover picks it freely.
template LeakMissingOutputConstraint() {
    signal input in;
    signal output out;

    out <-- in * in;
}

component main { public [ in ] } = LeakMissingOutputConstraint();
