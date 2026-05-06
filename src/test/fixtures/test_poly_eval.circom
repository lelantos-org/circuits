pragma circom 2.2.3;

// Test wrapper: expose PolyEval(N=22 + 3·N_OUT) directly so we can
// validate Horner evaluation, coefficient ordering, and z-boundary
// behaviour without the full Transact circuit.
//
// N matches `Transact(_, _, 2, _)` instantiation (PI_BASE=22, PI_PER_OUT=3,
// N_OUT=2 ⇒ 28 coefficients).

include "../../lib/poly_eval.circom";

template TestPolyEval28() {
    signal input coeffs[28];
    signal input z;
    signal output y;

    component pe = PolyEval(28);
    for (var i = 0; i < 28; i++) {
        pe.coeffs[i] <== coeffs[i];
    }
    pe.z <== z;
    y <== pe.y;
}

component main = TestPolyEval28();
