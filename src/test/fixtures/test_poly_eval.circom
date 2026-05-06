pragma circom 2.2.3;

// Test wrapper: expose PolyEval(N=20 + 3·N_OUT) directly so we can
// validate Horner evaluation, coefficient ordering, and z-boundary
// behaviour without the full Transact circuit.
//
// N matches `Transact(_, _, 2, _)` instantiation (PI_BASE=20, PI_PER_OUT=3,
// N_OUT=2 ⇒ 26 coefficients).

include "../../lib/poly_eval.circom";

template TestPolyEval26() {
    signal input coeffs[26];
    signal input z;
    signal output y;

    component pe = PolyEval(26);
    for (var i = 0; i < 26; i++) {
        pe.coeffs[i] <== coeffs[i];
    }
    pe.z <== z;
    y <== pe.y;
}

component main = TestPolyEval26();
