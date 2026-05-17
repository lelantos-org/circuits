pragma circom 2.2.3;

// Test wrapper: PolyEval(26) matching Transact(_, _, 2, _) (PI_BASE=20 +
// 3·N_OUT=6). NB: TransactCompress now uses PI_BASE=24; update if extending.

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
