pragma circom 2.2.3;

// Test wrapper: PolyEval(26). The gadget is generic in N; see
// TransactCompressN for the production public-input layout.

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
