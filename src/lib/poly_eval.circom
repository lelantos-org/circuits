pragma circom 2.2.3;

// Horner-form polynomial evaluation.
//
// Given coefficients c[0..N-1] and challenge z, computes
//   y = c[0] + c[1]·z + c[2]·z^2 + ... + c[N-1]·z^{N-1}
//
// Used by Transact to compress N would-be public inputs into a single
// (z, y) public pair. Verifier still binds every coeff because any change
// to c[k] alters y for almost all z (Schwartz–Zippel: collision prob ≤
// (N-1)/p over prime field p — negligible at BN254 scalar size).
//
// Coefficient ordering is load-bearing: it MUST match
// contracts/src/MASP.sol :: _flatten() byte-for-byte. Any reordering is
// a soundness change for the contract's binding of public state.
template PolyEval(N) {
    signal input coeffs[N];
    signal input z;
    signal output y;

    signal acc[N + 1];
    acc[0] <== 0;
    for (var i = N; i > 0; i--) {
        acc[N - i + 1] <== acc[N - i] * z + coeffs[i - 1];
    }
    y <== acc[N];
}
