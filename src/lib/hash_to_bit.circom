pragma circom 2.2.3;

// Legendre-symbol bit extraction. 4 constraints vs Num2Bits(254)'s ~254.
//
// Convention:
//   bit = 1  ⟺  hash = y²        (quadratic residue)
//   bit = 0  ⟺  hash = y² · Z    (non-residue; Z = 5 is a fixed QNR in 𝔽_r)
//
// Z must match FMD_LEGENDRE_QNR in sdk/src/crypto/tags.ts. Witnesses (bit, y)
// computed by fmdLegendreWitness in sdk/src/crypto/sqrt.ts.
//
// Soundness: exactly one of {hash, hash·Z⁻¹} is a QR for nonzero hash, so a
// valid (bit, y) exists for only one bit value. Cost: 4 mul constraints.
template HashToBit() {
    signal input hash;
    signal input bit;   // 1 if hash is QR, 0 otherwise.
    signal input y;     // sqrt(hash) or sqrt(hash · Z⁻¹).

    var Z = 5;

    // Reject hash == 0.
    signal inv;
    inv <-- 1 / hash;
    inv * hash === 1;

    bit * (1 - bit) === 0;

    // m = 1 if bit=1 else Z. Linear in bit.
    signal m;
    m <== Z + bit * (1 - Z);

    signal y_sq;
    y_sq <== y * y;
    hash === y_sq * m;
}
