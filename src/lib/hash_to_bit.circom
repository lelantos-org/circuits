pragma circom 2.2.3;

// Legendre-symbol bit extraction: 4 constraints instead of Num2Bits(254)'s ~254.
//   bit = 1  ⟺  hash = y²      (quadratic residue)
//   bit = 0  ⟺  hash = y²·Z    (Z = 5, a fixed non-residue in 𝔽_r)
// Z must match FMD_LEGENDRE_QNR in sdk/src/crypto/tags.ts.
//
// For nonzero hash exactly one of {hash, hash·Z⁻¹} is a residue, so only one
// value of bit admits a valid (bit, y).
template HashToBit() {
    signal input hash;
    signal input bit;   // 1 if hash is a quadratic residue, else 0.
    signal input y;     // sqrt(hash) or sqrt(hash · Z⁻¹).

    var Z = 5;

    // Reject hash == 0.
    signal inv;
    inv <-- 1 / hash;
    inv * hash === 1;

    bit * (1 - bit) === 0;

    // m = 1 if bit = 1 else Z, linear in bit.
    signal m;
    m <== Z + bit * (1 - Z);

    signal y_sq;
    y_sq <== y * y;
    hash === y_sq * m;
}
