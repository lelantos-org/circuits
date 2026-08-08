pragma circom 2.2.3;

// REFERENCE ONLY — deliberately outside `src/lib/` and outside the `just lint`
// path. Nothing includes this file; the FMD bit derivation it describes runs
// off-circuit in the SDK (`sdk/src/crypto/sqrt.ts`), and the clue fields reach
// the transact circuit constrained only by PolyEval.
//
// It lives here rather than in `src/lib/` because its `inv <-- 1 / hash` hint is
// the only `<--` in the tree. Keeping it out of the lint path lets `just lint`
// run without the CS0005 / CS0015 / CS0017 waivers, so those passes stay live on
// the circuits that actually get compiled. Do not move it back into `src/lib/`
// without restoring those waivers and re-reviewing the sites they hide.
//
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
