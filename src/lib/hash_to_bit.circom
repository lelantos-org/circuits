pragma circom 2.2.3;

// Legendre-symbol-based bit extraction from a Poseidon hash output.
//
// Replaces `Num2Bits(254) → out[0]` (~254 constraints) with a 4-constraint
// gadget that derives a uniform bit by checking quadratic residuosity of
// the hash in the BN254 scalar field 𝔽_r.
//
// Math:
//   |QR| = |QNR| = (r-1)/2 in 𝔽_r*. So for hash ←$ 𝔽_r the symbol is a
//   uniform bit; on Poseidon output (modeled as RO) this is the same as
//   "uniform bit on uniform field element".
//
// Convention:
//   bit = 1  ⟺  hash is a quadratic residue (∃ y with y² = hash)
//   bit = 0  ⟺  hash is a non-residue        (∃ y with y² · Z = hash)
//
// Z is a public QNR constant in 𝔽_r. Verified offline:
//     Z^((r-1)/2) ≡ -1 (mod r)  for Z=5.
// Must stay in sync with `FMD_LEGENDRE_QNR` in sdk/src/crypto/tags.ts.
//
// Witness inputs (`bit`, `y`) are computed off-circuit by
// `fmdLegendreWitness` in sdk/src/crypto/sqrt.ts and supplied via the
// outer circuit's input.json.
//
// Soundness: for any nonzero hash, exactly one of {hash, hash·Z⁻¹} is a
// QR (since Z is QNR), so a satisfying (bit, y) exists for exactly one
// value of bit. A malicious prover cannot pick the other branch because
// the corresponding y would have to be a square root of a non-residue,
// which does not exist in 𝔽_r.
//
// Cost: 4 multiplicative constraints (inv-check, bit-bool, y², final eq).
// Plus 1 linear assignment (m), free in R1CS.
template HashToBit() {
    signal input hash;
    signal input bit;   // prover-supplied: 1 if hash is QR, 0 otherwise.
    signal input y;     // prover-supplied: sqrt(hash) or sqrt(hash · Z^-1).

    var Z = 5;

    // 1. Reject hash == 0 (probability 1/r, negligible).
    signal inv;
    inv <-- 1 / hash;
    inv * hash === 1;

    // 2. bit ∈ {0,1}.
    bit * (1 - bit) === 0;

    // 3. Multiplier m = 1 when bit=1 (QR branch), Z when bit=0 (QNR branch).
    //    m = Z + bit·(1-Z). Linear in bit ⇒ free.
    signal m;
    m <== Z + bit * (1 - Z);

    // 4. Verify hash = y² · m.
    signal y_sq;
    y_sq <== y * y;
    hash === y_sq * m;
}
