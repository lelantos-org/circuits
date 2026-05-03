pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/bitify.circom";
include "../../node_modules/circomlib/circuits/escalarmulany.circom";
include "../../node_modules/circomlib/circuits/escalarmulfix.circom";
include "../../node_modules/circomlib/circuits/poseidon.circom";
include "tags.circom";

// FMD2 (lelantos.fmd.v2 / Poseidon scheme) bit-derivation, in-circuit.
//
// Mirrors `shared_bit` in backend/crates/fmd-crypto/src/clue.rs and
// sdk/src/fmd.ts, byte-identical:
//
//   R    = r · G_8                          (Baby-Jubjub fixed base, circomlib G8)
//   S_i  = r · fk_i                          for i ∈ [γ]
//   bit_i = lsb1(Poseidon([TAG_FMD_BIT, R.x, R.y, i, S_i.x, S_i.y]))
//
// Sender flips: clue_bits[i] === 1 - bit_i. Receiver tests:
//   bit_i ⊕ c_bits[i] === 1
// Honest sender ⇒ all γ checks pass. Constraining `clue_bits[i] === 1 - bit_i`
// here forces the sender to derive bits honestly: a malicious sender cannot
// set `clue_bits = all-ones` without also producing a valid `r, fk` whose
// Poseidon outputs all have LSB=0.
//
// Cost (γ=5):
//   1× EscalarMulFix(254)         R = r·G_8         ~3 k
//   γ× EscalarMulAny(254)         S_i = r·fk_i      ~γ × 4 k
//   γ× Poseidon(6)                bit_i             ~γ × 200
//   γ× Num2Bits(254)              LSB extract       ~γ × 254
// γ=5 total ≈ 25 k. γ=14 total ≈ 65 k.
//
// `r` is the FMD blinding scalar (private witness). `fk[i]` is the
// recipient flag-key point (private witness). `clue_bits` is a public
// witness (PolyEval-bound); 14 bits of which the first GAMMA are
// constrained — bits ≥ GAMMA are unconstrained here but the contract
// enforces upper-2-bits zero via `CLUE_BITS_MASK = 0x3FFF`.
//
// `R_x, R_y` are exposed as outputs so the caller can pipe them into
// PolyEval (the contract reads them from `aux.clueRx, aux.clueRy` and
// re-feeds them as PIs).
template ClueCheck(GAMMA) {
    signal input r;                  // private, Fr (≤ 254 bits)
    signal input fk[GAMMA][2];       // private, recipient flag-key points
    signal input clue_bits;          // public (via PolyEval), packed γ bits LSB-first
    signal output Rx;                // public output, R = r·G_8
    signal output Ry;

    // 1. Decompose r into bits once; reused by R = r·G8 and γ × S_i = r·fk_i.
    component rbits = Num2Bits(254);
    rbits.in <== r;

    // 2. R = r · G_8 (circomlib base point, see fmd-crypto/clue.rs:79-89).
    var G8[2];
    G8[0] = 5299619240641551281634865583518297030282874472190772894086521144482721001553;
    G8[1] = 16950150798460657717958625567821834550301663161624707787222815936182638968203;

    component rmul = EscalarMulFix(254, G8);
    for (var k = 0; k < 254; k++) {
        rmul.e[k] <== rbits.out[k];
    }
    Rx <== rmul.out[0];
    Ry <== rmul.out[1];

    // 3. clue_bits → γ bits. Higher bits unconstrained (contract masks).
    component cbits = Num2Bits(GAMMA);
    cbits.in <== clue_bits;

    // 4. Per-component shared secret + Poseidon bit + constraint.
    component s[GAMMA];
    component h[GAMMA];
    component lsb[GAMMA];

    for (var i = 0; i < GAMMA; i++) {
        s[i] = EscalarMulAny(254);
        for (var k = 0; k < 254; k++) {
            s[i].e[k] <== rbits.out[k];
        }
        s[i].p[0] <== fk[i][0];
        s[i].p[1] <== fk[i][1];

        // bit_i = lsb1(Poseidon([TAG_FMD_BIT, R.x, R.y, i, S_i.x, S_i.y]))
        h[i] = Poseidon(6);
        h[i].inputs[0] <== TAG_FMD_BIT();
        h[i].inputs[1] <== Rx;
        h[i].inputs[2] <== Ry;
        h[i].inputs[3] <== i;
        h[i].inputs[4] <== s[i].out[0];
        h[i].inputs[5] <== s[i].out[1];

        lsb[i] = Num2Bits(254);
        lsb[i].in <== h[i].out;

        // Sender format: c_bits[i] === 1 - lsb1(Poseidon(...))
        cbits.out[i] === 1 - lsb[i].out[0];
    }
}
