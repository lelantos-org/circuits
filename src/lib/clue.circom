pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/bitify.circom";
include "../../node_modules/circomlib/circuits/escalarmulany.circom";
include "../../node_modules/circomlib/circuits/escalarmulfix.circom";
include "../../node_modules/circomlib/circuits/poseidon.circom";
include "hash_to_bit.circom";
include "tags.circom";

// FMD2 (lelantos.fmd.v2) in-circuit bit derivation. Mirrors `shared_bit`
// in fmd-crypto/src/clue.rs and sdk/src/fmd.ts:
//
//   R     = r · G_8                                 (circomlib G8)
//   S_i   = r · fk_i                                for i ∈ [γ]
//   bit_i = legendre_bit(Poseidon(TAG_FMD_BIT, R.x, R.y, i, S_i.x, S_i.y))
//
// Sender constraint: clue_bits[i] === 1 - bit_i. Forces honest derivation —
// flipping a bit requires a valid (r, fk) whose Poseidon output flips
// residuosity. clue_bits is PolyEval-bound; upper bits ≥ GAMMA masked by
// the contract (CLUE_BITS_MASK = 0x3FFF). Rx/Ry exposed for PolyEval binding.
//
// Cost (γ=5) ≈ 24k. γ=14 ≈ 62k.
template ClueCheck(GAMMA) {
    signal input r;                  // private, Fr (≤ 254 bits)
    signal input fk[GAMMA][2];       // private, recipient flag-key points
    signal input clue_bits;          // public (via PolyEval), packed γ bits LSB-first
    signal input legendre_bit[GAMMA];// private, prover-supplied bit per γ
    signal input legendre_y[GAMMA];  // private, prover-supplied sqrt witness
    signal output Rx;                // public output, R = r·G_8
    signal output Ry;

    // 1. Decompose r once; reused by R = r·G8 and γ × S_i = r·fk_i.
    //    _strict rejects r ≥ p to prevent top-bit field aliasing.
    component rbits = Num2Bits_strict();
    rbits.in <== r;

    // 2. R = r · G_8 (circomlib base point).
    var G8[2];
    G8[0] = 5299619240641551281634865583518297030282874472190772894086521144482721001553;
    G8[1] = 16950150798460657717958625567821834550301663161624707787222815936182638968203;

    component rmul = EscalarMulFix(254, G8);
    for (var k = 0; k < 254; k++) {
        rmul.e[k] <== rbits.out[k];
    }
    Rx <== rmul.out[0];
    Ry <== rmul.out[1];

    // 3. clue_bits → γ bits (higher bits masked by contract).
    component cbits = Num2Bits(GAMMA);
    cbits.in <== clue_bits;

    // 4. Per-slot shared secret + Poseidon hash + Legendre bit.
    component s[GAMMA];
    component h[GAMMA];
    component hb[GAMMA];

    for (var i = 0; i < GAMMA; i++) {
        s[i] = EscalarMulAny(254);
        for (var k = 0; k < 254; k++) {
            s[i].e[k] <== rbits.out[k];
        }
        s[i].p[0] <== fk[i][0];
        s[i].p[1] <== fk[i][1];

        h[i] = Poseidon(6);
        h[i].inputs[0] <== TAG_FMD_BIT();
        h[i].inputs[1] <== Rx;
        h[i].inputs[2] <== Ry;
        h[i].inputs[3] <== i;
        h[i].inputs[4] <== s[i].out[0];
        h[i].inputs[5] <== s[i].out[1];

        hb[i] = HashToBit();
        hb[i].hash <== h[i].out;
        hb[i].bit <== legendre_bit[i];
        hb[i].y <== legendre_y[i];

        cbits.out[i] === 1 - legendre_bit[i];
    }
}
