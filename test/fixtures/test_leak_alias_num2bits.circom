pragma circom 2.2.3;

// DELIBERATELY BROKEN. Negative control for the aliasing check in
// `test/lib/bit_groups.ts`; not part of any circuit under `src/`.
//
// `Num2Bits(254)` does not determine its input on BN254: 2^254 > p, so the bits
// of `v` and the bits of `v + p` both satisfy the weighted sum. Any range check
// built on it is worthless. `src/` never exceeds 252.
include "../../node_modules/circomlib/circuits/bitify.circom";

template LeakAliasNum2Bits() {
    signal input in;
    signal output out;

    component n = Num2Bits(254);
    n.in <== in;
    out <== n.out[0];
}

component main { public [ in ] } = LeakAliasNum2Bits();
