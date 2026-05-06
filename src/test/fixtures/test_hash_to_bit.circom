pragma circom 2.2.3;

// Test wrapper: expose HashToBit gadget directly so we can stress its
// soundness + completeness without dragging in the full ClueCheck loop.

include "../../lib/hash_to_bit.circom";

template TestHashToBit() {
    signal input hash;
    signal input bit;
    signal input y;

    component h = HashToBit();
    h.hash <== hash;
    h.bit  <== bit;
    h.y    <== y;
}

component main = TestHashToBit();
