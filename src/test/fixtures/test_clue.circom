pragma circom 2.2.3;

// Test wrapper: expose ClueCheck(GAMMA=5) directly, mirroring
// FMD_DEFAULT_GAMMA in sdk/src/fmd.ts. Lets us validate the FMD2
// bit-derivation + R = r·G_8 binding in isolation, without wiring through
// the full Transact circuit.

include "../../lib/clue.circom";

template TestClueCheckG5() {
    signal input r;
    signal input fk[5][2];
    signal input clue_bits;
    signal input legendre_bit[5];
    signal input legendre_y[5];
    signal output Rx;
    signal output Ry;

    component cc = ClueCheck(5);
    cc.r <== r;
    for (var i = 0; i < 5; i++) {
        cc.fk[i][0] <== fk[i][0];
        cc.fk[i][1] <== fk[i][1];
        cc.legendre_bit[i] <== legendre_bit[i];
        cc.legendre_y[i] <== legendre_y[i];
    }
    cc.clue_bits <== clue_bits;
    Rx <== cc.Rx;
    Ry <== cc.Ry;
}

component main = TestClueCheckG5();
