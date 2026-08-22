pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/babyjub.circom";
include "../../node_modules/circomlib/circuits/bitify.circom";

// Windowed fixed-base scalar multiplication on Baby-Jubjub.
//
// Window tables are `var` arithmetic, evaluated by the compiler at no
// constraint cost, and entry 0 is the identity so no offset compensation is
// required. Each window costs 4 selector products plus one constraint per
// coordinate: 748 constraints for a 252-bit scalar.
//
// Arithmetic stays in twisted Edwards. BabyAdd's addition law is complete on
// Baby-Jubjub — `a = 168700` is a quadratic residue and `d = 168696` is not, so
// `1 ± d·τ` never vanishes for on-curve operands — leaving no exceptional case.
//
// Window size 4 is optimal: a k-bit window costs 2^(k-1) - k + 8 constraints
// over ceil(N/k) windows, so at N = 252, k=2 costs 1008, k=3 and k=4 tie at
// 756, and k=5 costs 969.

// Baby-Jubjub twisted Edwards addition, evaluated at compile time. Same formula
// as circomlib's BabyAdd; complete, so it doubles and handles the identity
// without special cases.
function bjAdd(x1, y1, x2, y2) {
    var a = 168700;
    var d = 168696;

    var beta  = x1 * y2;
    var gamma = y1 * x2;
    var delta = (-a * x1 + y1) * (x2 + y2);
    var tau   = beta * gamma;

    var out[2];
    out[0] = (beta + gamma) / (1 + d * tau);
    out[1] = (delta + a * beta - gamma) / (1 - d * tau);
    return out;
}

// One window's lookup table: W[j] = j * B, for j in 0..15. W[0] is the identity.
function windowTable(bx, by) {
    var W[16][2];
    W[0][0] = 0;
    W[0][1] = 1;

    var px = bx;
    var py = by;
    W[1][0] = px;
    W[1][1] = py;

    for (var j = 2; j < 16; j++) {
        var next[2] = bjAdd(px, py, bx, by);
        px = next[0];
        py = next[1];
        W[j][0] = px;
        W[j][1] = py;
    }
    return W;
}

// Multilinear (Möbius) coefficients of the 8 table entries W[8*half .. 8*half+7]
// in coordinate `coord`, over the selector bits s0, s1, s2:
//
//     W[j] = sum over m of coef[m] * prod(s_b : b in m)      for j on {0,1}^3
//     coef[m] = sum over j subset of m of (-1)^(|m|-|j|) * W[j]
//
// Derived rather than transcribed. The explicit form is 16 sixteen-term
// alternating sums per coordinate, where one sign error yields a gadget that is
// wrong only for the scalars selecting that entry.
function mobius8(W, half, coord) {
    var coef[8];
    for (var m = 0; m < 8; m++) {
        coef[m] = 0;
        for (var j = 0; j < 8; j++) {
            if ((j & m) == j) {
                var pop = 0;
                for (var b = 0; b < 3; b++) {
                    pop += ((m >> b) & 1) - ((j >> b) & 1);
                }
                coef[m] += (pop % 2 == 0 ? 1 : -1) * W[8 * half + j][coord];
            }
        }
    }
    return coef;
}

// out = e * BASE, with `e` given as N_BITS LSB-first bits.
//
// DANGER: the caller MUST constrain every e[i] to {0,1}. The window lookup is a
// multilinear extension of the table and agrees with it only on the boolean
// cube; off it a prover steers the output to an arbitrary field pair. That pair
// need not be on the curve, and BabyAdd's `(1 + d*tau) * xout === beta + gamma`
// leaves `xout` unconstrained when `1 + d*tau` vanishes, so a missing
// booleanity constraint can make the circuit under-constrained.
//
// Use `FixedBaseMul` below unless the caller already holds a constrained bit
// array to share.
//
// Bits above the top window are zero-padded, so N_BITS need not be a multiple
// of 4. The scalar is reduced modulo the subgroup order by the group itself; no
// range check is implied here.
template FixedBaseMulBits(N_BITS, BASE) {
    signal input e[N_BITS];
    signal output out[2];

    var nWindows = (N_BITS + 3) \ 4;

    signal sel[nWindows][4];
    // prod[m] = product of the selector bits in mask m, indexed so that
    // coefficient m multiplies prod[m]. Only masks 3, 5, 6, 7 are real products.
    signal prod[nWindows][8];
    signal wx[nWindows];
    signal wy[nWindows];

    component adder[nWindows - 1];

    var bx = BASE[0];
    var by = BASE[1];

    for (var i = 0; i < nWindows; i++) {
        var W[16][2] = windowTable(bx, by);

        for (var b = 0; b < 4; b++) {
            var pos = 4 * i + b;
            sel[i][b] <== pos < N_BITS ? e[pos] : 0;
        }

        prod[i][0] <== 1;
        prod[i][1] <== sel[i][0];
        prod[i][2] <== sel[i][1];
        prod[i][3] <== sel[i][1] * sel[i][0];
        prod[i][4] <== sel[i][2];
        prod[i][5] <== sel[i][2] * sel[i][0];
        prod[i][6] <== sel[i][2] * sel[i][1];
        prod[i][7] <== prod[i][6] * sel[i][0];

        // Split on the top bit: out = lo + s3 * (hi - lo), where lo and hi
        // interpolate the bottom and top halves of the table. One constraint per
        // coordinate, the four products above shared between them.
        var loX[8] = mobius8(W, 0, 0);
        var hiX[8] = mobius8(W, 1, 0);
        var loY[8] = mobius8(W, 0, 1);
        var hiY[8] = mobius8(W, 1, 1);

        var accLoX = 0;
        var accHiX = 0;
        var accLoY = 0;
        var accHiY = 0;
        for (var m = 0; m < 8; m++) {
            accLoX += loX[m] * prod[i][m];
            accHiX += (hiX[m] - loX[m]) * prod[i][m];
            accLoY += loY[m] * prod[i][m];
            accHiY += (hiY[m] - loY[m]) * prod[i][m];
        }

        wx[i] <== accHiX * sel[i][3] + accLoX;
        wy[i] <== accHiY * sel[i][3] + accLoY;

        // Window 0 seeds the accumulator, so it costs no addition.
        if (i > 0) {
            adder[i - 1] = BabyAdd();
            if (i == 1) {
                adder[i - 1].x1 <== wx[0];
                adder[i - 1].y1 <== wy[0];
            } else {
                adder[i - 1].x1 <== adder[i - 2].xout;
                adder[i - 1].y1 <== adder[i - 2].yout;
            }
            adder[i - 1].x2 <== wx[i];
            adder[i - 1].y2 <== wy[i];
        }

        // Advance the window base by 2^4.
        for (var k = 0; k < 4; k++) {
            var dbl[2] = bjAdd(bx, by, bx, by);
            bx = dbl[0];
            by = dbl[1];
        }
    }

    if (nWindows == 1) {
        out[0] <== wx[0];
        out[1] <== wy[0];
    } else {
        out[0] <== adder[nWindows - 2].xout;
        out[1] <== adder[nWindows - 2].yout;
    }
}

// out = scalar * BASE, decomposing the scalar here.
//
// Owns its Num2Bits, so the selector booleanity the table lookup depends on
// cannot be dropped by a caller.
//
// N_BITS must satisfy 2^N_BITS < p for the decomposition to be alias-free,
// which holds at the 252 bits MulH uses.
template FixedBaseMul(N_BITS, BASE) {
    signal input scalar;
    signal output out[2];

    component bits = Num2Bits(N_BITS);
    bits.in <== scalar;

    component mul = FixedBaseMulBits(N_BITS, BASE);
    for (var i = 0; i < N_BITS; i++) {
        mul.e[i] <== bits.out[i];
    }

    out[0] <== mul.out[0];
    out[1] <== mul.out[1];
}
