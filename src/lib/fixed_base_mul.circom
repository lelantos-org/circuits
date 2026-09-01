pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/babyjub.circom";
include "../../node_modules/circomlib/circuits/bitify.circom";

// Windowed fixed-base scalar multiplication on Baby-Jubjub.
//
// Window tables are `var` arithmetic, folded by the compiler at no constraint
// cost, and entry 0 is the identity, so no offset compensation is required.
// Each window costs 4 selector products plus one constraint per coordinate:
// 748 constraints for a 252-bit scalar.
//
// Arithmetic stays in twisted Edwards. BabyAdd's addition law is complete on
// Baby-Jubjub — `a = 168700` is a quadratic residue and `d = 168696` is not, so
// `1 ± d·τ` never vanishes for on-curve operands — leaving no exceptional case.
//
// Window size 4 minimises cost: a k-bit window costs 2^(k-1) - k + 8
// constraints over ceil(N/k) windows, so at N = 252, k=2 costs 1008, k=3 and
// k=4 tie at 756, and k=5 costs 969.
//
// The coefficient table must reach the gadget as a template parameter, never as
// a `var` computed in a template body. circom emits a template body into the
// witness generator as well as into the constraint system and does not prove
// that a `var` chain is input-independent, so a `windowTable` call in a body is
// compiled to wasm and re-executed on every proof, per component instance. Each
// `bjAdd` costs two modular inversions and a window needs 18 of them, so over
// 63 windows the 20 `MulH` instances of `Transact(11, 4, 6)` would cost roughly
// 45,000 inversions per witness — more than the Groth16 phase they save.
//
// Template arguments must be compile-time known, so circom evaluates them
// during instantiation and folds the results into the emitted coefficients.
// `fixedBaseCoefs` is therefore called only from an argument position, and
// `FixedBaseMulBits` takes coefficients rather than a base point. Moving that
// call into a body regresses witness-generation time only: the constraint
// count, the vectors and every test are unaffected.

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
// Computed rather than transcribed: the explicit form is 16 sixteen-term
// alternating sums per coordinate, and a single sign error there breaks only
// the scalars that select the affected entry.
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

// Windows covered by `fixedBaseCoefs`: enough for a 252-bit scalar, the widest
// the field admits alias-free (2^252 < p) and the width `RCV_BITS()` uses.
//
// A literal rather than a function of N_BITS: circom requires array lengths
// inside a `function` to be constant, and a function's own parameters do not
// qualify, unlike a template's.
function FIXED_BASE_WINDOWS() { return 63; }

// Per-window multilinear coefficients for BASE, indexed [window][row][mask]:
//
//   row 0  loX      row 1  hiX - loX
//   row 2  loY      row 3  hiY - loY
//
// The hi-minus-lo differences are taken here so the template body holds no
// compile-time arithmetic.
//
// Window i is built over base 16^i * BASE, advanced by four doublings per step.
// The sequence does not depend on the scalar width, so a narrower instance
// reads a prefix of the same table and one table serves every width.
//
// Call only from a template argument position (see header), where it runs once
// per instantiation in the compiler and never reaches the witness generator.
function fixedBaseCoefs(BASE) {
    var C[63][4][8];

    var bx = BASE[0];
    var by = BASE[1];

    for (var i = 0; i < FIXED_BASE_WINDOWS(); i++) {
        var W[16][2] = windowTable(bx, by);

        var loX[8] = mobius8(W, 0, 0);
        var hiX[8] = mobius8(W, 1, 0);
        var loY[8] = mobius8(W, 0, 1);
        var hiY[8] = mobius8(W, 1, 1);

        for (var m = 0; m < 8; m++) {
            C[i][0][m] = loX[m];
            C[i][1][m] = hiX[m] - loX[m];
            C[i][2][m] = loY[m];
            C[i][3][m] = hiY[m] - loY[m];
        }

        // Advance the window base by 2^4.
        for (var k = 0; k < 4; k++) {
            var dbl[2] = bjAdd(bx, by, bx, by);
            bx = dbl[0];
            by = dbl[1];
        }
    }

    return C;
}

// out = e * BASE, with `e` given as N_BITS LSB-first bits and BASE supplied
// through `COEFS = fixedBaseCoefs(BASE)`.
//
// Precondition: the caller must constrain every e[i] to {0,1}. The window
// lookup is a multilinear extension of the table and agrees with it only on the
// boolean cube; off it a prover steers the output to an arbitrary field pair.
// That pair need not be on the curve, and BabyAdd's
// `(1 + d*tau) * xout === beta + gamma` leaves `xout` unconstrained when
// `1 + d*tau` vanishes, so a missing booleanity constraint leaves the circuit
// under-constrained.
//
// Use `FixedBaseMul` below unless the caller already holds a constrained bit
// array to share: it derives COEFS itself and cannot be handed a table that
// disagrees with the intended base.
//
// Bits above the top window are zero-padded, so N_BITS need not be a multiple
// of 4. The scalar is reduced modulo the subgroup order by the group itself; no
// range check is implied here.
template FixedBaseMulBits(N_BITS, COEFS) {
    signal input e[N_BITS];
    signal output out[2];

    var nWindows = (N_BITS + 3) \ 4;
    // COEFS carries FIXED_BASE_WINDOWS() windows and this reads a prefix of it.
    // N_BITS is a template parameter, so this folds away at compile time.
    assert(nWindows <= FIXED_BASE_WINDOWS());

    signal sel[nWindows][4];
    // prod[m] = product of the selector bits in mask m, indexed so that
    // coefficient m multiplies prod[m]. Only masks 3, 5, 6, 7 are real products.
    signal prod[nWindows][8];
    signal wx[nWindows];
    signal wy[nWindows];

    component adder[nWindows - 1];

    for (var i = 0; i < nWindows; i++) {
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
        var accLoX = 0;
        var accHiX = 0;
        var accLoY = 0;
        var accHiY = 0;
        for (var m = 0; m < 8; m++) {
            accLoX += COEFS[i][0][m] * prod[i][m];
            accHiX += COEFS[i][1][m] * prod[i][m];
            accLoY += COEFS[i][2][m] * prod[i][m];
            accHiY += COEFS[i][3][m] * prod[i][m];
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

    component mul = FixedBaseMulBits(N_BITS, fixedBaseCoefs(BASE));
    for (var i = 0; i < N_BITS; i++) {
        mul.e[i] <== bits.out[i];
    }

    out[0] <== mul.out[0];
    out[1] <== mul.out[1];
}
