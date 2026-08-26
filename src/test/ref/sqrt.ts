// Legendre symbols in BN254 Fr, used by the FMD clue-bit derivation.
//
// `modPow` uses repeated squaring; direct exponentiation would produce an
// unbounded intermediate.

import { mod } from "./field.js";

function modPow(base: bigint, exp: bigint, p: bigint): bigint {
    let r = 1n;
    let b = mod(base, p);
    let e = exp;
    while (e > 0n) {
        if (e & 1n) r = (r * b) % p;
        e >>= 1n;
        b = (b * b) % p;
    }
    return r;
}

/** 1 if `a` is a non-zero quadratic residue mod `p`, -1 if a non-residue, 0 if zero. */
export function legendreSymbol(a: bigint, p: bigint): -1 | 0 | 1 {
    const am = mod(a, p);
    if (am === 0n) return 0;
    return modPow(am, (p - 1n) / 2n, p) === 1n ? 1 : -1;
}
