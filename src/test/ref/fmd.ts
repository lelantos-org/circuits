// Fuzzy Message Detection — FMD2, lelantos.fmd.v3 (Poseidon + Legendre symbol).
//
// bit = 1 iff the Poseidon output is a quadratic residue in F_r. Tunable
// false-positive rate p = 2^-gamma; default gamma = 5 => 1/32.
//
//   detection key  dk = (x_1..x_gamma)
//   flag key       fk = (X_1..X_gamma), X_i = B·x_i
//
// Sender flags for fk:
//   r <- Z_q*, R = B·r, S_i = r·X_i
//   bit_i = legendre_bit(Poseidon([TAG_FMD_BIT, R.x, R.y, i, S_i.x, S_i.y]))
//   c_i   = bit_i XOR 1
//
// `out_clue_Rx`, `out_clue_Ry` and `out_clue_bits` carry no in-circuit
// constraints; PolyEval is their only binding. A wrong Legendre symbol or
// bit-packing order therefore produces witnesses the circuit accepts, and is
// detectable only through the published vectors.

import { BABYJUB_SUBGROUP_ORDER, BN254_FR, type Field, type Point } from "./field.js";
import { packBits, unpackBits } from "./bytes.js";
import type { Jubjub } from "./jubjub.js";
import type { Poseidon } from "./poseidon.js";
import { legendreSymbol } from "./sqrt.js";
import { TAG_FMD_BIT } from "./tags.js";

export const FMD_DEFAULT_GAMMA = 5;
export const FMD_DOMAIN = "lelantos.fmd.v3";

export interface FmdDetectionKey {
    x: Field[];
}

export interface FmdFlagKey {
    X: Point[];
}

export interface FmdClue {
    R: Uint8Array;
    bits: Uint8Array;
    gamma: number;
}

export function fmdGenDetectionKey(
    randomScalar: () => Field,
    gamma = FMD_DEFAULT_GAMMA,
): FmdDetectionKey {
    const x = Array.from({ length: gamma }, () => {
        const xi = randomScalar() % BABYJUB_SUBGROUP_ORDER;
        return xi === 0n ? 1n : xi;
    });
    return { x };
}

export function fmdFlagKeyFromDetection(J: Jubjub, dk: FmdDetectionKey): FmdFlagKey {
    return { X: dk.x.map((xi) => J.mulPointEscalar(J.base8, xi)) };
}

export function fmdFlag(J: Jubjub, P: Poseidon, fk: FmdFlagKey, r: Field): FmdClue {
    const gamma = fk.X.length;
    const rMod = r % BABYJUB_SUBGROUP_ORDER;
    if (rMod === 0n) throw new Error("fmd flag: r must be non-zero mod q");

    const R = J.mulPointEscalar(J.base8, rMod);
    const Rpacked = J.packPoint(R);

    const cBits = fk.X.map((Xi, i) => {
        const shared = J.mulPointEscalar(Xi, rMod);
        return sharedBit(P, R, i, shared) ^ 1;
    });

    return { R: Rpacked, bits: packBits(cBits), gamma };
}

export function fmdTest(J: Jubjub, P: Poseidon, dk: FmdDetectionKey, clue: FmdClue): boolean {
    if (dk.x.length !== clue.gamma) return false;
    const R = J.unpackPoint(clue.R);
    if (!R || !J.inSubgroup(R)) return false;

    const cBits = unpackBits(clue.bits, clue.gamma);
    for (let i = 0; i < clue.gamma; i++) {
        const shared = J.mulPointEscalar(R, dk.x[i]);
        if ((sharedBit(P, R, i, shared) ^ cBits[i]) !== 1) return false;
    }
    return true;
}

export function encodeClue(c: FmdClue): Uint8Array {
    const out = new Uint8Array(1 + 32 + c.bits.length);
    out[0] = c.gamma;
    out.set(c.R, 1);
    out.set(c.bits, 33);
    return out;
}

export function decodeClue(buf: Uint8Array): FmdClue {
    const gamma = buf[0];
    return {
        gamma,
        R: buf.slice(1, 33),
        bits: buf.slice(33, 33 + Math.ceil(gamma / 8)),
    };
}

/** One output's clue, in the shape the circuit's PI slots want it. */
export interface ClueWitness {
    /** `clue.bits` read back as a little-endian integer — the `out_clue_bits` slot. */
    clueBits: Field;
    clueRx: Field;
    clueRy: Field;
    /** The scalar behind R. The circuit ignores it; the vectors record it. */
    r: Field;
    /** The full clue, for wire-format checks. */
    clue: FmdClue;
}

/**
 * Deterministic clue source for tests and the vector generator.
 *
 * The clue signals carry no in-circuit constraints, so any well-formed
 * Baby-Jubjub R with honest bits satisfies the circuit. The values are
 * published in `vectors/`, so they must be reproducible: the detection key uses
 * a fixed generator and `r` is counter-driven.
 */
export function deterministicClueGen(P: Poseidon, J: Jubjub, gamma = FMD_DEFAULT_GAMMA) {
    const dk = fmdGenDetectionKey(() => 1n, gamma);
    const fk = fmdFlagKeyFromDetection(J, dk);
    let counter = 0n;

    return {
        dk,
        fk,
        next(): ClueWitness {
            counter += 1n;
            const r = (counter * 1234567n + 89n) % BABYJUB_SUBGROUP_ORDER;
            const rSafe = r === 0n ? 1n : r;
            const clue = fmdFlag(J, P, fk, rSafe);
            // `clue.bits` is a packed BYTE array (ceil(gamma/8) bytes); this reads
            // it back little-endian into the single field element the slot holds.
            let clueBits = 0n;
            for (let i = 0; i < clue.bits.length; i++) {
                clueBits |= BigInt(clue.bits[i]) << BigInt(8 * i);
            }
            const R = J.mulPointEscalar(J.base8, rSafe);
            return { clueBits, clueRx: R[0], clueRy: R[1], r: rSafe, clue };
        },
    };
}

// Legendre-symbol bit of Poseidon([TAG_FMD_BIT, R.x, R.y, i, S.x, S.y]).
// Six-input layout, matching the clue-bit derivation; bit = 1 iff QR.
function sharedBit(P: Poseidon, R: Point, i: number, shared: Point): number {
    const h = P.hash([TAG_FMD_BIT, R[0], R[1], BigInt(i), shared[0], shared[1]]);
    const sym = legendreSymbol(h, BN254_FR);
    if (sym === 0) throw new Error("FMD shared bit: hash collided to zero");
    return sym === 1 ? 1 : 0;
}
