// The bit-decomposition half of the negative-test generator.
//
// `underconstrained.ts` sweeps one signal at a time, which by construction
// cannot see a bug that needs several signals to move together. The most
// important such bug in a circom circuit is the bit decomposition, and it fails
// in two ways:
//
//   1. ALIASING. `Num2Bits(n)` with `2^n > p` does not determine its input: the
//      bits of `v` and the bits of `v + p` both satisfy the weighted sum, since
//      the sum is taken mod `p`. A range check built on it proves nothing, and a
//      value near `p` passes as a small one. Only `n >= 254` is affected on
//      BN254 — `2^253 < p < 2^254`.
//
//   2. MISSING BOOLEANITY. If a signal carrying weight `2^k` in the sum is not
//      itself pinned to {0, 1}, the "bit" is a free field element and the sum
//      constrains nothing at all: any target is reachable by solving for it.
//
// Both are properties of the CONSTRAINT SYSTEM alone — no witness, no sampling,
// and every instance in the circuit is covered rather than a sample of them. So
// this runs as a structural check rather than a mutation: a mutation can only
// demonstrate the bug where it exists, while the check below rules it out
// everywhere at once, which is the stronger statement when it passes.
//
// Groups are recovered from the coefficients, not from `.sym` names, so a
// hand-rolled decomposition that never mentions `Num2Bits` is covered too.

import { mod, type LinearCombination, type R1csView } from "./r1cs";

/** Largest power of two below `p`: a decomposition wider than this can alias. */
export const MAX_SAFE_BITS = 253;

/**
 * Run length at which consecutive powers of two are taken to mean a
 * decomposition even when no digit carries a booleanity constraint.
 */
export const MIN_UNAMBIGUOUS_WIDTH = 8;

export interface BitGroup {
    /** Constraint the weighted sum appears in. */
    constraint: number;
    /** Which of A, B, C carried it. */
    slot: "A" | "B" | "C";
    /** Number of consecutive weights `2^0 .. 2^(width-1)` found. */
    width: number;
    /** Witness index carrying weight `2^k`, indexed by `k`. */
    signals: number[];
    /** Weights whose signal is NOT pinned to {0, 1} by any constraint. */
    unconstrainedBits: number[];
}

/**
 * Signals some constraint pins to exactly {0, 1}.
 *
 * A booleanity constraint mentions one signal and the constant, so
 * `f(t) = (a·t + a0)(b·t + b0) - (c·t + c0)` is fully determined by the
 * coefficients — no witness needed. It pins `t` to {0, 1} when it is genuinely
 * quadratic (`a·b != 0`, else it has a single root) and vanishes at both 0 and
 * 1. That covers circom's `b * (b - 1) === 0` and any re-association of it.
 */
export function booleanSignals(view: R1csView): Set<number> {
    const out = new Set<number>();

    for (const [A, B, C] of view.constraints) {
        const signal = loneSignal(A, B, C);
        if (signal === null) continue;

        const key = String(signal);
        const a = mod(A[key] ?? 0n);
        const b = mod(B[key] ?? 0n);
        const c = mod(C[key] ?? 0n);
        const a0 = mod(A["0"] ?? 0n);
        const b0 = mod(B["0"] ?? 0n);
        const c0 = mod(C["0"] ?? 0n);

        if (mod(a * b) === 0n) continue;                  // linear: one root, not two
        if (mod(a0 * b0 - c0) !== 0n) continue;           // f(0) != 0
        if (mod((a + a0) * (b + b0) - (c + c0)) !== 0n) continue; // f(1) != 0
        out.add(signal);
    }

    return out;
}

/**
 * The single non-constant witness index a constraint mentions, or null when it
 * mentions none or more than one.
 */
function loneSignal(...lcs: LinearCombination[]): number | null {
    let found: number | null = null;
    for (const lc of lcs) {
        for (const key in lc) {
            const s = Number(key);
            if (s === 0) continue;
            if (found === null) found = s;
            else if (found !== s) return null;
        }
    }
    return found;
}

/**
 * Every weighted-sum group in the system, with the booleanity of each weight
 * resolved.
 *
 * A group is a linear combination carrying the consecutive weights
 * `2^0, 2^1, ... 2^(width-1)`, at least one of whose signals some constraint
 * pins to {0, 1}. Both halves of that are needed:
 *
 *   - The run must start at `2^0`. A decomposition always has a units digit,
 *     while an isolated `2^k` coefficient is ordinary arithmetic.
 *   - Some digit must actually be a bit. Weights `1, 2` alone are far too common
 *     to mean anything — in `4x6` that pattern matches 1328 linear combinations
 *     of which none is a decomposition, against 87 that are. Requiring one real
 *     bit separates the two exactly, and it does not blunt the search this
 *     feeds: a decomposition whose digits are ALL free is not an underconstrained
 *     decomposition, it is not a decomposition at all, and the signals in it are
 *     covered one at a time by the sweep in `underconstrained.ts`.
 */
export function findBitGroups(view: R1csView): BitGroup[] {
    const booleans = booleanSignals(view);
    const weights = powerOfTwoWeights();

    const groups: BitGroup[] = [];
    const slots = ["A", "B", "C"] as const;

    for (let k = 0; k < view.constraints.length; k++) {
        const constraint = view.constraints[k];
        for (let si = 0; si < 3; si++) {
            const group = scanLc(constraint[si], k, slots[si], weights, booleans);
            if (group !== null) groups.push(group);
        }
    }

    return groups;
}

/** A power-of-two coefficient: which exponent, and with which sign. */
interface Weight {
    exponent: number;
    negative: boolean;
}

/**
 * Coefficient value -> the power of two it represents, in BOTH polarities.
 *
 * circom does not emit a decomposition as `sum 2^i b_i`; it emits the equality
 * `in === lc1` as the single linear constraint `in - lc1 = 0`, so the bits carry
 * NEGATIVE weights `p - 2^i` and only `in` is positive. Matching one polarity
 * finds nothing at all — the detector reports zero groups on a circuit full of
 * them, and every test built on it passes vacuously, which is exactly how the
 * first draft of this file behaved.
 */
function powerOfTwoWeights(): Map<bigint, Weight> {
    const weights = new Map<bigint, Weight>();
    for (let exponent = 0; exponent < 256; exponent++) {
        const w = mod(1n << BigInt(exponent));
        if (!weights.has(w)) weights.set(w, { exponent, negative: false });
        const nw = mod(-w);
        if (!weights.has(nw)) weights.set(nw, { exponent, negative: true });
    }
    return weights;
}

/**
 * The decomposition a linear combination carries, or null if it carries none.
 *
 * The two polarities are collected in one pass but kept apart, so a combination
 * that happens to mix signs cannot be spliced into a run that is not there. A
 * decomposition is written in one polarity; the other can at best pick up a
 * stray `2^0`, so the wider reading is the real one.
 */
function scanLc(
    lc: LinearCombination,
    constraint: number,
    slot: BitGroup["slot"],
    weights: Map<bigint, Weight>,
    booleans: Set<number>,
): BitGroup | null {
    // exponent -> signal, per polarity. A repeated exponent means the "digit" is
    // a sum of two signals and the run is not a decomposition, so that polarity
    // is abandoned rather than guessing which signal owns the weight.
    const byExponent: [Map<number, number> | null, Map<number, number> | null] =
        [new Map(), new Map()];

    for (const key in lc) {
        const signal = Number(key);
        if (signal === 0) continue;
        const weight = weights.get(mod(lc[key]));
        if (weight === undefined) continue;

        const side = weight.negative ? 1 : 0;
        const seen = byExponent[side];
        if (seen === null) continue;
        if (seen.has(weight.exponent)) byExponent[side] = null;
        else seen.set(weight.exponent, signal);
    }

    let best: BitGroup | null = null;
    for (const seen of byExponent) {
        if (seen === null) continue;
        const group = groupFrom(seen, constraint, slot, booleans);
        if (group !== null && (best === null || group.width > best.width)) best = group;
    }
    return best;
}

/** Turn one polarity's exponent table into a group, if it looks like one. */
function groupFrom(
    byExponent: Map<number, number>,
    constraint: number,
    slot: BitGroup["slot"],
    booleans: Set<number>,
): BitGroup | null {
    // The run must start at `2^0`: a decomposition always has a units digit,
    // while an isolated `2^k` coefficient is ordinary arithmetic.
    let width = 0;
    while (byExponent.has(width)) width++;
    if (width < 2) return null; // a lone `2^0` is just a coefficient of 1

    const signals: number[] = [];
    const unconstrainedBits: number[] = [];
    for (let e = 0; e < width; e++) {
        const signal = byExponent.get(e) as number;
        signals.push(signal);
        if (!booleans.has(signal)) unconstrainedBits.push(e);
    }

    // Nothing here looks like a decomposition: no digit is a bit, and the run is
    // short enough that consecutive powers of two are unremarkable arithmetic.
    //
    // The width escape hatch matters. Requiring a bit would make the ONE case
    // this check exists for — a decomposition whose booleanity was forgotten
    // entirely — invisible, since with no bit among its digits it would be
    // filtered out as arithmetic. A run of `MIN_UNAMBIGUOUS_WIDTH` consecutive
    // powers of two is not something ordinary arithmetic produces; in `4x6`
    // every false match is width 2 and every real group is fully boolean, so the
    // two populations do not overlap at all.
    if (unconstrainedBits.length === width && width < MIN_UNAMBIGUOUS_WIDTH) return null;

    return { constraint, slot, width, signals, unconstrainedBits };
}

/** Groups wide enough that `2^width > p`, so the sum does not determine its value. */
export function aliasableGroups(groups: BitGroup[]): BitGroup[] {
    return groups.filter(g => g.width > MAX_SAFE_BITS);
}

/** Groups carrying a weight whose signal no constraint pins to {0, 1}. */
export function groupsWithFreeBits(groups: BitGroup[]): BitGroup[] {
    return groups.filter(g => g.unconstrainedBits.length > 0);
}

/** `width -> how many groups have it`, for the report. */
export function widthHistogram(groups: BitGroup[]): Map<number, number> {
    const out = new Map<number, number>();
    for (const g of groups) out.set(g.width, (out.get(g.width) ?? 0) + 1);
    return new Map([...out].sort((a, b) => a[0] - b[0]));
}
