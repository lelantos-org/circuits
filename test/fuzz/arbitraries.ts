// Property-based test arbitraries for the MASP circuits.
//
// Generated values stay inside circuit-enforced ranges (64-bit values, valid
// path indices) so positive properties do not trip a range check.
//
// Env vars:
//   FUZZ=light|medium|heavy            global run count (5 / 20 / 100)
//   FUZZ_RUNS_<SUITE>=N                per-suite override, takes precedence
//     SUITE keys: FIXEDBASE, FRONTIER, MERKLE, POLYEVAL, TRANSACT,
//                 TRANSACT_OVERFLOW, TRANSACT_VARIANTS

import * as fc from "fast-check";
import { BN254_FR } from "../helpers";

// FUZZ env: light=5, medium=20 (default), heavy=100.
const FUZZ = (process.env.FUZZ || "medium").toLowerCase();
export const NUM_RUNS =
    FUZZ === "heavy" ? 100 :
    FUZZ === "light" ? 5 :
    20;

export const fcParams = { numRuns: NUM_RUNS };

// 64-bit value used by transact circuit (range-checked via Num2Bits(64)).
export const MAX_VALUE = (1n << 64n) - 1n;

// BN254 scalar field modulus — used by every gadget that constrains a Field.
export const R = BN254_FR;

// Canonical-positive modulo, re-exported rather than redefined: the reference
// implementation owns it.
export { mod } from "../helpers";

// Random bigint in [0, max] from a fast-check uint sequence (deterministic seed).
export const arbField = (max: bigint = MAX_VALUE): fc.Arbitrary<bigint> =>
    fc.bigInt(0n, max);

// Blinding scalars as `MulH` admits them: `Num2Bits(RCV_BITS = 252)`. Boundary
// biased, because the interesting failures live at the window edges — the top
// partial window, an all-ones scalar, and the subgroup order itself.
export const MAX_BLINDER = (1n << 252n) - 1n;

export const arbBlinder = (): fc.Arbitrary<bigint> =>
    fc.oneof(
        { arbitrary: fc.bigInt(0n, MAX_BLINDER), weight: 7 },
        {
            arbitrary: fc.constantFrom(
                0n,
                1n,
                15n,
                16n,
                (1n << 251n) - 1n,
                1n << 251n,
                MAX_BLINDER - 1n,
                MAX_BLINDER,
            ),
            weight: 3,
        },
    );

// Avoid 0 so random nsks produce distinct pks reliably.
export const arbNsk = (): fc.Arbitrary<bigint> =>
    fc.bigInt(1n, (1n << 200n));

// Pair of values (v1, v2) and split point s such that v1+v2 fits in 64 bits.
// Returns (v1, v2, o1, o2) with o1+o2 == v1+v2 and each < 2^64.
export const arbBalancedSplit = (): fc.Arbitrary<{ v1: bigint; v2: bigint; o1: bigint; o2: bigint }> =>
    fc.tuple(
        fc.bigInt(0n, MAX_VALUE / 2n),
        fc.bigInt(0n, MAX_VALUE / 2n),
        fc.bigInt(0n, 1n << 60n),
    ).map(([v1, v2, splitSeed]) => {
        const total = v1 + v2;
        const o1 = total === 0n ? 0n : splitSeed % (total + 1n);
        return { v1, v2, o1, o2: total - o1 };
    });

// Distinct-pair arbitraries via chain (no .filter shrink penalty).
// If the second draw collides with the first, bump by +1 (wrapping at max).
export const arbDistinctBigInt = (min: bigint, max: bigint): fc.Arbitrary<[bigint, bigint]> =>
    fc.bigInt(min, max).chain(a =>
        fc.bigInt(min, max).map(b => {
            if (b !== a) return [a, b] as [bigint, bigint];
            const bumped = a === max ? min : a + 1n;
            return [a, bumped] as [bigint, bigint];
        }),
    );

export const arbDistinctInt = (min: number, max: number): fc.Arbitrary<[number, number]> =>
    fc.integer({ min, max }).chain(a =>
        fc.integer({ min, max }).map(b => {
            if (b !== a) return [a, b] as [number, number];
            const bumped = a === max ? min : a + 1;
            return [a, bumped] as [number, number];
        }),
    );

// Per-suite scaling for slow suites; an env override takes precedence.
const SUITE_SCALE: Record<string, number> = {
    FRONTIER: 0.25,
    TRANSACT_VARIANTS: 0.5,
    // Overflow path runs SDK + circuit per trial; cap tighter.
    TRANSACT_OVERFLOW: 0.25,
};

function runsFor(suite: string): number {
    const env = process.env[`FUZZ_RUNS_${suite}`];
    if (env) {
        const n = parseInt(env, 10);
        if (!isNaN(n) && n > 0) return n;
    }
    const scale = SUITE_SCALE[suite] ?? 1;
    return Math.max(2, Math.floor(NUM_RUNS * scale));
}

export function fcParamsFor<E = unknown>(
    suite: string,
    extra?: { examples?: E[] },
): { numRuns: number; examples?: E[] } {
    const out: { numRuns: number; examples?: E[] } = { numRuns: runsFor(suite) };
    if (extra?.examples && extra.examples.length > 0) out.examples = extra.examples;
    return out;
}
