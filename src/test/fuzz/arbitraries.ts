// Property-based test arbitraries for MASP circuits.
// Builds on existing helpers in ../helpers.ts (which re-exports SDK crypto).
// Keeps generated values inside circuit-enforced ranges (64-bit values, valid
// path indices) so positive properties don't trip range checks accidentally.

import * as fc from "fast-check";

// FUZZ env: light=5, medium=20 (default), heavy=100.
const FUZZ = (process.env.FUZZ || "medium").toLowerCase();
export const NUM_RUNS =
    FUZZ === "heavy" ? 100 :
    FUZZ === "light" ? 5 :
    20;

export const fcParams = { numRuns: NUM_RUNS };

// 64-bit value used by transact circuit (range-checked via Num2Bits(64)).
export const MAX_VALUE = (1n << 64n) - 1n;

// Random bigint in [0, max] from a fast-check uint sequence (deterministic seed).
export const arbField = (max: bigint = MAX_VALUE): fc.Arbitrary<bigint> =>
    fc.bigInt(0n, max);

// Avoid 0 so random nsks produce distinct pks reliably.
export const arbNsk = (): fc.Arbitrary<bigint> =>
    fc.bigInt(1n, (1n << 200n));

// Distinct rho/rcm/rcv suitable for note construction.
export const arbNote64 = (): fc.Arbitrary<{ value: bigint; rho: bigint; rcm: bigint; rcv: bigint }> =>
    fc.record({
        value: fc.bigInt(0n, MAX_VALUE),
        rho: fc.bigInt(1n, (1n << 200n)),
        rcm: fc.bigInt(1n, (1n << 200n)),
        rcv: fc.bigInt(1n, (1n << 200n)),
    });

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

// Path index per quaternary level: 0..3.
export const arbPathIndex = (): fc.Arbitrary<number> => fc.integer({ min: 0, max: 3 });

export const arbPathIndices = (depth: number): fc.Arbitrary<number[]> =>
    fc.array(arbPathIndex(), { minLength: depth, maxLength: depth });
