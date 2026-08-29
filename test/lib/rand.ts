// Seeded PRNG for tests that draw many values and must stay reproducible.
//
// Every entry point takes an explicit seed, so a failing case can be replayed.
// 64-bit LCG with the Knuth/MMIX multiplier; not suitable for cryptographic use.

const LCG_MULT = 6364136223846793005n;
const LCG_INC = 1442695040888963407n;

/** Successive states of the LCG seeded at `seed`, each masked to `bits`. */
export function lcg(seed: bigint, bits: bigint): () => bigint {
    const mask = (1n << bits) - 1n;
    let state = seed;
    return () => {
        state = (state * LCG_MULT + LCG_INC) & mask;
        return state;
    };
}

/** `count` values in [0, bound), from a fixed seed. */
export function seededInts(seed: number, count: number, bound: number): number[] {
    const next = lcg(BigInt(seed), 64n);
    return Array.from({ length: count }, () => Number(next() % BigInt(bound)));
}
