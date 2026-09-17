// Property-based test arbitraries for the MASP circuits.
//
// Generated values stay inside circuit-enforced ranges (64-bit values, valid
// path indices) so positive properties do not trip a range check.
//
// Env vars:
//   FUZZ=light|medium|heavy            global run count (5 / 20 / 100)
//   FUZZ_RUNS_<SUITE>=N                per-suite override, takes precedence
//     SUITE keys: BALANCE, FIXEDBASE, FRONTIER, MERKLE, POLYEVAL, TRANSACT,
//                 TRANSACT_OVERFLOW, TRANSACT_VARIANTS, UNDERCONSTRAINED
//   FUZZ_SEED=N                        pin the fast-check seed (see below)
//   FUZZ_PATH=a:b:c                    replay one shrunk counterexample

import * as fc from "fast-check";
import { BN254_FR } from "../helpers";

const FUZZ = (process.env.FUZZ || "medium").toLowerCase();
export const NUM_RUNS =
    FUZZ === "heavy" ? 100 :
    FUZZ === "light" ? 5 :
    20;

// ===== replayability =====
//
// By default fast-check seeds from the clock, so a failing run cannot be
// regenerated, and the seed it prints appears only in CI logs that expire.
//
// The seed is therefore chosen here: pinned when `FUZZ_SEED` is set, otherwise
// drawn once per process and printed to stderr. Every suite shares the value,
// so a single `FUZZ_SEED=... just test-fuzz` reproduces the whole run.
// `.github/workflows/fuzz.yml` sets it and writes the replay line into the job
// summary, which outlives the log.
//
// `FUZZ_PATH` replays a single shrunk counterexample: pass the `path` from a
// fast-check report with its seed to go directly to that case. A path is
// meaningful only for the property that produced it, and this sets it for every
// property in the process, so combine it with a mocha `--grep` that isolates
// the failing test:
//
//   FUZZ_SEED=<seed> FUZZ_PATH=<path> npm run test:fuzz -- --grep "<test name>"

function readSeed(): number {
    const raw = process.env.FUZZ_SEED;
    if (raw === undefined || raw === "") return Date.now();
    const n = Number(raw);
    if (!Number.isFinite(n)) {
        throw new Error(`FUZZ_SEED must be a number, got "${raw}"`);
    }
    return n;
}

export const FUZZ_SEED = readSeed();

/** Set only when replaying; `undefined` lets fast-check run the full sequence. */
const FUZZ_PATH = process.env.FUZZ_PATH || undefined;

// Printed once per process, on stderr so a reporter that buffers stdout does
// not hide it. Printed on passing runs too, so they are repeatable.
console.error(
    `[fuzz] FUZZ=${FUZZ} FUZZ_SEED=${FUZZ_SEED}` +
        (FUZZ_PATH ? ` FUZZ_PATH=${FUZZ_PATH}` : "") +
        `  (replay: FUZZ=${FUZZ} FUZZ_SEED=${FUZZ_SEED} just test-fuzz)`,
);

export const fcParams = { numRuns: NUM_RUNS, seed: FUZZ_SEED, path: FUZZ_PATH };

// 64-bit value used by transact circuit (range-checked via Num2Bits(64)).
export const MAX_VALUE = (1n << 64n) - 1n;

// BN254 scalar field modulus — used by every gadget that constrains a Field.
export const R = BN254_FR;

// Canonical-positive modulo, re-exported from the reference implementation.
export { mod } from "../helpers";

// Random bigint in [0, max] from a fast-check uint sequence (deterministic seed).
export const arbField = (max: bigint = MAX_VALUE): fc.Arbitrary<bigint> =>
    fc.bigInt(0n, max);

// Blinding scalars as `MulH` admits them: `Num2Bits(RCV_BITS = 252)`. Biased
// toward the window edges: the top partial window, an all-ones scalar, and the
// subgroup order.
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
    // Each trial builds a witness and then sweeps all ~100k of its entries,
    // re-checking the full system once per finding.
    UNDERCONSTRAINED: 0.25,
    // Same search over the larger batch R1CS, ~8.5s per trial. Unlisted suites
    // default to scale 1.
    UNDERCONSTRAINED_BATCH: 0.25,
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

export interface FcParams<E> {
    numRuns: number;
    seed: number;
    path?: string;
    examples?: E[];
}

/**
 * Per-suite fast-check parameters. Every suite carries the same `FUZZ_SEED`, so
 * one env var reproduces a whole run; `runsFor` still scales the trial count
 * per suite.
 */
export function fcParamsFor<E = unknown>(
    suite: string,
    extra?: { examples?: E[] },
): FcParams<E> {
    const out: FcParams<E> = { numRuns: runsFor(suite), seed: FUZZ_SEED, path: FUZZ_PATH };
    if (extra?.examples && extra.examples.length > 0) out.examples = extra.examples;
    return out;
}

// ===== per-asset balance shapes =====
//
// `PerAssetValueBalance(N_IN, N_OUT)` sweeps N_IN + N_OUT + 1 candidate assets,
// so its behaviour depends on how assets are spread across slots rather than on
// the values alone. The transact-level arbitraries above are single-asset (a
// witness there costs a tree, four authentication paths and a 100k-constraint
// circuit); these draw the gadget's inputs directly, which is cheap enough to
// vary the asset layout itself.

/** A 64-bit asset id. Never 0: the circuits reject `asset_id == 0` on real slots. */
export const arbAssetId = (): fc.Arbitrary<bigint> =>
    fc.oneof(
        // Small ids, as a registry would assign them, so collisions between
        // slots are common and duplicate candidate rows get exercised.
        { arbitrary: fc.bigInt(1n, 8n), weight: 3 },
        { arbitrary: fc.bigInt(1n, MAX_VALUE), weight: 1 },
    );

/** Values are capped so that a whole side sums well below the modulus. */
const MAX_SLOT_VALUE = 1n << 60n;

export interface AssetBalanceShape {
    inAsset: bigint[];
    inValue: bigint[];
    outAsset: bigint[];
    outValue: bigint[];
    publicAssetId: bigint;
    publicIn: bigint;
    publicOut: bigint;
}

/**
 * A per-asset balanced shape: every asset's inputs plus its transparent bucket
 * equal its outputs plus the other bucket, exactly as the gadget requires.
 *
 * Output slots `j < N_IN` take input slot `j`'s asset, so no input asset can be
 * left without an output slot to be spent into; the remaining output slots
 * repeat one of those assets. `publicMode` picks between no transparent bucket,
 * a deposit, a withdrawal and an orphan asset whose two buckets cancel — the
 * last being the only case where `public_asset_id` names an asset no note
 * carries.
 */
export const arbBalancedAssetShape = (
    nIn: number,
    nOut: number,
): fc.Arbitrary<AssetBalanceShape> => {
    if (nOut < nIn) throw new Error("arbBalancedAssetShape: nOut must be at least nIn");
    return fc.tuple(
        fc.array(arbAssetId(), { minLength: nIn, maxLength: nIn }),
        fc.array(fc.bigInt(0n, MAX_SLOT_VALUE), { minLength: nIn, maxLength: nIn }),
        fc.array(fc.nat({ max: nIn - 1 }), { minLength: nOut - nIn, maxLength: nOut - nIn }),
        fc.array(fc.bigInt(0n, 1n << 62n), { minLength: nOut, maxLength: nOut }),
        fc.nat({ max: 3 }),
        fc.bigInt(0n, MAX_SLOT_VALUE),
        arbAssetId(),
    ).map(([inAsset, inValue, extraPicks, splitSeeds, publicMode, publicAmount, orphan]) => {
        const outAsset = [
            ...inAsset,
            ...extraPicks.map(i => inAsset[i]),
        ];

        // Per-asset totals the outputs must reproduce.
        const totals = new Map<bigint, bigint>();
        for (let i = 0; i < nIn; i++) {
            totals.set(inAsset[i], (totals.get(inAsset[i]) ?? 0n) + inValue[i]);
        }

        let publicAssetId = orphan;
        let publicIn = 0n;
        let publicOut = 0n;
        if (publicMode === 1) {
            // Deposit: the bucket adds to an asset the notes already carry.
            publicAssetId = inAsset[0];
            publicIn = publicAmount;
            totals.set(publicAssetId, (totals.get(publicAssetId) ?? 0n) + publicIn);
        } else if (publicMode === 2) {
            // Withdrawal, capped at what that asset actually holds.
            publicAssetId = inAsset[0];
            const held = totals.get(publicAssetId) ?? 0n;
            publicOut = held === 0n ? 0n : publicAmount % (held + 1n);
            totals.set(publicAssetId, held - publicOut);
        } else if (publicMode === 3) {
            // Both buckets equal, so the row reads `x + p == x + p` whether or
            // not the drawn id collides with an asset the notes carry.
            publicIn = publicAmount;
            publicOut = publicAmount;
        }

        // Split each asset's total across the output slots carrying it.
        const outValue = Array<bigint>(nOut).fill(0n);
        for (const [asset, total] of totals) {
            const slots = outAsset.flatMap((a, j) => (a === asset ? [j] : []));
            let left = total;
            for (let k = 0; k < slots.length - 1; k++) {
                const share = left === 0n ? 0n : splitSeeds[slots[k]] % (left + 1n);
                outValue[slots[k]] = share;
                left -= share;
            }
            outValue[slots[slots.length - 1]] = left;
        }

        return { inAsset, inValue, outAsset, outValue, publicAssetId, publicIn, publicOut };
    });
};
