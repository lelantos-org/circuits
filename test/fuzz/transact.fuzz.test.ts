import * as fc from "fast-check";

import { commit } from "../helpers";
import { DEFAULT_ASSET as ASSET } from "../lib/transact";
import { expectAccepts, expectThrows, expectWitnessFails } from "../lib/expect";
import { useTransactCircuit } from "../transact/setup";
import {
    arbBalancedSplit, arbNsk, arbField, MAX_VALUE,
    fcParamsFor, arbDistinctBigInt,
} from "./arbitraries";
import { ALICE_NSK, BOB_NSK, TIMEOUT_HEAVY } from "../lib/constants";

const fcParams = fcParamsFor("TRANSACT");

// Balanced-split edge cases seeded into every fc.assert.
// Note: MAX_VALUE = 2^64 - 1 is odd, so 2 * (MAX_VALUE / 2n) = MAX_VALUE - 1.
// Each tuple must satisfy o1 + o2 === v1 + v2 (the circuit rejects otherwise).
const BALANCED_EXAMPLES = [
    { v1: 0n, v2: 0n, o1: 0n, o2: 0n },
    { v1: MAX_VALUE / 2n, v2: MAX_VALUE / 2n, o1: MAX_VALUE - 1n, o2: 0n },
    { v1: MAX_VALUE / 2n, v2: MAX_VALUE / 2n, o1: 0n, o2: MAX_VALUE - 1n },
];

describe("transact_4x6 [fuzz]", function () {
    this.timeout(TIMEOUT_HEAVY);

    const ctx = useTransactCircuit();

    it("balanced random 2-in-2-out same-asset always passes", async () => {
        await fc.assert(fc.asyncProperty(
            arbBalancedSplit(),
            arbNsk(), arbNsk(),
            // rhoA/rhoB always distinct via chained arbitrary (no .filter shrink penalty).
            arbDistinctBigInt(1n, 1n << 200n),
            arbField(1n << 200n), arbField(1n << 200n),
            async (split, aliceNsk, bobNsk, [rhoA, rhoB], rhoOA, rhoOB) => {
                await expectAccepts(ctx.circuit, ctx.tx.transfer(split, aliceNsk, bobNsk, [rhoA, rhoB, rhoOA, rhoOB]));
            },
        ), fcParamsFor("TRANSACT", { examples: BALANCED_EXAMPLES.map(s => [s, 11n, 22n, [1n, 2n] as [bigint, bigint], 3n, 4n]) }));
    });

    it("unbalanced random ctx.tx (output mutated by +delta) always fails", async () => {
        // Draws (v1, v2, o1, o2, delta) with delta > 0 and o2 + delta ≤ MAX_VALUE,
        // so the result is unbalanced and in range.
        const arbUnbalancedDelta = arbBalancedSplit().chain(({ v1, v2, o1, o2 }) => {
            const headroom = MAX_VALUE - o2;
            if (headroom === 0n) return fc.constant({ v1, v2, o1, o2, delta: 0n, skip: true });
            return fc.bigInt(1n, headroom).map(delta => ({ v1, v2, o1, o2, delta, skip: false }));
        });

        await fc.assert(fc.asyncProperty(
            arbUnbalancedDelta,
            arbNsk(), arbNsk(),
            async ({ v1, v2, o1, o2, delta, skip }, aliceNsk, bobNsk) => {
                if (skip) return; // o2 already saturated at MAX_VALUE; rare.
                const input = ctx.tx.transfer(
                    { v1, v2, o1, o2: o2 + delta }, aliceNsk, bobNsk,
                    [101n, 102n, 103n, 104n],
                );
                await expectWitnessFails(ctx.circuit, input, "expected unbalanced ctx.tx to fail");
            },
        ), fcParams);
    });

    it("wrong asset_id on an output (ghost note) always fails", async () => {
        // o1 ≥ 1 forces an observable asset mismatch (commit binds asset·2^64+value).
        // Built directly without .filter to keep shrinking efficient.
        const arbSplitO1Nonzero = fc.tuple(
            fc.bigInt(1n, MAX_VALUE / 2n - 1n),
            fc.bigInt(0n, MAX_VALUE / 2n),
            fc.bigInt(0n, 1n << 60n),
        ).map(([v1, v2, splitSeed]) => {
            const total = v1 + v2;
            const o1 = 1n + (splitSeed % total);
            return { v1, v2, o1, o2: total - o1 };
        });
        await fc.assert(fc.asyncProperty(
            arbSplitO1Nonzero,
            arbField(1n << 60n),
            async (split, badAssetSeed) => {
                const badAsset = ASSET + 1n + badAssetSeed;
                const { scenario, outputs } = ctx.tx.transferParts(split, ALICE_NSK, BOB_NSK);
                outputs[0] = { ...outputs[0], asset: badAsset };
                const input = ctx.tx.spend(scenario, outputs);
                await expectWitnessFails(ctx.circuit, input, "expected ghost-note ctx.tx to fail");
            },
        ), fcParams);
    });

    it("note commitment binds asset even at value=0", async () => {
        await fc.assert(fc.asyncProperty(
            // Distinct asset pair via chained arb; no post-hoc skip.
            arbDistinctBigInt(1n, 1n << 60n),
            arbField(1n << 200n), arbField(1n << 200n), arbField(1n << 200n),
            async ([assetA, assetB], pk, rho, rcm) => {
                const base = { value: 0n, pk, rho, rcm } as const;
                const cmA = commit(ctx.tx.P, { ...base, asset: assetA });
                const cmB = commit(ctx.tx.P, { ...base, asset: assetB });
                if (cmA === cmB) throw new Error("commitment collision across assets at value=0");
            },
        ), fcParams);
    });

    it("input value > 2^64 always fails (range check)", async () => {
        // Each run exercises the SDK and the circuit; the run count is scaled
        // down by default and overridable via FUZZ_RUNS_TRANSACT_OVERFLOW.
        await fc.assert(fc.asyncProperty(
            fc.bigInt(1n, 1n << 200n),
            async (overflowSeed) => {
                const overflow = MAX_VALUE + 1n + (overflowSeed % (1n << 64n));
                // Either the reference builder or the circuit range check must reject.
                const split = { v1: overflow, v2: 0n, o1: overflow, o2: 0n };
                await expectThrows(
                    () => ctx.circuit.calculateWitness(ctx.tx.transfer(split, ALICE_NSK, ALICE_NSK), true),
                    "expected overflow value to fail (SDK or ctx.circuit)",
                );
            },
        ), fcParamsFor("TRANSACT_OVERFLOW"));
    });

    it("wrong nsk (not the owner) always fails nullifier/key checks", async () => {
        await fc.assert(fc.asyncProperty(
            arbBalancedSplit(),
            // wrongNsk distinct from the owner's.
            arbNsk().map(n => n === ALICE_NSK ? n + 1n : n),
            async (split, wrongNsk) => {
                const { scenario, outputs } = ctx.tx.transferParts(split, ALICE_NSK, BOB_NSK);
                scenario.inputs[0] = { ...scenario.inputs[0], nsk: wrongNsk };
                const input = ctx.tx.spend(scenario, outputs);
                await expectWitnessFails(ctx.circuit, input, "expected wrong-nsk ctx.tx to fail");
            },
        ), fcParams);
    });
});
