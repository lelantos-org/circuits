// Fuzz coverage for frontier binding at production depth.
//
// `BatchAppend` (`lib/batch_append.circom`) rebuilds `old_root` from
// `frontier_in`, so a relayer cannot pair a real `oldRoot` with a forged
// frontier. This file drives the full `tree_update_batch` circuit at the
// production DEPTH over random:
//   - edge-digit `start_index` patterns (digits ∈ {0, 3}: minimal or maximal
//     slot fill at each level);
//   - active-leaf counts k ∈ [1, MAX_L], so every padding shape is covered;
//   - tamper coordinates (level, slot) over the filled siblings.
//
// Property: any perturbation of a filled frontier slot rejects the witness.
//
// The prefilled tree reaches ~4^DEPTH leaves, so `buildHonest` uses
// `MerkleTree.fillBlocks` to build it from a few hash chains.

import * as fc from "fast-check";

import { treeUpdateBatchInputJson } from "../lib/inputs";
import { expectAccepts } from "../lib/expect";
import type { BatchWitness } from "../lib/batch";
import { DEPTH, MAX_L, TIMEOUT_HEAVY } from "../lib/constants";
import { fcParamsFor } from "./arbitraries";
import { CAPACITY, expectBatchRejects, useBatchCircuit } from "../batch/setup";

/// The `start_index` with the given quaternary digits. At most 4^DEPTH - 1, so
/// it fits the circuit's Num2Bits(2·DEPTH).
function startIndexFromEdgeDigits(digits: number[]): number {
    let n = 0;
    for (let lvl = digits.length - 1; lvl >= 0; lvl--) n = n * 4 + digits[lvl];
    return n;
}

/// Levels where start_index has digit 3: all three frontier slots there hold
/// filled siblings, so tampering any of them must perturb the rebuild.
function tamperableLevels(digits: number[]): number[] {
    const out: number[] = [];
    for (let lvl = 0; lvl < digits.length; lvl++) if (digits[lvl] === 3) out.push(lvl);
    return out;
}

describe(`frontier binding [fuzz, depth=${DEPTH}, MAX_L=${MAX_L}]`, function () {
    this.timeout(TIMEOUT_HEAVY);

    const ctx = useBatchCircuit();

    it(`any filled-frontier perturbation rejects (random {0,3}-digit start_index, 1..${MAX_L} leaves)`, async () => {
        // Digits and k are drawn together so k fits the remaining capacity. At
        // least one digit must be 3 for `tamperableLevels` to be non-empty, so
        // an all-zero draw has its top level set to 3.
        const arbDigitsK = fc.array(fc.constantFrom(0, 3), { minLength: DEPTH, maxLength: DEPTH })
            .chain(rawDigits => {
                const digits = rawDigits.some(d => d === 3) ? rawDigits : (() => {
                    const d = [...rawDigits];
                    d[DEPTH - 1] = 3;
                    return d;
                })();
                const startIndex = startIndexFromEdgeDigits(digits);
                // The circuit range-checks start_index + k only for active slots
                // (k < actual_count), so the batch fits when the last active
                // index stays inside the tree. An all-3 draw puts startIndex at
                // 4^DEPTH - 1, where the only legal count is 1.
                const headroom = Math.min(MAX_L, CAPACITY - startIndex);
                return fc.integer({ min: 1, max: headroom }).map(k => ({ digits, k }));
            });
        // Tamper level picked uniformly over the filled subset.
        const arbTamperLevel = arbDigitsK.chain(({ digits, k }) => {
            const tLevels = tamperableLevels(digits);
            return fc.constantFrom(...tLevels).map(level => ({ digits, k, level }));
        });

        await fc.assert(fc.asyncProperty(
            arbTamperLevel,
            // Which of the 3 filled slots at the chosen level to perturb.
            fc.integer({ min: 0, max: 2 }),
            // isDeposit per leaf. Every constraint is per-slot, so any
            // interleaving of deposit and spend leaves is satisfiable.
            fc.array(fc.constantFrom<0 | 1>(0, 1), { minLength: MAX_L, maxLength: MAX_L }),
            async ({ digits, k, level }, slotIdx, depositFlags) => {
                const startIndex = startIndexFromEdgeDigits(digits);

                const leaves = ctx.batch.seededMany(k, i => depositFlags[i]);
                const honest = ctx.batch.honest(startIndex, leaves);

                // The honest witness must verify, or the tamper-rejection
                // assertion below is vacuous.
                await expectAccepts(ctx.circuit, treeUpdateBatchInputJson(honest));

                const tampered: BatchWitness = {
                    ...honest,
                    frontier: honest.frontier.map(lvl => lvl.slice()),
                };
                tampered.frontier[level][slotIdx] = tampered.frontier[level][slotIdx] + 1n;

                // No Fiat-Shamir rebind: the frontier is private, so it is in
                // neither the challenge preimage nor the evaluated prefix, and
                // the only possible failure is `old_root === append.old_root`.
                await expectBatchRejects(
                    ctx.circuit,
                    tampered,
                    `frontier perturbation at (level=${level}, slot=${slotIdx}) must reject`,
                );
            },
        ), fcParamsFor("FRONTIER", { examples: [
            // Boundary digit patterns with tampers at the extremes. Each example
            // must match the shape of the arbitraries above.
            [{ digits: Array<number>(DEPTH).fill(3).map((_, i) => i === DEPTH - 1 ? 0 : 3), k: 1, level: 0 }, 0, Array<0 | 1>(MAX_L).fill(1)],
            [{ digits: [...Array<number>(DEPTH - 1).fill(0), 3], k: 3, level: DEPTH - 1 }, 2, Array<0 | 1>(MAX_L).fill(0)],
        ] }));
    });
});
