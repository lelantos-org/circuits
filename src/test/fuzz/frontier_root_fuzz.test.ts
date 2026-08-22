// Fuzz coverage for frontier binding at production depth.
//
// `lib/frontier_root.circom` rebinds `frontier_in` to public `old_root`, so a
// relayer cannot pair a real `oldRoot` with a forged frontier.
// `frontier_root.test.ts` covers a depth-3 wrapper over canned indices; this
// file drives the full `tree_update_batch` circuit at DEPTH = 10 over random:
//   - edge-digit `start_index` patterns (digits ∈ {0, 3}: minimal or maximal
//     slot fill at each of the 10 levels);
//   - active-leaf counts k ∈ [1, MAX_L], odd counts included, so every padding
//     shape is covered alongside the rebuild;
//   - tamper coordinates (level, slot) over the filled siblings.
//
// Property: any perturbation of a filled frontier slot rejects the witness.
// The contract layer (`MASP._verifyProofs`) consumes a proof of this same
// circuit, so a rejection here means `verifyProof` also rejects and a tampered
// batch cannot corrupt the authoritative root.
//
// Slow: each fast-check trial builds two depth-10 batch witnesses. Run count
// follows the shared `FUZZ` env (`light` / `medium` / `heavy`).

import * as fc from "fast-check";

import { Jubjub, Poseidon } from "../helpers";
import { loadCircuit, srcPath, type CircuitTester } from "../lib/circuit";
import { treeUpdateBatchInputJson } from "../lib/inputs";
import { expectAccepts, expectWitnessFails } from "../lib/expect";
import { buildHonest, seededLeaf, type BatchWitness, type LeafWitness } from "../lib/batch";
import { DEPTH, MAX_L, TIMEOUT_HEAVY } from "../lib/constants";
import { fcParamsFor } from "./arbitraries";

const CAPACITY = 4 ** DEPTH;
const WRAPPER = srcPath("tree_update_batch.circom");

// Run count comes from `fcParamsFor("FRONTIER")` at the call site below.
// `FRONTIER` scales to 0.5x NUM_RUNS in arbitraries.ts; override with
// `FUZZ_RUNS_FRONTIER=N`.

/// Compose a `start_index` whose quaternary digits at every level are
/// in {0, 3} — the "edge" slot positions at each tree level. Returns the
/// integer; bits length is 2·DEPTH = 20 (Num2Bits-safe).
function startIndexFromEdgeDigits(digits: number[]): number {
    let n = 0;
    for (let lvl = digits.length - 1; lvl >= 0; lvl--) n = n * 4 + digits[lvl];
    return n;
}

/// Levels where the start_index has digit == 3 (i.e. all 3 frontier slots
/// at that level hold real filled siblings, so tampering any of them must
/// perturb the rebuild).
function tamperableLevels(digits: number[]): number[] {
    const out: number[] = [];
    for (let lvl = 0; lvl < digits.length; lvl++) if (digits[lvl] === 3) out.push(lvl);
    return out;
}

describe(`frontier_root [fuzz, depth=${DEPTH}, MAX_L=${MAX_L}]`, function () {
    this.timeout(TIMEOUT_HEAVY);

    let circuit: CircuitTester;
    let P: Poseidon;
    let J: Jubjub;

    before(async () => {
        P = await Poseidon.build();
        J = await Jubjub.build();
        circuit = await loadCircuit(WRAPPER);
    });

    it(`any filled-frontier perturbation rejects (random {0,3}-digit start_index, 1..${MAX_L} leaves)`, async () => {
        // Compose digits and k together so k always fits the remaining capacity,
        // avoiding a discard when the draw would overflow. At least one digit
        // must be 3 for `tamperableLevels` to be non-empty; an all-zero draw has
        // its top level set to 3, still a valid edge-digit pattern.
        const arbDigitsK = fc.array(fc.constantFrom(0, 3), { minLength: DEPTH, maxLength: DEPTH })
            .chain(rawDigits => {
                const digits = rawDigits.some(d => d === 3) ? rawDigits : (() => {
                    const d = [...rawDigits];
                    d[DEPTH - 1] = 3;
                    return d;
                })();
                const startIndex = startIndexFromEdgeDigits(digits);
                const headroom = Math.max(1, Math.min(MAX_L, CAPACITY - startIndex));
                return fc.integer({ min: 1, max: headroom }).map(k => ({ digits, k }));
            });
        // Tamper level picked uniformly over the filled subset (no levelSeed
        // bias from the previous `levelSeed % tLevels.length` mod).
        const arbTamperLevel = arbDigitsK.chain(({ digits, k }) => {
            const tLevels = tamperableLevels(digits);
            return fc.constantFrom(...tLevels).map(level => ({ digits, k, level }));
        });

        await fc.assert(fc.asyncProperty(
            arbTamperLevel,
            // Which of the 3 filled slots at the chosen level to perturb.
            fc.integer({ min: 0, max: 2 }),
            // isDeposit per active leaf (Pedersen binding path vs spend skip).
            fc.array(fc.constantFrom<0 | 1>(0, 1), { minLength: MAX_L, maxLength: MAX_L }),
            async ({ digits, k, level }, slotIdx, depositFlags) => {
                const startIndex = startIndexFromEdgeDigits(digits);

                const leaves: LeafWitness[] = [];
                for (let i = 0; i < k; i++) {
                    leaves.push(seededLeaf(P, J, i, depositFlags[i]));
                }
                const honest = buildHonest(P, J, startIndex, leaves);

                // Sanity: honest witness must verify. Without this, a
                // tamper-rejection assertion below would be vacuous.
                await expectAccepts(circuit, treeUpdateBatchInputJson(honest));

                // At digit == 3 every slot 0..2 holds a filled sibling
                // (MerkleTree.frontier zeros only `k >= currentSlot`). A bump of
                // 1 stays inside BN254 Fr, since Poseidon outputs are bounded
                // well below R/2.
                const tampered: BatchWitness = {
                    ...honest,
                    frontier: honest.frontier.map(lvl => lvl.slice()),
                };
                tampered.frontier[level][slotIdx] = tampered.frontier[level][slotIdx] + 1n;

                // No Fiat-Shamir rebind: the frontier is not in the PolyEval
                // coefficient vector (see `treeUpdateBatchCoeffs`), so the only
                // possible failure is FrontierRoot's `old_root === rebuilt`
                // check rather than a (z, y) mismatch.
                await expectWitnessFails(
                    circuit,
                    treeUpdateBatchInputJson(tampered),
                    `frontier perturbation at (level=${level}, slot=${slotIdx}) must reject`,
                );
            },
        ), fcParamsFor("FRONTIER", { examples: [
            // Boundary digit patterns + tamper at extremes.
            [{ digits: Array<number>(DEPTH).fill(3).map((_, i) => i === DEPTH - 1 ? 0 : 3), k: 1, level: 0 }, 0, Array<0 | 1>(MAX_L).fill(1)],
            [{ digits: [...Array<number>(DEPTH - 1).fill(0), 3], k: 3, level: DEPTH - 1 }, 2, Array<0 | 1>(MAX_L).fill(0)],
        ] }));
    });
});
