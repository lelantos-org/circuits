// Fuzz coverage for the H-1 frontier-binding fix at DEPTH=10 / MAX_N=8.
//
// `lib/frontier_root.circom` rebinds `frontier_in` to public `old_root` so a
// malicious relayer cannot pair a real `oldRoot` with a forged frontier.
// The existing `frontier_root.test.ts` only exercises a depth-3 wrapper plus a
// handful of canned indices. This file drives the FULL `tree_update_batch`
// circuit at the production depth across random:
//   - edge-digit `start_index` patterns (digits ∈ {0, 3}, i.e. minimal /
//     maximal slot fill at each of the 10 levels);
//   - active-pair counts `k ∈ [1, MAX_N]` (so every padding shape — none,
//     partial, full — is fuzzed alongside the frontier rebuild);
//   - tamper coordinates `(level, slot)` over the filled siblings.
//
// Property: any perturbation of a filled frontier slot must reject the
// witness. The same SNARK is the one whose proof the contract layer
// (`MASP._verifyProofs`) consumes; if the circuit rejects, the on-chain
// `verifyProof` call also rejects ⇒ tampered batches cannot corrupt the
// authoritative root.
//
// SLOW: each fast-check trial builds two depth-10 batch witnesses. The
// suite respects the shared `FUZZ` env (`light` / `medium` / `heavy`).

import * as fc from "fast-check";

import { Poseidon, Jubjub, MerkleTree, type Field, type Point } from "../helpers";
import { fiatShamirZ, hornerEval } from "@lelantos-org/sdk";
import { loadCircuit, srcPath } from "../lib/circuit";
import { treeUpdateBatchInputJson, flattenTreeUpdateBatch } from "../lib/inputs";
import { expectWitnessFails } from "../lib/expect";
import { fcParamsFor } from "./arbitraries";

const DEPTH = 10;
const MAX_N = 8;
const SLOTS = 2 * MAX_N;
const TAG_LEAF = 10n;
const CAPACITY = 4 ** DEPTH;
const WRAPPER = srcPath("tree_update_batch.circom");

// Suite-tuned run count. `FRONTIER` scale defaults to 0.5x NUM_RUNS in
// arbitraries.ts; override via `FUZZ_RUNS_FRONTIER=N`. Suite is the slowest
// in the tree because each trial builds two depth-10 witnesses.
const fcParams = fcParamsFor("FRONTIER");

interface Pair {
    cm0: Field;
    cm1: Field;
    cvDep0: Point;
    cvDep1: Point;
    pairAsset: Field;
    pairPublicIn: Field;
    isDeposit: 0 | 1;
    rcvTotal: Field;
    rcvDepPad: Field;
}

function padToSlots<T>(real: T[], total: number, zero: T): T[] {
    const out = real.slice();
    while (out.length < total) out.push(zero);
    return out;
}

function buildPair(P: Poseidon, J: Jubjub, seed: number, isDeposit: 0 | 1): Pair {
    const asset = 7n;
    const val0 = BigInt(100 + seed);
    // Deposit pads must carry value 0: tree_update_batch pins cv_dep1 to
    // rcv_dep_pad·H so the pair total cannot be split between the leaves.
    const val1 = isDeposit === 1 ? 0n : BigInt(200 + seed);
    const pk = BigInt(0xb000 + seed);
    const rho0 = BigInt(1 + 4 * seed);
    const rho1 = BigInt(2 + 4 * seed);
    const rcm0 = BigInt(3 + 4 * seed);
    const rcm1 = BigInt(4 + 4 * seed);
    const rcvDep0 = BigInt(11 + 7 * seed);
    const rcvDep1 = BigInt(13 + 7 * seed);
    const cm0 = P.hash([asset * (1n << 64n) + val0, pk, rho0, rcm0]);
    const cm1 = P.hash([asset * (1n << 64n) + val1, pk, rho1, rcm1]);
    const assetGen = J.hashToAssetGen(asset);
    const cvDep0 = J.valueCommit(val0, assetGen, rcvDep0);
    const cvDep1 = J.valueCommit(val1, assetGen, rcvDep1);
    const pairPublicIn = isDeposit === 1 ? val0 + val1 : 0n;
    const pairAsset = isDeposit === 1 ? asset : 0n;
    const rcvTotal = isDeposit === 1 ? rcvDep0 + rcvDep1 : 0n;
    const rcvDepPad = isDeposit === 1 ? rcvDep1 : 0n;
    return { cm0, cm1, cvDep0, cvDep1, pairAsset, pairPublicIn, isDeposit, rcvTotal, rcvDepPad };
}

function leafOf(P: Poseidon, cm: Field, cvDep: Point): Field {
    return P.hash([TAG_LEAF, cm, cvDep[0], cvDep[1]]);
}

interface Witness {
    oldRoot: Field;
    newRoot: Field;
    startIndex: number;
    actualCount: number;
    cms: Field[];
    cvDep: Point[];
    pairAsset: Field[];
    pairPublicIn: Field[];
    isDeposit: number[];
    rcvTotal: Field[];
    rcvDepPad: Field[];
    frontier: Field[][];
    z: Field;
    y: Field;
}

function buildHonest(P: Poseidon, J: Jubjub, prefilled: number, pairs: Pair[]): Witness {
    const tree = new MerkleTree(P, DEPTH);
    for (let i = 0; i < prefilled; i++) tree.insert(BigInt(0xdead + i));
    const oldRoot = tree.root();
    const frontier = tree.frontier();

    for (const p of pairs) {
        tree.insert(leafOf(P, p.cm0, p.cvDep0));
        tree.insert(leafOf(P, p.cm1, p.cvDep1));
    }
    const newRoot = tree.root();

    const cms: Field[] = [];
    const cvDep: Point[] = [];
    for (const p of pairs) {
        cms.push(p.cm0);
        cms.push(p.cm1);
        cvDep.push(p.cvDep0);
        cvDep.push(p.cvDep1);
    }
    const cmsPadded = padToSlots(cms, SLOTS, 0n);
    const cvDepPadded = padToSlots(cvDep, SLOTS, [0n, 0n] as Point);
    const pairAssetPadded = padToSlots(pairs.map(p => p.pairAsset), MAX_N, 0n);
    const pairPublicInPadded = padToSlots(pairs.map(p => p.pairPublicIn), MAX_N, 0n);
    const isDepositPadded = padToSlots(pairs.map(p => p.isDeposit as number), MAX_N, 0);
    const rcvTotalPadded = padToSlots(pairs.map(p => p.rcvTotal), MAX_N, 0n);
    const rcvDepPadPadded = padToSlots(pairs.map(p => p.rcvDepPad), MAX_N, 0n);

    const coeffs = flattenTreeUpdateBatch({
        oldRoot,
        newRoot,
        startIndex: prefilled,
        actualCount: pairs.length,
        cms: cmsPadded,
        cvDep: cvDepPadded,
        pairAsset: pairAssetPadded,
        pairPublicIn: pairPublicInPadded,
        isDeposit: isDepositPadded,
    });
    const z = fiatShamirZ(coeffs);
    const y = hornerEval(coeffs, z);

    return {
        oldRoot,
        newRoot,
        startIndex: prefilled,
        actualCount: pairs.length,
        cms: cmsPadded,
        cvDep: cvDepPadded,
        pairAsset: pairAssetPadded,
        pairPublicIn: pairPublicInPadded,
        isDeposit: isDepositPadded,
        rcvTotal: rcvTotalPadded,
        rcvDepPad: rcvDepPadPadded,
        frontier,
        z,
        y,
    };
}

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

describe("frontier_root [fuzz, depth=10, MAX_N=8]", function () {
    this.timeout(3_600_000);

    let circuit: any;
    let P: Poseidon;
    let J: Jubjub;

    before(async () => {
        P = await Poseidon.build();
        J = await Jubjub.build();
        circuit = await loadCircuit(WRAPPER);
    });

    it("any filled-frontier perturbation rejects (random {0,3}-digit start_index, 1..8 pairs)", async () => {
        // Compose digits + k together so 2·k always fits remaining capacity
        // (drops the old `if (startIndex + 2*k > CAPACITY) return;` skip).
        // We also require at least one digit==3 so `tamperableLevels` is
        // non-empty; if the random draw gives all-zero digits we clear the
        // top level to 3 (still a valid edge-digit pattern).
        const arbDigitsK = fc.array(fc.constantFrom(0, 3), { minLength: DEPTH, maxLength: DEPTH })
            .chain(rawDigits => {
                const digits = rawDigits.some(d => d === 3) ? rawDigits : (() => {
                    const d = [...rawDigits];
                    d[DEPTH - 1] = 3;
                    return d;
                })();
                const startIndex = startIndexFromEdgeDigits(digits);
                const headroom = Math.max(1, Math.min(MAX_N, Math.floor((CAPACITY - startIndex) / 2)));
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
            // isDeposit per active pair (Pedersen aggregate path vs spend skip).
            fc.array(fc.constantFrom<0 | 1>(0, 1), { minLength: MAX_N, maxLength: MAX_N }),
            async ({ digits, k, level }, slotIdx, depositFlags) => {
                const startIndex = startIndexFromEdgeDigits(digits);

                const pairs: Pair[] = [];
                for (let i = 0; i < k; i++) {
                    pairs.push(buildPair(P, J, i, depositFlags[i]));
                }
                const honest = buildHonest(P, J, startIndex, pairs);

                // Sanity: honest witness must verify. Without this, a
                // tamper-rejection assertion below would be vacuous.
                const wHonest = await circuit.calculateWitness(treeUpdateBatchInputJson(honest), true);
                await circuit.checkConstraints(wHonest);

                // At digit==3 every slot 0..2 holds a real filled sibling
                // (MerkleTree.frontier zeros only `k >= currentSlot`).
                // Bump by 1 — still inside the BN254 scalar field since
                // Poseidon outputs are bounded well below R/2.
                const tampered: Witness = {
                    ...honest,
                    frontier: honest.frontier.map(lvl => lvl.slice()),
                };
                tampered.frontier[level][slotIdx] = tampered.frontier[level][slotIdx] + 1n;

                // Rebind Fiat-Shamir (frontier is NOT in the PolyEval
                // coefficient vector — see `flattenTreeUpdateBatch`) so the
                // failure can only come from FrontierRoot's `old_root ===
                // rebuilt` check, not from a (z, y) mismatch.
                await expectWitnessFails(
                    () => circuit.calculateWitness(treeUpdateBatchInputJson(tampered), true),
                    `frontier perturbation at (level=${level}, slot=${slotIdx}) must reject`,
                );
            },
        ), fcParamsFor("FRONTIER", { examples: [
            // Boundary digit patterns + tamper at extremes.
            [{ digits: Array<number>(DEPTH).fill(3).map((_, i) => i === DEPTH - 1 ? 0 : 3), k: 1, level: 0 }, 0, Array<0 | 1>(MAX_N).fill(1)],
            [{ digits: [...Array<number>(DEPTH - 1).fill(0), 3], k: 1, level: DEPTH - 1 }, 2, Array<0 | 1>(MAX_N).fill(0)],
        ] }));
    });
});
