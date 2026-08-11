// Fuzz coverage for the H-1 frontier-binding fix at DEPTH=10 / MAX_L=8.
//
// `lib/frontier_root.circom` rebinds `frontier_in` to public `old_root` so a
// malicious relayer cannot pair a real `oldRoot` with a forged frontier.
// The existing `frontier_root.test.ts` only exercises a depth-3 wrapper plus a
// handful of canned indices. This file drives the FULL `tree_update_batch`
// circuit at the production depth across random:
//   - edge-digit `start_index` patterns (digits ∈ {0, 3}, i.e. minimal /
//     maximal slot fill at each of the 10 levels);
//   - active-leaf counts `k ∈ [1, MAX_L]`, odd counts included (so every
//     padding shape — none, partial, full — is fuzzed alongside the rebuild);
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

import {
    Poseidon,
    Jubjub,
    MerkleTree,
    buildNoteCommitment,
    fiatShamirZ,
    hornerEval,
    type Field,
    type Point,
} from "../helpers";
import { loadCircuit, srcPath } from "../lib/circuit";
import { treeUpdateBatchInputJson, treeUpdateBatchCoeffs, padToSlots } from "../lib/inputs";
import { expectWitnessFails } from "../lib/expect";
import { fcParamsFor } from "./arbitraries";

const DEPTH = 10;
const MAX_L = 8;
const TAG_LEAF = 10n;
const CAPACITY = 4 ** DEPTH;
const WRAPPER = srcPath("tree_update_batch.circom");

// Suite-tuned run count. `FRONTIER` scale defaults to 0.5x NUM_RUNS in
// arbitraries.ts; override via `FUZZ_RUNS_FRONTIER=N`. Suite is the slowest
// in the tree because each trial builds two depth-10 witnesses.
const fcParams = fcParamsFor("FRONTIER");

interface Leaf {
    cm: Field;
    cvDep: Point;
    leafAsset: Field;
    leafPublicIn: Field;
    isDeposit: 0 | 1;
    rcv: Field;
}

function buildLeaf(P: Poseidon, J: Jubjub, seed: number, isDeposit: 0 | 1): Leaf {
    const asset = 7n;
    const val = BigInt(100 + seed);
    const pk = BigInt(0xb000 + seed);
    const rho = BigInt(1 + 2 * seed);
    const rcm = BigInt(3 + 2 * seed);
    const rcv = BigInt(11 + 7 * seed);
    const cm = buildNoteCommitment(P, { asset, value: val, pk, rho, rcm });
    const assetGen = J.hashToAssetGen(asset);
    const cvDep = J.valueCommit(val, assetGen, rcv);
    // A deposit leaf is pinned directly to its own value, so the claimed
    // public_in is exactly `val`.
    return {
        cm,
        cvDep,
        leafAsset: isDeposit === 1 ? asset : 0n,
        leafPublicIn: isDeposit === 1 ? val : 0n,
        isDeposit,
        rcv,
    };
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
    leafAsset: Field[];
    leafPublicIn: Field[];
    isDeposit: number[];
    rcv: Field[];
    frontier: Field[][];
    z: Field;
    y: Field;
}

function buildHonest(P: Poseidon, J: Jubjub, prefilled: number, leaves: Leaf[]): Witness {
    const tree = new MerkleTree(P, DEPTH);
    for (let i = 0; i < prefilled; i++) tree.insert(BigInt(0xdead + i));
    const oldRoot = tree.root();
    const frontier = tree.frontier();

    for (const l of leaves) {
        tree.insert(leafOf(P, l.cm, l.cvDep));
    }
    const newRoot = tree.root();

    const cmsPadded = padToSlots(leaves.map(l => l.cm), MAX_L, 0n);
    const cvDepPadded = padToSlots(leaves.map(l => l.cvDep), MAX_L, [0n, 0n] as Point);
    const leafAssetPadded = padToSlots(leaves.map(l => l.leafAsset), MAX_L, 0n);
    const leafPublicInPadded = padToSlots(leaves.map(l => l.leafPublicIn), MAX_L, 0n);
    const isDepositPadded = padToSlots(leaves.map(l => l.isDeposit as number), MAX_L, 0);
    const rcvPadded = padToSlots(leaves.map(l => l.rcv), MAX_L, 0n);

    const coeffs = treeUpdateBatchCoeffs({
        oldRoot,
        newRoot,
        startIndex: prefilled,
        actualCount: leaves.length,
        cms: cmsPadded,
        cvDep: cvDepPadded,
        leafAsset: leafAssetPadded,
        leafPublicIn: leafPublicInPadded,
        isDeposit: isDepositPadded,
    });
    const z = fiatShamirZ(coeffs);
    const y = hornerEval(coeffs, z);

    return {
        oldRoot,
        newRoot,
        startIndex: prefilled,
        actualCount: leaves.length,
        cms: cmsPadded,
        cvDep: cvDepPadded,
        leafAsset: leafAssetPadded,
        leafPublicIn: leafPublicInPadded,
        isDeposit: isDepositPadded,
        rcv: rcvPadded,
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

describe("frontier_root [fuzz, depth=10, MAX_L=8]", function () {
    this.timeout(3_600_000);

    let circuit: any;
    let P: Poseidon;
    let J: Jubjub;

    before(async () => {
        P = await Poseidon.build();
        J = await Jubjub.build();
        circuit = await loadCircuit(WRAPPER);
    });

    it("any filled-frontier perturbation rejects (random {0,3}-digit start_index, 1..8 leaves)", async () => {
        // Compose digits + k together so k always fits the remaining capacity,
        // avoiding a discard when the draw would overflow.
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

                const leaves: Leaf[] = [];
                for (let i = 0; i < k; i++) {
                    leaves.push(buildLeaf(P, J, i, depositFlags[i]));
                }
                const honest = buildHonest(P, J, startIndex, leaves);

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
                // coefficient vector — see `treeUpdateBatchCoeffs`) so the
                // failure can only come from FrontierRoot's `old_root ===
                // rebuilt` check, not from a (z, y) mismatch.
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
