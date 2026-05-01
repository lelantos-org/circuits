import * as fc from "fast-check";

import { Poseidon, MerkleTree, type Field } from "../helpers";
import { fiatShamirZ, hornerEval } from "@lelantos-org/sdk";
import { loadCircuit, srcPath } from "../lib/circuit";
import { treeUpdateInputJson } from "../lib/inputs";
import { expectWitnessFails } from "../lib/expect";
import { fcParams, arbField } from "./arbitraries";

const DEPTH = 10;
const ARITY = 4;
const MAX_LEAVES = ARITY ** DEPTH;
const WRAPPER = srcPath("tree_update.circom");

describe("tree_update [fuzz]", function () {
    this.timeout(900000);

    let circuit: any;
    let P: Poseidon;

    before(async () => {
        P = await Poseidon.build();
        circuit = await loadCircuit(WRAPPER);
    });

    it("random valid 2-leaf insertion always proves", async () => {
        await fc.assert(fc.asyncProperty(
            // Cap prefilled at a small range so insertion stays cheap; covers
            // boundary indices (0, parent crossings, mid-tree).
            fc.integer({ min: 0, max: 4096 }),
            arbField(1n << 200n), arbField(1n << 200n),
            async (prefilled, cm0, cm1) => {
                const tree = new MerkleTree(P, DEPTH);
                for (let i = 0; i < prefilled; i++) tree.insert(BigInt(0xdead + i));
                const oldRoot = tree.root();
                const frontier = tree.frontier();

                tree.insert(cm0);
                tree.insert(cm1);
                const newRoot = tree.root();

                const startIndex = prefilled;
                const coeffs: Field[] = [oldRoot, newRoot, cm0, cm1, BigInt(startIndex)];
                const z = fiatShamirZ(coeffs);
                const expectedY = hornerEval(coeffs, z);

                const w = await circuit.calculateWitness(
                    treeUpdateInputJson({ oldRoot, newRoot, cm0, cm1, startIndex, frontier, z }), true,
                );
                await circuit.checkConstraints(w);
                await circuit.assertOut(w, { y: expectedY.toString() });
            },
        ), { ...fcParams, numRuns: Math.min(fcParams.numRuns ?? 20, 10) });
    });

    it("wrong new_root always fails", async () => {
        await fc.assert(fc.asyncProperty(
            fc.integer({ min: 0, max: 256 }),
            arbField(1n << 200n), arbField(1n << 200n),
            arbField(1n << 200n),
            async (prefilled, cm0, cm1, rootMutator) => {
                const tree = new MerkleTree(P, DEPTH);
                for (let i = 0; i < prefilled; i++) tree.insert(BigInt(0xdead + i));
                const oldRoot = tree.root();
                const frontier = tree.frontier();

                tree.insert(cm0);
                tree.insert(cm1);
                const trueRoot = tree.root();
                const wrongRoot = trueRoot ^ (rootMutator | 1n);
                if (wrongRoot === trueRoot) return;

                const startIndex = prefilled;
                const coeffs: Field[] = [oldRoot, wrongRoot, cm0, cm1, BigInt(startIndex)];
                const z = fiatShamirZ(coeffs);
                await expectWitnessFails(
                    circuit,
                    treeUpdateInputJson({ oldRoot, newRoot: wrongRoot, cm0, cm1, startIndex, frontier, z }),
                    "expected wrong new_root to fail",
                );
            },
        ), fcParams);
    });

    it("start_index >= 4^DEPTH - 1 always fails", async () => {
        await fc.assert(fc.asyncProperty(
            fc.integer({ min: MAX_LEAVES - 1, max: MAX_LEAVES + 1024 }),
            arbField(1n << 60n), arbField(1n << 60n),
            async (startIndex, cm0, cm1) => {
                const tree = new MerkleTree(P, DEPTH);
                const oldRoot = tree.root();
                const frontier = tree.frontier();
                const coeffs: Field[] = [oldRoot, 0n, cm0, cm1, BigInt(startIndex)];
                const z = fiatShamirZ(coeffs);
                await expectWitnessFails(
                    circuit,
                    treeUpdateInputJson({ oldRoot, newRoot: 0n, cm0, cm1, startIndex, frontier, z }),
                    "expected oob start_index to fail",
                );
            },
        ), { ...fcParams, numRuns: Math.min(fcParams.numRuns ?? 20, 10) });
    });
});
