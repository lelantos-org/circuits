import { expect } from "chai";
import * as fc from "fast-check";

import { Poseidon, MerkleTree, Field } from "../helpers";
import { fixturePath, loadCircuit } from "../lib/circuit";
import { merkleInputJson } from "../lib/inputs";
import { expectWitnessFails, witnessMatchesRoot } from "../lib/expect";
import { fcParams, arbField } from "./arbitraries";

const DEPTH = 2;
const ARITY = 4;
const N_LEAVES = ARITY ** DEPTH;
const WRAPPER = fixturePath("test_merkle_d2.circom");

describe("quaternary merkle [fuzz]", function () {
    this.timeout(900000);

    let circuit: any;
    let P: Poseidon;

    before(async () => {
        P = await Poseidon.build();
        circuit = await loadCircuit(WRAPPER);
    });

    it("insert+proof round-trip verifies for any leaf set and any index", async () => {
        await fc.assert(fc.asyncProperty(
            fc.array(arbField(1n << 200n), { minLength: N_LEAVES, maxLength: N_LEAVES }),
            fc.integer({ min: 0, max: N_LEAVES - 1 }),
            async (leaves, queryIdx) => {
                const tree = new MerkleTree(P, DEPTH);
                for (const l of leaves) tree.insert(l);
                const expected = tree.root();
                const { pathElements, pathIndices } = tree.proof(queryIdx);

                const w = await circuit.calculateWitness(
                    merkleInputJson(leaves[queryIdx], pathElements, pathIndices), true,
                );
                await circuit.checkConstraints(w);
                await circuit.assertOut(w, { root: expected.toString() });
            },
        ), fcParams);
    });

    it("permuting any two siblings within a level changes the root", async () => {
        await fc.assert(fc.asyncProperty(
            fc.array(arbField(1n << 200n), { minLength: N_LEAVES, maxLength: N_LEAVES }),
            fc.integer({ min: 0, max: N_LEAVES - 1 }),
            fc.integer({ min: 0, max: DEPTH - 1 }),
            fc.integer({ min: 0, max: ARITY - 3 }),
            async (leaves, queryIdx, swapLevel, swapA) => {
                const tree = new MerkleTree(P, DEPTH);
                for (const l of leaves) tree.insert(l);
                const { pathElements, pathIndices } = tree.proof(queryIdx);

                const swapped: Field[][] = pathElements.map(lvl => lvl.slice());
                const a = swapA;
                const b = swapA + 1;
                if (swapped[swapLevel][a] === swapped[swapLevel][b]) return; // no-op swap
                [swapped[swapLevel][a], swapped[swapLevel][b]] = [swapped[swapLevel][b], swapped[swapLevel][a]];

                const w = await circuit.calculateWitness(
                    merkleInputJson(leaves[queryIdx], swapped, pathIndices), true,
                );
                expect(await witnessMatchesRoot(circuit, w, tree.root())).to.equal(false);
            },
        ), fcParams);
    });

    it("path_index >= 4 always fails Num2Bits(2) range check", async () => {
        await fc.assert(fc.asyncProperty(
            fc.integer({ min: 0, max: N_LEAVES - 1 }),
            fc.integer({ min: 0, max: DEPTH - 1 }),
            fc.integer({ min: 4, max: 1 << 20 }),
            async (queryIdx, level, badIdx) => {
                const tree = new MerkleTree(P, DEPTH);
                for (let i = 0; i < N_LEAVES; i++) tree.insert(BigInt(0x100 + i));
                const { pathElements, pathIndices } = tree.proof(queryIdx);
                pathIndices[level] = badIdx;
                await expectWitnessFails(
                    circuit,
                    merkleInputJson(tree.leaves[queryIdx], pathElements, pathIndices),
                    "expected out-of-range path_index to fail",
                );
            },
        ), fcParams);
    });
});
