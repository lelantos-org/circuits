import { expect } from "chai";
import * as path from "path";
// @ts-ignore
import { wasm as wasmTester } from "circom_tester";

import { Poseidon, MerkleTree, Field } from "./helpers";

const TAG_MERKLE: Field = 5n;
const ARITY = 4;
const DEPTH = 2; // 16 leaves
const WRAPPER = path.join(__dirname, "fixtures", "test_merkle_d2.circom");

describe("quaternary merkle tree", function () {
    this.timeout(180000);

    let circuit: any;
    let P: Poseidon;

    before(async () => {
        P = await Poseidon.build();
        circuit = await wasmTester(WRAPPER, {
            include: [path.join(__dirname, "..", "..", "node_modules")],
        });
    });

    function buildInput(leaf: Field, pathElements: Field[][], pathIndices: number[]) {
        return {
            leaf: leaf.toString(),
            path_elements: pathElements.map(lvl => lvl.map(s => s.toString())),
            path_indices: pathIndices.map(p => p.toString()),
        };
    }

    it("empty tree root matches manual zero-subtree fold", async () => {
        const tree = new MerkleTree(P, DEPTH);
        // Manually compute: level1 nodes all = Poseidon(5,0,0,0,0); root = Poseidon(5, n,n,n,n)
        const lvl1 = P.hash([TAG_MERKLE, 0n, 0n, 0n, 0n]);
        const expected = P.hash([TAG_MERKLE, lvl1, lvl1, lvl1, lvl1]);
        expect(tree.root()).to.equal(expected);
    });

    it("single-leaf root matches direct Poseidon evaluation", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const leaf = 0xabcdn;
        tree.insert(leaf);
        // Leaf at index 0 → bottom group = (leaf, 0, 0, 0); other 3 bottom groups all-zero.
        const bottom0 = P.hash([TAG_MERKLE, leaf, 0n, 0n, 0n]);
        const bottomZ = P.hash([TAG_MERKLE, 0n, 0n, 0n, 0n]);
        const expected = P.hash([TAG_MERKLE, bottom0, bottomZ, bottomZ, bottomZ]);
        expect(tree.root()).to.equal(expected);
    });

    it("circuit-computed root equals tree.root() at every quaternary slot (all 16 leaves)", async () => {
        // Insert 16 distinct leaves so every position in the depth-2 tree is exercised.
        const tree = new MerkleTree(P, DEPTH);
        const leaves: Field[] = [];
        for (let i = 0; i < 16; i++) {
            const leaf = BigInt(0x100 + i);
            leaves.push(leaf);
            tree.insert(leaf);
        }
        const expectedRoot = tree.root();

        for (let i = 0; i < 16; i++) {
            const { pathElements, pathIndices } = tree.proof(i);
            // Sanity: pathIndices encode (i % 4, (i/4) % 4)
            expect(pathIndices[0]).to.equal(i % ARITY);
            expect(pathIndices[1]).to.equal(Math.floor(i / ARITY) % ARITY);

            const w = await circuit.calculateWitness(buildInput(leaves[i], pathElements, pathIndices), true);
            await circuit.checkConstraints(w);
            await circuit.assertOut(w, { root: expectedRoot.toString() });
        }
    });

    it("MerkleLevel4 places `cur` at every path_index slot correctly", async () => {
        // Single-level check via depth-2 wrapper: pin the second level so we can
        // isolate level-0 placement behaviour. Use distinct sibling values to
        // detect any off-by-one in the slot-routing logic.
        const leaf = 42n;
        const sibs0: Field[] = [111n, 222n, 333n];
        // Level 1 fully arbitrary — just need a deterministic value.
        const lvl1Sibs: Field[] = [1n, 2n, 3n];
        const lvl1Idx = 2;

        for (let pos = 0; pos < ARITY; pos++) {
            // Reconstruct expected level-0 grouping based on `pos`.
            const group: Field[] = [];
            let s = 0;
            for (let k = 0; k < ARITY; k++) {
                if (k === pos) group.push(leaf);
                else group.push(sibs0[s++]);
            }
            const lvl0Out = P.hash([TAG_MERKLE, group[0], group[1], group[2], group[3]]);
            // Level 1 places lvl0Out at slot lvl1Idx
            const grp1: Field[] = [];
            let t = 0;
            for (let k = 0; k < ARITY; k++) {
                if (k === lvl1Idx) grp1.push(lvl0Out);
                else grp1.push(lvl1Sibs[t++]);
            }
            const expectedRoot = P.hash([TAG_MERKLE, grp1[0], grp1[1], grp1[2], grp1[3]]);

            const w = await circuit.calculateWitness(
                buildInput(leaf, [sibs0, lvl1Sibs], [pos, lvl1Idx]),
                true,
            );
            await circuit.assertOut(w, { root: expectedRoot.toString() });
        }
    });

    it("FAILS when path_index >= 4 (Num2Bits(2) range check)", async () => {
        const tree = new MerkleTree(P, DEPTH);
        tree.insert(7n);
        const { pathElements, pathIndices } = tree.proof(0);
        pathIndices[0] = 4; // out of {0,1,2,3}
        let threw = false;
        try { await circuit.calculateWitness(buildInput(7n, pathElements, pathIndices), true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("FAILS when path_index is large garbage (e.g. 2^32)", async () => {
        const tree = new MerkleTree(P, DEPTH);
        tree.insert(7n);
        const { pathElements, pathIndices } = tree.proof(0);
        pathIndices[1] = 1 << 30;
        let threw = false;
        try { await circuit.calculateWitness(buildInput(7n, pathElements, pathIndices), true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("permuting siblings within a level changes the root (order matters)", async () => {
        const tree = new MerkleTree(P, DEPTH);
        for (let i = 0; i < 5; i++) tree.insert(BigInt(0x900 + i));
        const expected = tree.root();

        // Index 1 has selfPos=1 at level 0. Sibling slots at level 0 are {0,2,3}
        // → siblings array order is [slot0, slot2, slot3]. Swapping siblings[0]
        // and siblings[2] reorders slot0 ↔ slot3, must produce a different root.
        const { pathElements, pathIndices } = tree.proof(1);
        const swapped: Field[][] = pathElements.map(lvl => lvl.slice());
        [swapped[0][0], swapped[0][2]] = [swapped[0][2], swapped[0][0]];

        const w = await circuit.calculateWitness(buildInput(tree.leaves[1], swapped, pathIndices), true);
        const out: any = {};
        try {
            await circuit.assertOut(w, { root: expected.toString() });
            out.equal = true;
        } catch {
            out.equal = false;
        }
        expect(out.equal).to.equal(false);
    });

    it("dummy zeros[i] cache equals iterated Poseidon(5, z,z,z,z)", async () => {
        // Sanity: validates the zero-subtree precomputation in MerkleTree.
        let z: Field = 0n;
        const tree = new MerkleTree(P, DEPTH);
        const zeros = (tree as unknown as { zeros: Field[] }).zeros;
        for (let i = 0; i < DEPTH; i++) {
            expect(zeros[i]).to.equal(z);
            z = P.hash([TAG_MERKLE, z, z, z, z]);
        }
        expect(zeros[DEPTH]).to.equal(z);
    });
});
