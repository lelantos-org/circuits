import * as fs from "fs";
import * as path from "path";
import { fileURLToPath } from "url";

import { expect } from "chai";

import { Poseidon, MerkleTree, TAG_MERKLE, Field } from "./helpers";
import { fixturePath, loadCircuit, type CircuitTester } from "./lib/circuit";
import { merkleInputJson } from "./lib/inputs";
import { expectWitnessFails, witnessMatchesRoot } from "./lib/expect";
import { ARITY, TIMEOUT_CIRCUIT, TIMEOUT_FAST } from "./lib/constants";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const DEPTH = 2; // 16 leaves
const WRAPPER = fixturePath("test_merkle_d2.circom");

describe("quaternary merkle tree", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    let circuit: CircuitTester;
    let P: Poseidon;

    before(async () => {
        P = await Poseidon.build();
        circuit = await loadCircuit(WRAPPER);
    });

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
            expect(pathIndices[0]).to.equal(i % ARITY);
            expect(pathIndices[1]).to.equal(Math.floor(i / ARITY) % ARITY);

            const w = await circuit.calculateWitness(merkleInputJson(leaves[i], pathElements, pathIndices), true);
            await circuit.checkConstraints(w);
            await circuit.assertOut(w, { root: expectedRoot.toString() });
        }
    });

    it("MerkleLevel4 places `cur` at every path_index slot correctly", async () => {
        // Single-level check via the depth-2 wrapper: pin the second level to
        // isolate level-0 placement behaviour. Use distinct sibling values to
        // detect any off-by-one in the slot-routing logic.
        const leaf = 42n;
        const sibs0: Field[] = [111n, 222n, 333n];
        const lvl1Sibs: Field[] = [1n, 2n, 3n];
        const lvl1Idx = 2;

        for (let pos = 0; pos < ARITY; pos++) {
            const group: Field[] = [];
            let s = 0;
            for (let k = 0; k < ARITY; k++) {
                if (k === pos) group.push(leaf);
                else group.push(sibs0[s++]);
            }
            const lvl0Out = P.hash([TAG_MERKLE, group[0], group[1], group[2], group[3]]);
            const grp1: Field[] = [];
            let t = 0;
            for (let k = 0; k < ARITY; k++) {
                if (k === lvl1Idx) grp1.push(lvl0Out);
                else grp1.push(lvl1Sibs[t++]);
            }
            const expectedRoot = P.hash([TAG_MERKLE, grp1[0], grp1[1], grp1[2], grp1[3]]);

            const w = await circuit.calculateWitness(
                merkleInputJson(leaf, [sibs0, lvl1Sibs], [pos, lvl1Idx]),
                true,
            );
            await circuit.assertOut(w, { root: expectedRoot.toString() });
        }
    });

    it("FAILS when path_index >= 4 (Num2Bits(2) range check)", async () => {
        const tree = new MerkleTree(P, DEPTH);
        tree.insert(7n);
        const { pathElements, pathIndices } = tree.proof(0);
        pathIndices[0] = 4;
        await expectWitnessFails(circuit, merkleInputJson(7n, pathElements, pathIndices));
    });

    it("FAILS when path_index is large garbage (e.g. 2^32)", async () => {
        const tree = new MerkleTree(P, DEPTH);
        tree.insert(7n);
        const { pathElements, pathIndices } = tree.proof(0);
        pathIndices[1] = 1 << 30;
        await expectWitnessFails(circuit, merkleInputJson(7n, pathElements, pathIndices));
    });

    it("permuting siblings within a level changes the root (order matters)", async () => {
        const tree = new MerkleTree(P, DEPTH);
        for (let i = 0; i < 5; i++) tree.insert(BigInt(0x900 + i));
        const expected = tree.root();

        // Index 1 has selfPos=1 at level 0. Sibling slots at level 0 are {0,2,3}
        // → siblings array order is [slot0, slot2, slot3]. Swapping siblings[0]
        // and siblings[2] reorders slot0 ↔ slot3, must produce a different root.
        const { pathElements, pathIndices } = tree.proof(1);
        const swapped: Field[][] = pathElements.map((lvl: Field[]) => lvl.slice());
        [swapped[0][0], swapped[0][2]] = [swapped[0][2], swapped[0][0]];

        const w = await circuit.calculateWitness(merkleInputJson(tree.leaves[1], swapped, pathIndices), true);
        expect(await witnessMatchesRoot(circuit, w, expected)).to.equal(false);
    });

    it("dummy zeros[i] cache equals iterated Poseidon(5, z,z,z,z)", async () => {
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

// EMPTY_SUBTREE(d) in lib/common.circom is a hardcoded table rather than an
// in-circuit Poseidon chain, since circom does not constant-fold Poseidon.
// These tests read the constants out of the circom source and recompute the
// chain, so a typo in the table fails CI rather than shifting every empty
// subtree.
describe("EMPTY_SUBTREE constant table (lib/common.circom)", function () {
    this.timeout(TIMEOUT_FAST);

    // Genesis root for DEPTH = 11, which CommitmentTree.EMPTY_ROOT must become.
    //
    // PENDING: the contract still carries the depth-10 root
    // (0x1308eb79d37ed29a9a2d34861692ea8c3e4fed3f555f53a8776c1256738e40a7) and
    // MAX_LEAVES = 4^10. Updating it in isolation would leave the pool with a
    // depth-11 tree behind a depth-10 verifier and a 4-output ABI, so it lands
    // with the rest of the contract work — the compress overload at 69 slots,
    // Output[6], MAX_L_BATCH = 8 and the regenerated verifiers.
    //
    // This constant is the value it must take. It is asserted against the
    // circuit's own table below, so the two cannot drift while they wait.
    const CONTRACT_EMPTY_ROOT =
        0x1cf92e62b512433b35f0064d537576b0184cad5fa7ab64201cd8084ee2dc171fn;
    const TABLE_DEPTH = 11;

    let table: Field[];
    let P2: Poseidon;

    before(async () => {
        P2 = await Poseidon.build();

        const src = fs.readFileSync(
            path.join(__dirname, "..", "src", "lib", "common.circom"),
            "utf8",
        );
        const body = src.slice(src.indexOf("function EMPTY_SUBTREE"));
        table = [];
        for (const m of body.matchAll(/^\s*z\[(\d+)\]\s*=\s*(\d+);/gm)) {
            table[Number(m[1])] = BigInt(m[2]);
        }
    });

    it("parses exactly DEPTH+1 entries from the circom source", () => {
        expect(table.length).to.equal(TABLE_DEPTH + 1);
        for (let d = 0; d <= TABLE_DEPTH; d++) {
            expect(table[d], `z[${d}] missing`).to.not.equal(undefined);
        }
    });

    it("every entry equals the iterated Poseidon(TAG_MERKLE, z,z,z,z) chain", () => {
        let z: Field = 0n;
        for (let d = 0; d <= TABLE_DEPTH; d++) {
            expect(table[d], `EMPTY_SUBTREE(${d})`).to.equal(z);
            z = P2.hash([TAG_MERKLE, z, z, z, z]);
        }
    });

    it("EMPTY_SUBTREE(TABLE_DEPTH) equals CommitmentTree.EMPTY_ROOT", () => {
        // The cross-repo pin: the circuit's empty-subtree chain and the
        // contract's genesis root are the same value reached two ways, so a
        // depth change touching only one side fails here rather than at a root
        // mismatch on the first insert.
        expect(table[TABLE_DEPTH]).to.equal(CONTRACT_EMPTY_ROOT);
    });
});
