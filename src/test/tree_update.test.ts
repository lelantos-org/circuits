import { expect } from "chai";
import * as path from "path";
// @ts-ignore
import { wasm as wasmTester } from "circom_tester";

import { Poseidon, MerkleTree, type Field } from "./helpers";
import { fiatShamirZ, hornerEval } from "../../../sdk/src/snark-compression";

const DEPTH = 10;
const ARITY = 4;
const WRAPPER = path.join(__dirname, "..", "tree_update.circom");

interface BuildArgs {
    oldRoot: Field;
    newRoot: Field;
    cm0: Field;
    cm1: Field;
    startIndex: number;
    frontier: Field[][];
    z: Field;
}

function buildInput(a: BuildArgs) {
    return {
        z: a.z.toString(),
        old_root: a.oldRoot.toString(),
        new_root: a.newRoot.toString(),
        cm0: a.cm0.toString(),
        cm1: a.cm1.toString(),
        start_index: a.startIndex.toString(),
        frontier_in: a.frontier.map(lvl => lvl.map(s => s.toString())),
    };
}

describe("tree_update circuit", function () {
    this.timeout(180000);

    let circuit: any;
    let P: Poseidon;

    before(async () => {
        P = await Poseidon.build();
        circuit = await wasmTester(WRAPPER, {
            include: [path.join(__dirname, "..", "..", "node_modules")],
        });
    });

    function setupAt(prefilled: number): { tree: MerkleTree; oldRoot: Field; frontier: Field[][]; startIndex: number } {
        const tree = new MerkleTree(P, DEPTH);
        for (let i = 0; i < prefilled; i++) {
            tree.insert(BigInt(0xdead + i));
        }
        return {
            tree,
            oldRoot: tree.root(),
            frontier: tree.frontier(),
            startIndex: prefilled,
        };
    }

    function provedRoot(prefilled: number, cm0: Field, cm1: Field): Field {
        const tree = new MerkleTree(P, DEPTH);
        for (let i = 0; i < prefilled; i++) tree.insert(BigInt(0xdead + i));
        tree.insert(cm0);
        tree.insert(cm1);
        return tree.root();
    }

    async function runCase(prefilled: number, cm0: Field, cm1: Field) {
        const { oldRoot, frontier, startIndex } = setupAt(prefilled);
        const newRoot = provedRoot(prefilled, cm0, cm1);

        const coeffs: Field[] = [oldRoot, newRoot, cm0, cm1, BigInt(startIndex)];
        const z = fiatShamirZ(coeffs);
        const expectedY = hornerEval(coeffs, z);

        const w = await circuit.calculateWitness(
            buildInput({ oldRoot, newRoot, cm0, cm1, startIndex, frontier, z }),
            true,
        );
        await circuit.checkConstraints(w);
        await circuit.assertOut(w, { y: expectedY.toString() });
    }

    it("inserts at empty tree (startIndex=0)", async () => {
        await runCase(0, 0xc01dn, 0xc02dn);
    });

    it("inserts at slot=1,2 (startIndex=1)", async () => {
        await runCase(1, 0x111n, 0x222n);
    });

    it("inserts at slot=2,3 within first parent (startIndex=2)", async () => {
        await runCase(2, 0xaaaaaaaaaaan, 0xbbbbbbbbbbbn);
    });

    it("inserts spanning a parent boundary (startIndex=3)", async () => {
        await runCase(3, 0xc1n, 0xc2n);
    });

    it("inserts mid-tree (startIndex=16)", async () => {
        await runCase(16, 0xfeedfacen, 0xdeadbeefn);
    });

    it("inserts crossing higher-level group boundary (startIndex=63)", async () => {
        await runCase(63, 0x1234n, 0x5678n);
    });

    it("inserts late (startIndex=4096)", async () => {
        await runCase(4096, 0x9999n, 0xaaaan);
    });

    it("rejects when supplied new_root does not match the actual tree advance", async () => {
        const { oldRoot, frontier, startIndex } = setupAt(0);
        const cm0 = 1n;
        const cm1 = 2n;
        const wrongNewRoot = 0n; // forced mismatch
        const coeffs: Field[] = [oldRoot, wrongNewRoot, cm0, cm1, BigInt(startIndex)];
        const z = fiatShamirZ(coeffs);

        let threw = false;
        try {
            await circuit.calculateWitness(
                buildInput({ oldRoot, newRoot: wrongNewRoot, cm0, cm1, startIndex, frontier, z }),
                true,
            );
        } catch {
            threw = true;
        }
        expect(threw).to.equal(true);
    });

    it("rejects when start_index = 4^DEPTH - 1 (would put cm1 out of range)", async () => {
        const { oldRoot, frontier } = setupAt(0);
        const startIndex = Math.pow(ARITY, DEPTH) - 1;
        const cm0 = 1n;
        const cm1 = 2n;
        const coeffs: Field[] = [oldRoot, 0n, cm0, cm1, BigInt(startIndex)];
        const z = fiatShamirZ(coeffs);

        let threw = false;
        try {
            await circuit.calculateWitness(
                buildInput({ oldRoot, newRoot: 0n, cm0, cm1, startIndex, frontier, z }),
                true,
            );
        } catch {
            threw = true;
        }
        expect(threw).to.equal(true);
    });
});
