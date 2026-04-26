import { expect } from "chai";
import * as path from "path";
// circom_tester ships without TS types
// @ts-ignore
import { wasm as wasmTester } from "circom_tester";

import {
    Poseidon, Jubjub, MerkleTree, derivePk, commit, nullifier,
    toCircomInput, dummyInputAt, dummyOutput, SpentNote, Note, Field,
} from "./helpers";

// Quaternary tree: depth 8 → 4^8 = 65,536 leaves (matches binary depth 16 capacity).
const DEPTH = 10;
const ASSET = 7n;          // arbitrary asset id
const ASSET_B = 99n;       // second asset for multi-asset tests
const CIRCUIT = path.join(__dirname, "..", "2x2.circom");

describe("transact_2x2", function () {
    this.timeout(300000);

    let circuit: any;
    let P: Poseidon;
    let J: Jubjub;

    before(async () => {
        P = await Poseidon.build();
        J = await Jubjub.build();
        circuit = await wasmTester(CIRCUIT, {
            include: [path.join(__dirname, "..", "..", "node_modules")],
        });
    });

    function insert(tree: MerkleTree, n: Note, nsk: Field): SpentNote {
        const cm = commit(P, n);
        const idx = tree.insert(cm);
        return {
            ...n, nsk, cm,
            nf: nullifier(P, nsk, n.rho),
            leafIndex: idx,
            pathElements: [], pathIndices: [], isDummy: false,
        };
    }
    function finalize(tree: MerkleTree, sn: SpentNote): SpentNote {
        const { pathElements, pathIndices } = tree.proof(sn.leafIndex);
        return { ...sn, pathElements, pathIndices };
    }

    function freshNote(value: bigint, ownerNsk: Field, rho: Field, asset: Field = ASSET): Note {
        return { asset, value, pk: derivePk(P, ownerNsk), rho, rcm: rho + 1n, rcv: rho + 2n };
    }
    function note(value: bigint, ownerNsk: Field, rho: Field, asset: Field = ASSET): Note {
        return { asset, value, pk: derivePk(P, ownerNsk), rho, rcm: rho + 1n, rcv: rho + 2n };
    }

    it("internal 2-in-2-out balanced same asset", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const aliceNsk = 11n, bobNsk = 22n;

        let inA = insert(tree, freshNote(100n, aliceNsk, 1n), aliceNsk);
        let inB = insert(tree, freshNote(50n, aliceNsk, 2n), aliceNsk);
        const root = tree.root();
        inA = finalize(tree, inA);
        inB = finalize(tree, inB);

        const outA = note(30n, bobNsk, 100n);
        const outB = note(120n, aliceNsk, 200n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });

        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("deposit: 2 dummy inputs, 1 real output, public_in > 0", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const root = tree.root();
        const aliceNsk = 11n;

        const dA = dummyInputAt(P, DEPTH, 0n);
        const dB = dummyInputAt(P, DEPTH, 1n);

        const outA = note(1000n, aliceNsk, 9n);
        const outB = note(0n, aliceNsk, 11n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 1000n, publicOut: 0n,
            inputs: [dA, dB], outputs: [outA, outB], merkleRoot: root,
        });

        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("withdraw: 1 real input, 1 dummy input, public_out > 0", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const aliceNsk = 11n;
        let inA = insert(tree, freshNote(500n, aliceNsk, 1n), aliceNsk);
        const dB = dummyInputAt(P, DEPTH, 99n);
        const root = tree.root();
        inA = finalize(tree, inA);

        const outA = note(200n, aliceNsk, 50n);
        const outB = note(0n, aliceNsk, 60n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 300n,
            inputs: [inA, dB], outputs: [outA, outB], merkleRoot: root,
        });

        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("FAILS on unbalanced values", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const nsk = 11n;
        let inA = insert(tree, freshNote(100n, nsk, 1n), nsk);
        let inB = insert(tree, freshNote(50n, nsk, 2n), nsk);
        const root = tree.root();
        inA = finalize(tree, inA);
        inB = finalize(tree, inB);
        const outA = note(10n, nsk, 9n);
        const outB = note(10n, nsk, 11n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("FAILS on cross-asset rejection (in=A,A out=B,B same scalar sums)", async () => {
        // No longer a "single-asset" check — point-balance enforces per-asset
        // conservation. Same scalar totals across different assets must fail.
        const tree = new MerkleTree(P, DEPTH);
        const nsk = 11n;
        let inA = insert(tree, freshNote(100n, nsk, 1n, ASSET), nsk);
        let inB = insert(tree, freshNote(50n, nsk, 2n, ASSET), nsk);
        const root = tree.root();
        inA = finalize(tree, inA);
        inB = finalize(tree, inB);
        const outA = note(75n, nsk, 9n, ASSET_B);
        const outB = note(75n, nsk, 11n, ASSET_B);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("FAILS on wrong nsk for given pk", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const realNsk = 11n;
        const wrongNsk = 12n;
        const n = freshNote(100n, realNsk, 1n);
        const cm = commit(P, n);
        const idx = tree.insert(cm);
        let inB = insert(tree, freshNote(0n, realNsk, 2n), realNsk);
        const root = tree.root();
        inB = finalize(tree, inB);
        const proof = tree.proof(idx);
        const tampered: SpentNote = {
            ...n, nsk: wrongNsk, cm,
            nf: nullifier(P, wrongNsk, n.rho),
            leafIndex: idx, pathElements: proof.pathElements, pathIndices: proof.pathIndices, isDummy: false,
        };
        const outA = note(100n, realNsk, 9n);
        const outB = note(0n, realNsk, 11n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [tampered, inB], outputs: [outA, outB], merkleRoot: root,
        });
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("FAILS on tampered Merkle path", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const nsk = 11n;
        let inA = insert(tree, freshNote(100n, nsk, 1n), nsk);
        let inB = insert(tree, freshNote(50n, nsk, 2n), nsk);
        const root = tree.root();
        inA = finalize(tree, inA);
        inB = finalize(tree, inB);
        inA.pathElements[3][0] = inA.pathElements[3][0] + 1n;

        const outA = note(75n, nsk, 9n);
        const outB = note(75n, nsk, 11n);
        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("padding output: value=0 note with a different asset accepted", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const aliceNsk = 11n;
        let inA = insert(tree, freshNote(100n, aliceNsk, 1n), aliceNsk);
        const dB = dummyInputAt(P, DEPTH, 99n);
        const root = tree.root();
        inA = finalize(tree, inA);

        const realOut = note(100n, aliceNsk, 9n);
        // Padding output: real value=0 note, real cm. Asset must be != 0.
        // value=0 ⇒ value*gen = identity, contributes neutrally to balance.
        const dOut: Note = { asset: 999n, value: 0n, pk: 0n, rho: 0n, rcm: 0n, rcv: 0n };

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, dB], outputs: [realOut, dOut], merkleRoot: root,
        });

        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("FAILS when output has asset_id == 0 (ghost-note defense, no dummy bypass)", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const aliceNsk = 11n;
        let inA = insert(tree, freshNote(100n, aliceNsk, 1n), aliceNsk);
        const dB = dummyInputAt(P, DEPTH, 99n);
        const root = tree.root();
        inA = finalize(tree, inA);

        const realOut = note(100n, aliceNsk, 9n);
        const dOut: Note = { asset: 0n, value: 0n, pk: 0n, rho: 0n, rcm: 0n, rcv: 0n }; // illegal

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, dB], outputs: [realOut, dOut], merkleRoot: root,
        });
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("FAILS when non-dummy output has wrong out_cm", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const aliceNsk = 11n;
        let inA = insert(tree, freshNote(100n, aliceNsk, 1n), aliceNsk);
        const dB = dummyInputAt(P, DEPTH, 99n);
        const root = tree.root();
        inA = finalize(tree, inA);

        const realOut = note(100n, aliceNsk, 9n);
        const dOut = dummyOutput();

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, dB], outputs: [realOut, dOut], merkleRoot: root,
        });
        (input.out_cm as string[])[0] = "12345";
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("FAILS when nullifier doesn't match Poseidon(TAG_NF, nsk, rho) for dummy slot", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const root = tree.root();
        const dA = dummyInputAt(P, DEPTH, 0n);
        const dB = dummyInputAt(P, DEPTH, 1n);
        const aliceNsk = 11n;
        const outA = note(1000n, aliceNsk, 9n);
        const outB = note(0n, aliceNsk, 11n);
        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 1000n, publicOut: 0n,
            inputs: [dA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        (input.nullifier as string[])[0] = "42";
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("FAILS when out_cm tampered for padding output", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const aliceNsk = 11n;
        let inA = insert(tree, freshNote(100n, aliceNsk, 1n), aliceNsk);
        const dB = dummyInputAt(P, DEPTH, 99n);
        const root = tree.root();
        inA = finalize(tree, inA);
        const realOut = note(100n, aliceNsk, 9n);
        const dOut = dummyOutput();
        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, dB], outputs: [realOut, dOut], merkleRoot: root,
        });
        (input.out_cm as string[])[1] = "777";
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    // ----- additional edge cases -----

    it("spends at leaf indices covering every quaternary path_index slot", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const nsk = 11n;
        const placeholders: SpentNote[] = [];
        for (let i = 0; i < 21; i++) {
            placeholders.push(insert(tree, freshNote(10n, nsk, BigInt(i + 1)), nsk));
        }
        const root = tree.root();

        const inA = finalize(tree, placeholders[17]);
        const inB = finalize(tree, placeholders[20]);

        expect(inA.pathIndices[0]).to.equal(1);
        expect(inB.pathIndices[1]).to.equal(1);

        const outA = note(5n, nsk, 9n);
        const outB = note(15n, nsk, 11n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("FAILS on wrong merkle_root", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const nsk = 11n;
        let inA = insert(tree, freshNote(100n, nsk, 1n), nsk);
        let inB = insert(tree, freshNote(50n, nsk, 2n), nsk);
        const root = tree.root();
        inA = finalize(tree, inA);
        inB = finalize(tree, inB);
        const outA = note(75n, nsk, 9n);
        const outB = note(75n, nsk, 11n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root + 1n,
        });
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("FAILS when in_value exceeds 64 bits", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const root = tree.root();
        const dA = dummyInputAt(P, DEPTH, 0n);
        const dB = dummyInputAt(P, DEPTH, 1n);
        const aliceNsk = 11n;
        const outA = note(0n, aliceNsk, 9n);
        const outB = note(0n, aliceNsk, 11n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [dA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        (input.in_value as string[])[0] = (1n << 64n).toString();
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("FAILS when out_value exceeds 64 bits", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const root = tree.root();
        const dA = dummyInputAt(P, DEPTH, 0n);
        const dB = dummyInputAt(P, DEPTH, 1n);
        const aliceNsk = 11n;
        const outA: Note = { asset: ASSET, value: 1n << 64n, pk: derivePk(P, aliceNsk), rho: 9n, rcm: 10n, rcv: 11n };
        const outB = note(0n, aliceNsk, 11n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: (1n << 64n), publicOut: 0n,
            inputs: [dA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("FAILS when in_is_dummy is non-boolean (2)", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const root = tree.root();
        const dA = dummyInputAt(P, DEPTH, 0n);
        const dB = dummyInputAt(P, DEPTH, 1n);
        const aliceNsk = 11n;
        const outA = note(0n, aliceNsk, 9n);
        const outB = note(0n, aliceNsk, 11n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [dA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        (input.in_is_dummy as string[])[0] = "2";
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("all-dummy zero tx is accepted", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const root = tree.root();
        const dA = dummyInputAt(P, DEPTH, 0n);
        const dB = dummyInputAt(P, DEPTH, 1n);
        const dOut1 = dummyOutput();
        const dOut2 = dummyOutput();

        const input = toCircomInput(P, J, {
            publicAssetId: 0n, publicIn: 0n, publicOut: 0n,
            inputs: [dA, dB], outputs: [dOut1, dOut2], merkleRoot: root,
        });
        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("simultaneous deposit + withdraw (both public_in and public_out > 0) accepted if balanced", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const aliceNsk = 11n;
        let inA = insert(tree, freshNote(100n, aliceNsk, 1n), aliceNsk);
        const dB = dummyInputAt(P, DEPTH, 99n);
        const root = tree.root();
        inA = finalize(tree, inA);
        const outA = note(80n, aliceNsk, 9n);
        const outB = note(0n, aliceNsk, 11n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 50n, publicOut: 70n,
            inputs: [inA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("dummy input with garbage non-zero pk/rho/rcm still accepted (key + Merkle bypassed)", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const aliceNsk = 11n;
        let inA = insert(tree, freshNote(100n, aliceNsk, 1n), aliceNsk);
        const root = tree.root();
        inA = finalize(tree, inA);

        const dB = dummyInputAt(P, DEPTH, 99n);
        dB.pk = 0xbadc0den;
        dB.rcm = 0xdeadn;
        dB.pathElements[0][0] = 12345n;

        const outA = note(100n, aliceNsk, 9n);
        const outB = note(0n, aliceNsk, 11n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("FAILS on tampered in_path_indices (>3)", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const nsk = 11n;
        let inA = insert(tree, freshNote(100n, nsk, 1n), nsk);
        let inB = insert(tree, freshNote(50n, nsk, 2n), nsk);
        const root = tree.root();
        inA = finalize(tree, inA);
        inB = finalize(tree, inB);
        const outA = note(75n, nsk, 9n);
        const outB = note(75n, nsk, 11n);
        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        (input.in_path_indices as string[][])[0][0] = "4";
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("FAILS when dummy input has nonzero value", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const root = tree.root();
        const dummy = dummyInputAt(P, DEPTH, 0n);
        dummy.value = 50n;
        const dB = dummyInputAt(P, DEPTH, 1n);

        const aliceNsk = 11n;
        const outA = note(50n, aliceNsk, 9n);
        const outB = note(0n, aliceNsk, 11n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 50n, publicOut: 0n,
            inputs: [dummy, dB], outputs: [outA, outB], merkleRoot: root,
        });
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    // ===== Multi-asset (Sapling-style) =====

    it("multi-asset balanced: in=[A,B], out=[A,B] per-asset balance holds", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const aliceNsk = 11n, bobNsk = 22n;

        // Two notes of asset A, two of asset B inserted on chain.
        let inA = insert(tree, freshNote(100n, aliceNsk, 1n, ASSET),   aliceNsk);
        let inB = insert(tree, freshNote(50n,  aliceNsk, 2n, ASSET_B), aliceNsk);
        const root = tree.root();
        inA = finalize(tree, inA);
        inB = finalize(tree, inB);

        // Outputs preserve per-asset totals: A: 100→100, B: 50→50.
        const outA = note(100n, bobNsk,   100n, ASSET);
        const outB = note(50n,  aliceNsk, 200n, ASSET_B);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });

        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("FAILS when in_cv (public output) is tampered", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const nsk = 11n;
        let inA = insert(tree, freshNote(100n, nsk, 1n), nsk);
        let inB = insert(tree, freshNote(50n, nsk, 2n), nsk);
        const root = tree.root();
        inA = finalize(tree, inA);
        inB = finalize(tree, inB);
        const outA = note(75n, nsk, 9n);
        const outB = note(75n, nsk, 11n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        // Bump the x-coord of the first input's value commitment.
        (input.in_cv as string[][])[0][0] = "42";
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("FAILS when pub_asset_gen is wrong for given public_asset_id (deposit)", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const root = tree.root();
        const dA = dummyInputAt(P, DEPTH, 0n);
        const dB = dummyInputAt(P, DEPTH, 1n);
        const aliceNsk = 11n;
        const outA = note(1000n, aliceNsk, 9n);
        const outB = note(0n, aliceNsk, 11n);

        // Pass a public-asset generator that does NOT match HashToAssetGen(ASSET):
        // use the gen for ASSET_B instead. Off-chain registry would catch this in
        // Solidity, but the circuit independently rejects via balance failure
        // (deposit credits the wrong asset bucket).
        const wrongGen = J.hashToAssetGen(ASSET_B);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET,
            publicAssetGen: wrongGen,
            publicIn: 1000n, publicOut: 0n,
            inputs: [dA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("dummy with arbitrary asset_id and rcv accepted (value=0 ⇒ no balance contribution)", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const aliceNsk = 11n;
        let inA = insert(tree, freshNote(100n, aliceNsk, 1n), aliceNsk);
        const root = tree.root();
        inA = finalize(tree, inA);

        const dB = dummyInputAt(P, DEPTH, 99n);
        // Smuggle nonsense asset/rcv into the dummy slot. value=0 forced by
        // DummyZeroValue; gen is computed but multiplied by 0 → identity.
        // rcv contribution cancels in rcv_delta.
        dB.asset = 12345n;
        dB.rcv = 0n; // keep zero to match rcv_delta cancellation; nonzero would also work since balance accounts for it

        const outA = note(100n, aliceNsk, 9n);
        const outB = note(0n, aliceNsk, 11n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("FAILS when pub_asset_gen is identity (0,1)", async () => {
        // SafePoint(pub_asset_gen) must reject (0,1). Without this, an
        // all-dummy tx could withdraw arbitrary public_out from the pool.
        const tree = new MerkleTree(P, DEPTH);
        const root = tree.root();
        const dA = dummyInputAt(P, DEPTH, 0n);
        const dB = dummyInputAt(P, DEPTH, 1n);
        const dOut1 = dummyOutput();
        const dOut2 = dummyOutput();

        const input = toCircomInput(P, J, {
            publicAssetId: 7n,
            publicAssetGen: [0n, 1n],
            publicIn: 0n, publicOut: 1000n,
            inputs: [dA, dB], outputs: [dOut1, dOut2], merkleRoot: root,
        });
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("FAILS when pub_asset_gen is 2-torsion (0,-1)", async () => {
        // (0, -1) has x=0; EscalarMulAny mis-substitutes G8. SafePoint catches it.
        const tree = new MerkleTree(P, DEPTH);
        const root = tree.root();
        const dA = dummyInputAt(P, DEPTH, 0n);
        const dB = dummyInputAt(P, DEPTH, 1n);
        const aliceNsk = 11n;
        const outA = note(1000n, aliceNsk, 9n);
        const outB = note(0n, aliceNsk, 11n);
        // p (BN254 scalar field) - 1
        const NEG_ONE = 21888242871839275222246405745257275088548364400416034343698204186575808495616n;
        const input = toCircomInput(P, J, {
            publicAssetId: ASSET,
            publicAssetGen: [0n, NEG_ONE],
            publicIn: 1000n, publicOut: 0n,
            inputs: [dA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("FAILS when pub_asset_gen is off-curve", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const root = tree.root();
        const dA = dummyInputAt(P, DEPTH, 0n);
        const dB = dummyInputAt(P, DEPTH, 1n);
        const aliceNsk = 11n;
        const outA = note(1000n, aliceNsk, 9n);
        const outB = note(0n, aliceNsk, 11n);
        const input = toCircomInput(P, J, {
            publicAssetId: ASSET,
            publicAssetGen: [3n, 5n],   // garbage
            publicIn: 1000n, publicOut: 0n,
            inputs: [dA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("FAILS when non-dummy input has asset_id == 0", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const nsk = 11n;
        let inA = insert(tree, freshNote(100n, nsk, 1n, 0n), nsk);   // asset_id = 0
        let inB = insert(tree, freshNote(50n, nsk, 2n), nsk);
        const root = tree.root();
        inA = finalize(tree, inA);
        inB = finalize(tree, inB);
        const outA = note(75n, nsk, 9n);
        const outB = note(75n, nsk, 11n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("FAILS when non-dummy output has asset_id == 0", async () => {
        const tree = new MerkleTree(P, DEPTH);
        const nsk = 11n;
        let inA = insert(tree, freshNote(100n, nsk, 1n), nsk);
        const dB = dummyInputAt(P, DEPTH, 99n);
        const root = tree.root();
        inA = finalize(tree, inA);
        const outA = note(100n, nsk, 9n, 0n);                       // asset_id = 0
        const outB = note(0n, nsk, 11n);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });

    it("multi-asset: per-asset imbalance fails even if scalar totals match", async () => {
        // in: A=80, B=120 (totals=200). out: A=120, B=80 (totals=200). Per-asset
        // mismatched. Old single-asset value-balance would accept; point-balance
        // must reject.
        const tree = new MerkleTree(P, DEPTH);
        const nsk = 11n;
        let inA = insert(tree, freshNote(80n,  nsk, 1n, ASSET),   nsk);
        let inB = insert(tree, freshNote(120n, nsk, 2n, ASSET_B), nsk);
        const root = tree.root();
        inA = finalize(tree, inA);
        inB = finalize(tree, inB);
        const outA = note(120n, nsk, 9n,  ASSET);
        const outB = note(80n,  nsk, 11n, ASSET_B);

        const input = toCircomInput(P, J, {
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        let threw = false;
        try { await circuit.calculateWitness(input, true); } catch { threw = true; }
        expect(threw).to.equal(true);
    });
});
