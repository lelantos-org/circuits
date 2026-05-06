import { expect } from "chai";

import { dummyInputAt, dummyOutput, SpentNote, Note, Field, commit, nullifier } from "./helpers";
import { loadCircuit, srcPath } from "./lib/circuit";
import { buildTxBuilder, TxBuilder, DEFAULT_ASSET as ASSET } from "./lib/transact";
import { expectWitnessFails } from "./lib/expect";

const DEPTH = 10;          // quaternary depth 10 → 4^10 = 1,048,576 leaves
const ASSET_B: Field = 99n; // second asset for multi-asset tests
const CIRCUIT = srcPath("2x2.circom");

describe("transact_2x2", function () {
    this.timeout(300000);

    let circuit: any;
    let tx: TxBuilder;

    before(async () => {
        tx = await buildTxBuilder(DEPTH);
        circuit = await loadCircuit(CIRCUIT);
    });

    // Common case: 2 real inputs from the same owner. Returns the finalized
    // SpentNotes and the (frozen) merkle root used for the proof.
    function twoRealInputs(values: [bigint, bigint], nsk: Field, asset: Field = ASSET) {
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(values[0], nsk, 1n, asset), nsk);
        let inB = tx.insert(tree, tx.note(values[1], nsk, 2n, asset), nsk);
        const root = tree.root();
        inA = tx.finalize(tree, inA);
        inB = tx.finalize(tree, inB);
        return { tree, root, inA, inB };
    }

    it("internal 2-in-2-out balanced same asset", async () => {
        const aliceNsk = 11n, bobNsk = 22n;
        const { root, inA, inB } = twoRealInputs([100n, 50n], aliceNsk);
        const outA = tx.note(30n, bobNsk, 100n);
        const outB = tx.note(120n, aliceNsk, 200n);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });

        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("deposit: 2 dummy inputs, 1 real output, public_in > 0", async () => {
        const tree = tx.newTree();
        const root = tree.root();
        const aliceNsk = 11n;
        const dA = dummyInputAt(tx.P, DEPTH, 0n);
        const dB = dummyInputAt(tx.P, DEPTH, 1n);
        const outA = tx.note(1000n, aliceNsk, 9n);
        const outB = tx.note(0n, aliceNsk, 11n);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 1000n, publicOut: 0n,
            inputs: [dA, dB], outputs: [outA, outB], merkleRoot: root,
        });

        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("withdraw: 1 real input, 1 dummy input, public_out > 0", async () => {
        const aliceNsk = 11n;
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(500n, aliceNsk, 1n), aliceNsk);
        const dB = dummyInputAt(tx.P, DEPTH, 99n);
        const root = tree.root();
        inA = tx.finalize(tree, inA);
        const outA = tx.note(200n, aliceNsk, 50n);
        const outB = tx.note(0n, aliceNsk, 60n);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 300n,
            inputs: [inA, dB], outputs: [outA, outB], merkleRoot: root,
        });

        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("FAILS on unbalanced values", async () => {
        const nsk = 11n;
        const { root, inA, inB } = twoRealInputs([100n, 50n], nsk);
        const outA = tx.note(10n, nsk, 9n);
        const outB = tx.note(10n, nsk, 11n);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        await expectWitnessFails(circuit, input);
    });

    it("FAILS on cross-asset rejection (in=A,A out=B,B same scalar sums)", async () => {
        // Point-balance enforces per-asset conservation. Same scalar totals across
        // different assets must fail.
        const nsk = 11n;
        const { root, inA, inB } = twoRealInputs([100n, 50n], nsk, ASSET);
        const outA = tx.note(75n, nsk, 9n, ASSET_B);
        const outB = tx.note(75n, nsk, 11n, ASSET_B);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        await expectWitnessFails(circuit, input);
    });

    it("FAILS on wrong nsk for given pk", async () => {
        const realNsk = 11n;
        const wrongNsk = 12n;
        const tree = tx.newTree();
        const n = tx.note(100n, realNsk, 1n);
        const cm = commit(tx.P, n);
        const idx = tree.insert(cm);
        let inB = tx.insert(tree, tx.note(0n, realNsk, 2n), realNsk);
        const root = tree.root();
        inB = tx.finalize(tree, inB);
        const proof = tree.proof(idx);
        const tampered: SpentNote = {
            ...n, nsk: wrongNsk, cm,
            nf: nullifier(tx.P, wrongNsk, n.rho),
            leafIndex: idx, pathElements: proof.pathElements, pathIndices: proof.pathIndices, isDummy: false,
        };
        const outA = tx.note(100n, realNsk, 9n);
        const outB = tx.note(0n, realNsk, 11n);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [tampered, inB], outputs: [outA, outB], merkleRoot: root,
        });
        await expectWitnessFails(circuit, input);
    });

    it("FAILS on tampered Merkle path", async () => {
        const nsk = 11n;
        const { root, inA, inB } = twoRealInputs([100n, 50n], nsk);
        inA.pathElements[3][0] = inA.pathElements[3][0] + 1n;

        const outA = tx.note(75n, nsk, 9n);
        const outB = tx.note(75n, nsk, 11n);
        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        await expectWitnessFails(circuit, input);
    });

    it("padding output: value=0 note with a different asset accepted", async () => {
        const aliceNsk = 11n;
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(100n, aliceNsk, 1n), aliceNsk);
        const dB = dummyInputAt(tx.P, DEPTH, 99n);
        const root = tree.root();
        inA = tx.finalize(tree, inA);

        const realOut = tx.note(100n, aliceNsk, 9n);
        // Padding output: real value=0 note, real cm. Asset must be != 0.
        // value=0 ⇒ value*gen = identity, contributes neutrally to balance.
        const dOut: Note = { asset: 999n, value: 0n, pk: 0n, rho: 0n, rcm: 0n, rcv: 0n };

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, dB], outputs: [realOut, dOut], merkleRoot: root,
        });

        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("FAILS when output has asset_id == 0 (ghost-note defense, no dummy bypass)", async () => {
        const aliceNsk = 11n;
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(100n, aliceNsk, 1n), aliceNsk);
        const dB = dummyInputAt(tx.P, DEPTH, 99n);
        const root = tree.root();
        inA = tx.finalize(tree, inA);

        const realOut = tx.note(100n, aliceNsk, 9n);
        const dOut: Note = { asset: 0n, value: 0n, pk: 0n, rho: 0n, rcm: 0n, rcv: 0n }; // illegal

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, dB], outputs: [realOut, dOut], merkleRoot: root,
        });
        await expectWitnessFails(circuit, input);
    });

    it("FAILS when non-dummy output has wrong out_cm", async () => {
        const aliceNsk = 11n;
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(100n, aliceNsk, 1n), aliceNsk);
        const dB = dummyInputAt(tx.P, DEPTH, 99n);
        const root = tree.root();
        inA = tx.finalize(tree, inA);

        const realOut = tx.note(100n, aliceNsk, 9n);
        const dOut = dummyOutput();

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, dB], outputs: [realOut, dOut], merkleRoot: root,
        });
        (input.out_cm as string[])[0] = "12345";
        await expectWitnessFails(circuit, input);
    });

    it("FAILS when nullifier doesn't match Poseidon(TAG_NF, nk, rho) for dummy slot", async () => {
        const tree = tx.newTree();
        const root = tree.root();
        const dA = dummyInputAt(tx.P, DEPTH, 0n);
        const dB = dummyInputAt(tx.P, DEPTH, 1n);
        const aliceNsk = 11n;
        const outA = tx.note(1000n, aliceNsk, 9n);
        const outB = tx.note(0n, aliceNsk, 11n);
        const input = tx.build({
            publicAssetId: ASSET, publicIn: 1000n, publicOut: 0n,
            inputs: [dA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        (input.nullifier as string[])[0] = "42";
        await expectWitnessFails(circuit, input);
    });

    it("FAILS when out_cm tampered for padding output", async () => {
        const aliceNsk = 11n;
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(100n, aliceNsk, 1n), aliceNsk);
        const dB = dummyInputAt(tx.P, DEPTH, 99n);
        const root = tree.root();
        inA = tx.finalize(tree, inA);
        const realOut = tx.note(100n, aliceNsk, 9n);
        const dOut = dummyOutput();
        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, dB], outputs: [realOut, dOut], merkleRoot: root,
        });
        (input.out_cm as string[])[1] = "777";
        await expectWitnessFails(circuit, input);
    });

    // ----- additional edge cases -----

    it("spends at leaf indices covering every quaternary path_index slot", async () => {
        const tree = tx.newTree();
        const nsk = 11n;
        const placeholders: SpentNote[] = [];
        for (let i = 0; i < 21; i++) {
            placeholders.push(tx.insert(tree, tx.note(10n, nsk, BigInt(i + 1)), nsk));
        }
        const root = tree.root();

        const inA = tx.finalize(tree, placeholders[17]);
        const inB = tx.finalize(tree, placeholders[20]);

        expect(inA.pathIndices[0]).to.equal(1);
        expect(inB.pathIndices[1]).to.equal(1);

        const outA = tx.note(5n, nsk, 9n);
        const outB = tx.note(15n, nsk, 11n);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("FAILS on wrong merkle_root", async () => {
        const nsk = 11n;
        const { root, inA, inB } = twoRealInputs([100n, 50n], nsk);
        const outA = tx.note(75n, nsk, 9n);
        const outB = tx.note(75n, nsk, 11n);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root + 1n,
        });
        await expectWitnessFails(circuit, input);
    });

    // Two near-identical 64-bit overflow tests collapsed into a parameterized loop.
    for (const field of ["in_value", "out_value"] as const) {
        it(`FAILS when ${field} exceeds 64 bits`, async () => {
            const tree = tx.newTree();
            const root = tree.root();
            const dA = dummyInputAt(tx.P, DEPTH, 0n);
            const dB = dummyInputAt(tx.P, DEPTH, 1n);
            const aliceNsk = 11n;
            const outA = tx.note(0n, aliceNsk, 9n);
            const outB = tx.note(0n, aliceNsk, 11n);

            const input = tx.build({
                publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
                inputs: [dA, dB], outputs: [outA, outB], merkleRoot: root,
            });
            (input[field] as string[])[0] = (1n << 64n).toString();
            await expectWitnessFails(circuit, input);
        });
    }

    it("FAILS when in_is_dummy is non-boolean (2)", async () => {
        const tree = tx.newTree();
        const root = tree.root();
        const dA = dummyInputAt(tx.P, DEPTH, 0n);
        const dB = dummyInputAt(tx.P, DEPTH, 1n);
        const aliceNsk = 11n;
        const outA = tx.note(0n, aliceNsk, 9n);
        const outB = tx.note(0n, aliceNsk, 11n);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [dA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        (input.in_is_dummy as string[])[0] = "2";
        await expectWitnessFails(circuit, input);
    });

    it("all-dummy zero tx is accepted", async () => {
        const tree = tx.newTree();
        const root = tree.root();
        const dA = dummyInputAt(tx.P, DEPTH, 0n);
        const dB = dummyInputAt(tx.P, DEPTH, 1n);
        const dOut1 = dummyOutput();
        const dOut2 = dummyOutput();

        const input = tx.build({
            publicAssetId: 0n, publicIn: 0n, publicOut: 0n,
            inputs: [dA, dB], outputs: [dOut1, dOut2], merkleRoot: root,
        });
        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("simultaneous deposit + withdraw (both public_in and public_out > 0) accepted if balanced", async () => {
        const aliceNsk = 11n;
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(100n, aliceNsk, 1n), aliceNsk);
        const dB = dummyInputAt(tx.P, DEPTH, 99n);
        const root = tree.root();
        inA = tx.finalize(tree, inA);
        const outA = tx.note(80n, aliceNsk, 9n);
        const outB = tx.note(0n, aliceNsk, 11n);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 50n, publicOut: 70n,
            inputs: [inA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("dummy input with garbage non-zero pk/rho/rcm still accepted (key + Merkle bypassed)", async () => {
        const aliceNsk = 11n;
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(100n, aliceNsk, 1n), aliceNsk);
        const root = tree.root();
        inA = tx.finalize(tree, inA);

        const dB = dummyInputAt(tx.P, DEPTH, 99n);
        dB.pk = 0xbadc0den;
        dB.rcm = 0xdeadn;
        dB.pathElements[0][0] = 12345n;

        const outA = tx.note(100n, aliceNsk, 9n);
        const outB = tx.note(0n, aliceNsk, 11n);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("FAILS on tampered in_path_indices (>3)", async () => {
        const nsk = 11n;
        const { root, inA, inB } = twoRealInputs([100n, 50n], nsk);
        const outA = tx.note(75n, nsk, 9n);
        const outB = tx.note(75n, nsk, 11n);
        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        (input.in_path_indices as string[][])[0][0] = "4";
        await expectWitnessFails(circuit, input);
    });

    it("FAILS when dummy input has nonzero value", async () => {
        const tree = tx.newTree();
        const root = tree.root();
        const dummy = dummyInputAt(tx.P, DEPTH, 0n);
        dummy.value = 50n;
        const dB = dummyInputAt(tx.P, DEPTH, 1n);

        const aliceNsk = 11n;
        const outA = tx.note(50n, aliceNsk, 9n);
        const outB = tx.note(0n, aliceNsk, 11n);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 50n, publicOut: 0n,
            inputs: [dummy, dB], outputs: [outA, outB], merkleRoot: root,
        });
        await expectWitnessFails(circuit, input);
    });

    // ===== Multi-asset (Sapling-style) =====

    it("multi-asset balanced: in=[A,B], out=[A,B] per-asset balance holds", async () => {
        const aliceNsk = 11n, bobNsk = 22n;
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(100n, aliceNsk, 1n, ASSET),   aliceNsk);
        let inB = tx.insert(tree, tx.note(50n,  aliceNsk, 2n, ASSET_B), aliceNsk);
        const root = tree.root();
        inA = tx.finalize(tree, inA);
        inB = tx.finalize(tree, inB);

        const outA = tx.note(100n, bobNsk,   100n, ASSET);
        const outB = tx.note(50n,  aliceNsk, 200n, ASSET_B);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });

        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("FAILS when in_cv (public output) is tampered", async () => {
        const nsk = 11n;
        const { root, inA, inB } = twoRealInputs([100n, 50n], nsk);
        const outA = tx.note(75n, nsk, 9n);
        const outB = tx.note(75n, nsk, 11n);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        // Bump the x-coord of the first input's value commitment.
        (input.in_cv as string[][])[0][0] = "42";
        await expectWitnessFails(circuit, input);
    });

    it("dummy with arbitrary asset_id and rcv accepted (value=0 ⇒ no balance contribution)", async () => {
        const aliceNsk = 11n;
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(100n, aliceNsk, 1n), aliceNsk);
        const root = tree.root();
        inA = tx.finalize(tree, inA);

        const dB = dummyInputAt(tx.P, DEPTH, 99n);
        // Smuggle nonsense asset/rcv into the dummy slot. value=0 forced by
        // DummyZeroValue; gen is computed but multiplied by 0 → identity.
        dB.asset = 12345n;
        dB.rcv = 0n;

        const outA = tx.note(100n, aliceNsk, 9n);
        const outB = tx.note(0n, aliceNsk, 11n);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("FAILS when non-dummy input has asset_id == 0", async () => {
        const nsk = 11n;
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(100n, nsk, 1n, 0n), nsk);   // asset_id = 0
        let inB = tx.insert(tree, tx.note(50n, nsk, 2n), nsk);
        const root = tree.root();
        inA = tx.finalize(tree, inA);
        inB = tx.finalize(tree, inB);
        const outA = tx.note(75n, nsk, 9n);
        const outB = tx.note(75n, nsk, 11n);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        await expectWitnessFails(circuit, input);
    });

    it("FAILS when non-dummy output has asset_id == 0", async () => {
        const nsk = 11n;
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(100n, nsk, 1n), nsk);
        const dB = dummyInputAt(tx.P, DEPTH, 99n);
        const root = tree.root();
        inA = tx.finalize(tree, inA);
        const outA = tx.note(100n, nsk, 9n, 0n);                       // asset_id = 0
        const outB = tx.note(0n, nsk, 11n);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, dB], outputs: [outA, outB], merkleRoot: root,
        });
        await expectWitnessFails(circuit, input);
    });

    // ===== FMD clue / Legendre negative coverage =====
    //
    // The honest path is exercised everywhere above (clues are auto-synthesized
    // by TxBuilder). These cases tamper the prover's clue/Legendre witnesses
    // post-hoc to confirm ClueCheck + HashToBit reject inside the full circuit.

    it("FAILS when out_clue_bits is flipped (ClueCheck mismatch)", async () => {
        const nsk = 11n;
        const { root, inA, inB } = twoRealInputs([100n, 50n], nsk);
        const outA = tx.note(75n, nsk, 9n);
        const outB = tx.note(75n, nsk, 11n);
        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        const orig = BigInt((input.out_clue_bits as string[])[0]);
        (input.out_clue_bits as string[])[0] = (orig ^ 1n).toString();
        await expectWitnessFails(circuit, input);
    });

    it("FAILS when out_legendre_bit is flipped (HashToBit reject)", async () => {
        const nsk = 11n;
        const { root, inA, inB } = twoRealInputs([100n, 50n], nsk);
        const outA = tx.note(75n, nsk, 9n);
        const outB = tx.note(75n, nsk, 11n);
        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        const orig = (input.out_legendre_bit as string[][])[0][0];
        (input.out_legendre_bit as string[][])[0][0] = orig === "1" ? "0" : "1";
        await expectWitnessFails(circuit, input);
    });

    it("FAILS when out_legendre_y is wrong (no valid sqrt)", async () => {
        const nsk = 11n;
        const { root, inA, inB } = twoRealInputs([100n, 50n], nsk);
        const outA = tx.note(75n, nsk, 9n);
        const outB = tx.note(75n, nsk, 11n);
        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        const orig = BigInt((input.out_legendre_y as string[][])[0][0]);
        (input.out_legendre_y as string[][])[0][0] = (orig + 1n).toString();
        await expectWitnessFails(circuit, input);
    });

    it("multi-asset: per-asset imbalance fails even if scalar totals match", async () => {
        // in: A=80, B=120 (totals=200). out: A=120, B=80 (totals=200). Per-asset
        // mismatched. Old single-asset value-balance would accept; point-balance
        // must reject.
        const nsk = 11n;
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(80n,  nsk, 1n, ASSET),   nsk);
        let inB = tx.insert(tree, tx.note(120n, nsk, 2n, ASSET_B), nsk);
        const root = tree.root();
        inA = tx.finalize(tree, inA);
        inB = tx.finalize(tree, inB);
        const outA = tx.note(120n, nsk, 9n,  ASSET);
        const outB = tx.note(80n,  nsk, 11n, ASSET_B);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        await expectWitnessFails(circuit, input);
    });
});
