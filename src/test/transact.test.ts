import { expect } from "chai";

import { dummyInputAt, dummyOutput, SpentNote, Note, Field, commit, nullifier, buildRho, deriveNk } from "./helpers";
import { loadCircuit, srcPath } from "./lib/circuit";
import { buildTxBuilder, TxBuilder, DEFAULT_ASSET as ASSET } from "./lib/transact";
import { expectWitnessFails } from "./lib/expect";
import { flatten, hornerEval } from "@lelantos-org/sdk";

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
            nf: nullifier(tx.P, wrongNsk, n.rho, cm),
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
        const dOut: Note = { asset: 999n, value: 0n, pk: 0n, rho: 0n, rcm: 0n, rcv: 0n, rcvDep: 0n };

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
        const dOut: Note = { asset: 0n, value: 0n, pk: 0n, rho: 0n, rcm: 0n, rcv: 0n, rcvDep: 0n }; // illegal

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

    it("FAILS when nullifier doesn't match Poseidon(TAG_NF, nk, rho, cm) for dummy slot", async () => {
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
        // nf binds cm, and cm covers pk/rcm — re-seal after mutating them.
        dB.cm = commit(tx.P, dB);
        dB.nf = nullifier(tx.P, dB.nsk, dB.rho, dB.cm);

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
        // asset feeds packed_av inside cm, and nf binds cm — re-seal.
        dB.cm = commit(tx.P, dB);
        dB.nf = nullifier(tx.P, dB.nsk, dB.rho, dB.cm);

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

    // ===== Range-check coverage for asset / public-bucket scalars =====
    //
    // HashToAssetGen wraps Num2Bits(64) on every asset_id (per-note and
    // public-bucket). 2x2.circom layers RangeCheck64 on public_in/out.
    // Each tampers ONE 64-bit-bound field to (1 << 64) and expects rejection.

    /// Build a balanced honest input then apply `tamper` to the JSON shape
    /// before submission. Used for parameterized range tests.
    async function expectFailsAfterTamper(tamper: (input: Record<string, unknown>) => void) {
        const nsk = 11n;
        const { root, inA, inB } = twoRealInputs([100n, 50n], nsk);
        const outA = tx.note(75n, nsk, 9n);
        const outB = tx.note(75n, nsk, 11n);
        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        tamper(input);
        await expectWitnessFails(circuit, input);
    }

    it("FAILS when public_asset_id exceeds 2^64 (HashToAssetGen Num2Bits)", async () => {
        await expectFailsAfterTamper(input => {
            input.public_asset_id = (1n << 64n).toString();
        });
    });

    it("FAILS when in_asset[0] exceeds 2^64 (per-note Num2Bits in HashToAssetGen)", async () => {
        await expectFailsAfterTamper(input => {
            (input.in_asset as string[])[0] = (1n << 64n).toString();
        });
    });

    it("FAILS when out_asset[0] exceeds 2^64 (per-note Num2Bits in HashToAssetGen)", async () => {
        await expectFailsAfterTamper(input => {
            (input.out_asset as string[])[0] = (1n << 64n).toString();
        });
    });

    it("FAILS when public_in exceeds 2^64 (RangeCheck64)", async () => {
        await expectFailsAfterTamper(input => {
            input.public_in = (1n << 64n).toString();
        });
    });

    it("FAILS when public_out exceeds 2^64 (RangeCheck64)", async () => {
        await expectFailsAfterTamper(input => {
            input.public_out = (1n << 64n).toString();
        });
    });

    it("FAILS when out_cv (public output) is tampered", async () => {
        // Mirror of the existing in_cv tamper test, but for OutputNote's
        // `cv[0] === vc.cv[0]` binding. Catches a substituted public cv
        // that doesn't match the ValueCommit recomputation.
        await expectFailsAfterTamper(input => {
            const orig = BigInt((input.out_cv as string[][])[0][0]);
            (input.out_cv as string[][])[0][0] = (orig + 1n).toString();
        });
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

    // ===== PolyEval binding: FMD clue fields =====
    // ClueCheck was removed; out_clue_Rx/Ry/bits have no in-circuit constraints.
    // Relayer resistance relies solely on PolyEval: changing any clue field must
    // change y, making the proof invalid with the original (z, y) pair.
    // These tests verify the wiring is correct — a TransactCompressN bug that
    // silently dropped clue slots would pass all constraint tests but fail here.

    function buildBindingBase() {
        const nsk = 11n;
        const { root, inA, inB } = twoRealInputs([100n, 50n], nsk);
        const outA = tx.note(75n, nsk, 9n);
        const outB = tx.note(75n, nsk, 11n);
        // Non-zero address fields so their coefficient slots are distinguishable.
        const raw = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        raw.recipient_address = "12345";
        raw.chain_id          = "67890";
        raw.payer_address     = "11111";
        raw.relayer_address   = "22222";
        return raw;
    }

    async function assertBinds(
        base: any,
        patch: (inp: any) => any,
        label: string,
    ) {
        const z = BigInt(base.z);
        const coeffs1 = flatten(base);
        const y1 = hornerEval(coeffs1, z);

        const tampered = patch({ ...base });
        const coeffs2 = flatten(tampered);
        const y2 = hornerEval(coeffs2, z);

        expect(y1, `${label}: y must differ when field changes`).to.not.equal(y2);

        // Both witnesses generate (no in-circuit constraint on these fields).
        const w1 = await circuit.calculateWitness(base, true);
        const w2 = await circuit.calculateWitness(tampered, true);
        await circuit.assertOut(w1, { y: y1.toString() });
        await circuit.assertOut(w2, { y: y2.toString() });
    }

    it("BINDS out_clue_Rx[0]: altering it changes y", async () => {
        const base = buildBindingBase();
        await assertBinds(base, inp => {
            inp.out_clue_Rx = [(BigInt(inp.out_clue_Rx[0]) + 1n).toString(), inp.out_clue_Rx[1]];
            return inp;
        }, "out_clue_Rx[0]");
    });

    it("BINDS out_clue_Ry[0]: altering it changes y", async () => {
        const base = buildBindingBase();
        await assertBinds(base, inp => {
            inp.out_clue_Ry = [(BigInt(inp.out_clue_Ry[0]) + 1n).toString(), inp.out_clue_Ry[1]];
            return inp;
        }, "out_clue_Ry[0]");
    });

    it("BINDS out_clue_bits[0]: altering it changes y", async () => {
        const base = buildBindingBase();
        await assertBinds(base, inp => {
            inp.out_clue_bits = [(BigInt(inp.out_clue_bits[0]) + 1n).toString(), inp.out_clue_bits[1]];
            return inp;
        }, "out_clue_bits[0]");
    });

    it("BINDS out_clue_Rx[1]: altering it changes y", async () => {
        const base = buildBindingBase();
        await assertBinds(base, inp => {
            inp.out_clue_Rx = [inp.out_clue_Rx[0], (BigInt(inp.out_clue_Rx[1]) + 1n).toString()];
            return inp;
        }, "out_clue_Rx[1]");
    });

    it("BINDS out_clue_Ry[1]: altering it changes y", async () => {
        const base = buildBindingBase();
        await assertBinds(base, inp => {
            inp.out_clue_Ry = [inp.out_clue_Ry[0], (BigInt(inp.out_clue_Ry[1]) + 1n).toString()];
            return inp;
        }, "out_clue_Ry[1]");
    });

    it("BINDS out_clue_bits[1]: altering it changes y", async () => {
        const base = buildBindingBase();
        await assertBinds(base, inp => {
            inp.out_clue_bits = [inp.out_clue_bits[0], (BigInt(inp.out_clue_bits[1]) + 1n).toString()];
            return inp;
        }, "out_clue_bits[1]");
    });

    // ===== PolyEval binding: encrypted-note payload =====
    // out_aux_digest is keccak256(abi.encode(aux)) mod r, recomputed on-chain
    // from the aux calldata. Like the clue fields it has no in-circuit
    // constraint, so PolyEval inclusion is the entire defence: without it a
    // relayer could keep the clue intact (proof verifies, recipient's FMD scan
    // still flags the note) while corrupting ephPub/ciphertext, leaving the
    // recipient unable to decrypt the opening of a note already paid for.

    it("BINDS out_aux_digest: altering it changes y", async () => {
        const base = buildBindingBase();
        await assertBinds(base, inp => {
            inp.out_aux_digest = (BigInt(inp.out_aux_digest) + 1n).toString();
            return inp;
        }, "out_aux_digest");
    });

    it("out_aux_digest occupies the final coefficient slot", () => {
        const base = buildBindingBase();
        const coeffs = flatten(base);
        expect(coeffs.length).to.equal(31);
        expect(coeffs[30]).to.equal(BigInt(base.out_aux_digest));
    });

    // ===== PolyEval binding: address fields =====

    it("BINDS recipient_address: altering it changes y", async () => {
        const base = buildBindingBase();
        await assertBinds(base, inp => {
            inp.recipient_address = (BigInt(inp.recipient_address) + 1n).toString();
            return inp;
        }, "recipient_address");
    });

    it("BINDS chain_id: altering it changes y", async () => {
        const base = buildBindingBase();
        await assertBinds(base, inp => {
            inp.chain_id = (BigInt(inp.chain_id) + 1n).toString();
            return inp;
        }, "chain_id");
    });

    it("BINDS payer_address: altering it changes y", async () => {
        const base = buildBindingBase();
        await assertBinds(base, inp => {
            inp.payer_address = (BigInt(inp.payer_address) + 1n).toString();
            return inp;
        }, "payer_address");
    });

    it("BINDS relayer_address: altering it changes y", async () => {
        const base = buildBindingBase();
        await assertBinds(base, inp => {
            inp.relayer_address = (BigInt(inp.relayer_address) + 1n).toString();
            return inp;
        }, "relayer_address");
    });

    // ===== in-circuit constraint: out_cv_dep =====
    // out_cv_dep is PolyEval-bound AND equality-constrained in-circuit
    // (2x2.circom: out_cv_dep[j][0] === out_note[j].cv_dep[0]). Tampering
    // must cause constraint failure, not just a different y.

    it("FAILS when out_cv_dep[0][0] is tampered (in-circuit equality constraint)", async () => {
        await expectFailsAfterTamper(input => {
            const orig = BigInt((input.out_cv_dep as string[][])[0][0]);
            (input.out_cv_dep as string[][])[0][0] = (orig + 1n).toString();
        });
    });

    // ===== private-signal tamper coverage =====
    // These verify the end-to-end constraint chain for private inputs.
    // A computation bug in ValueCommit / NoteCommitment / leaf-hash would
    // not be caught by any existing test if the private signals are unconstrained.

    it("FAILS when in_rcv[0] is tampered (cv binding rejects wrong blinding)", async () => {
        await expectFailsAfterTamper(input => {
            const orig = BigInt((input.in_rcv as string[])[0]);
            (input.in_rcv as string[])[0] = (orig + 1n).toString();
        });
    });

    it("FAILS when out_rcv[0] is tampered (cv binding rejects wrong blinding)", async () => {
        await expectFailsAfterTamper(input => {
            const orig = BigInt((input.out_rcv as string[])[0]);
            (input.out_rcv as string[])[0] = (orig + 1n).toString();
        });
    });

    it("FAILS when in_rcv_dep[0] is tampered (leaf hash changes, Merkle proof fails)", async () => {
        await expectFailsAfterTamper(input => {
            const orig = BigInt((input.in_rcv_dep as string[])[0]);
            (input.in_rcv_dep as string[])[0] = (orig + 1n).toString();
        });
    });

    it("FAILS when out_rcv_dep[0] is tampered (cv_dep equality constraint rejects)", async () => {
        await expectFailsAfterTamper(input => {
            const orig = BigInt((input.out_rcv_dep as string[])[0]);
            (input.out_rcv_dep as string[])[0] = (orig + 1n).toString();
        });
    });

    it("FAILS when out_rcm[0] is tampered (note commitment binding rejects)", async () => {
        await expectFailsAfterTamper(input => {
            const orig = BigInt((input.out_rcm as string[])[0]);
            (input.out_rcm as string[])[0] = (orig + 1n).toString();
        });
    });

    it("FAILS when in_pk[0] is inconsistent with in_nsk[0] (pk derivation constraint)", async () => {
        // nsk stays correct; only the declared pk is forged. The circuit derives
        // pk = DerivePk(nsk) in-circuit and asserts it equals the provided in_pk.
        await expectFailsAfterTamper(input => {
            const orig = BigInt((input.in_pk as string[])[0]);
            (input.in_pk as string[])[0] = (orig + 1n).toString();
        });
    });

    it("FAILS when nullifier[0] is tampered directly (nf binding constraint)", async () => {
        // nsk and rho are correct; only the public nullifier signal is forged.
        // Circuit recomputes nf = Poseidon(TAG_NF, nk, rho, cm) and checks equality.
        await expectFailsAfterTamper(input => {
            const orig = BigInt((input.nullifier as string[])[0]);
            (input.nullifier as string[])[0] = (orig + 1n).toString();
        });
    });

    it("FAILS when in_rho[0] is tampered (nullifier mismatch + Merkle leaf change)", async () => {
        // rho feeds NoteCommitment (→ cm → leaf → Merkle) AND nullifier(nk, rho).
        // Either path alone would reject; both fire simultaneously.
        await expectFailsAfterTamper(input => {
            const orig = BigInt((input.in_rho as string[])[0]);
            (input.in_rho as string[])[0] = (orig + 1n).toString();
        });
    });

    it("FAILS when in_rcm[0] is tampered (note commitment changes leaf, Merkle rejects)", async () => {
        // rcm feeds NoteCommitment → different cm → different leaf hash →
        // Merkle proof no longer matches the tree root.
        await expectFailsAfterTamper(input => {
            const orig = BigInt((input.in_rcm as string[])[0]);
            (input.in_rcm as string[])[0] = (orig + 1n).toString();
        });
    });

    it("FAILS when out_rho[0] is tampered (output note commitment binding)", async () => {
        // rho feeds NoteCommitment in output.circom; cm_h.cm === cm rejects
        // when rho changes (distinct from the out_rcm path already tested).
        await expectFailsAfterTamper(input => {
            const orig = BigInt((input.out_rho as string[])[0]);
            (input.out_rho as string[])[0] = (orig + 1n).toString();
        });
    });

    it("FAILS when out_cv_dep[0][1] (y-coordinate) is tampered", async () => {
        await expectFailsAfterTamper(input => {
            const orig = BigInt((input.out_cv_dep as string[][])[0][1]);
            (input.out_cv_dep as string[][])[0][1] = (orig + 1n).toString();
        });
    });

    it("FAILS when out_cv_dep[1][0] (second output x-coordinate) is tampered", async () => {
        await expectFailsAfterTamper(input => {
            const orig = BigInt((input.out_cv_dep as string[][])[1][0]);
            (input.out_cv_dep as string[][])[1][0] = (orig + 1n).toString();
        });
    });

    it("FAILS when out_cv_dep[1][1] (second output y-coordinate) is tampered", async () => {
        await expectFailsAfterTamper(input => {
            const orig = BigInt((input.out_cv_dep as string[][])[1][1]);
            (input.out_cv_dep as string[][])[1][1] = (orig + 1n).toString();
        });
    });

    // ===== F2: cross-asset cancellation (asset-generator DL) =====

    it("FAILS on cross-asset cancellation V^1 + V^3 == 2·V^2", async () => {
        // HashToAssetGen is circomlib Pedersen over 72 bits ⇒ a single segment
        // ⇒ V^a = m(a)·BASE[0] for a publicly computable m(·). m is ~2^85 and
        // affine in the low nibbles of asset_id, so m(1) + m(3) == 2·m(2)
        // exactly and the Edwards point balance is satisfied by spending X of
        // asset 1 plus X of asset 3 to mint 2X of asset 2. PerAssetValueBalance
        // rejects it: assets are compared as field elements, not as points.
        const nsk = 11n;
        const X = 1000n;

        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(X, nsk, 1n, 1n), nsk);
        let inB = tx.insert(tree, tx.note(X, nsk, 2n, 3n), nsk);
        const root = tree.root();
        inA = tx.finalize(tree, inA);
        inB = tx.finalize(tree, inB);

        // Sanity: the point balance really is satisfied by this forgery.
        const J = tx.J;
        const lhs = J.addPoint(
            J.mulPointEscalar(J.hashToAssetGen(1n), X),
            J.mulPointEscalar(J.hashToAssetGen(3n), X),
        );
        const rhs = J.mulPointEscalar(J.hashToAssetGen(2n), 2n * X);
        expect(lhs[0]).to.equal(rhs[0]);
        expect(lhs[1]).to.equal(rhs[1]);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB],
            outputs: [tx.note(2n * X, nsk, 9n, 2n), tx.note(0n, nsk, 11n, 2n)],
            merkleRoot: root,
        });
        await expectWitnessFails(circuit, input);
    });

    it("FAILS when an output asset is swapped for one of equal total value", async () => {
        // Straight asset substitution: same numbers, wrong colour.
        const nsk = 11n;
        const { root, inA, inB } = twoRealInputs([100n, 50n], nsk);
        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB],
            outputs: [tx.note(150n, nsk, 9n, ASSET_B), tx.note(0n, nsk, 11n, ASSET)],
            merkleRoot: root,
        });
        await expectWitnessFails(circuit, input);
    });

    it("multi-asset: two assets conserved independently", async () => {
        // Per-asset conservation, not aggregate: 100 of ASSET in → 100 of
        // ASSET out, 50 of ASSET_B in → 50 of ASSET_B out.
        const nsk = 11n;
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(100n, nsk, 1n, ASSET), nsk);
        let inB = tx.insert(tree, tx.note(50n, nsk, 2n, ASSET_B), nsk);
        const root = tree.root();
        inA = tx.finalize(tree, inA);
        inB = tx.finalize(tree, inB);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB],
            outputs: [tx.note(100n, nsk, 9n, ASSET), tx.note(50n, nsk, 11n, ASSET_B)],
            merkleRoot: root,
        });
        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    // ===== F3: nullifier binds cm (faerie-gold defense, all inserters) =====

    it("nullifier separates two notes that share (nk, rho)", () => {
        // The faerie-gold shape: a dust note planted at a victim's pk reusing
        // the rho of a note they already hold. rho for transact outputs is
        // publicly derivable from nullifier[0], and the deposit path
        // (tree_update_batch's cms[]) constrains no rho at all, so rho alone
        // is not a safe nullifier key. cm in the preimage separates them.
        const nsk = 11n;
        const rho = 42n;
        const real = tx.note(1000n, nsk, rho);
        const dust = tx.note(1n, nsk, rho);
        const cmReal = commit(tx.P, real);
        const cmDust = commit(tx.P, dust);
        expect(cmReal).to.not.equal(cmDust);
        expect(nullifier(tx.P, nsk, rho, cmReal)).to.not.equal(
            nullifier(tx.P, nsk, rho, cmDust),
        );
    });

    it("FAILS when nullifier omits cm from the preimage", async () => {
        const nsk = 11n;
        const { root, inA, inB } = twoRealInputs([100n, 50n], nsk);
        // Pre-fix derivation: Poseidon(TAG_NF, nk, rho), no cm.
        inA.nf = tx.P.hash([2n, deriveNk(tx.P, nsk), inA.rho]);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB],
            outputs: [tx.note(75n, nsk, 9n), tx.note(75n, nsk, 11n)],
            merkleRoot: root,
        });
        await expectWitnessFails(circuit, input);
    });

    // ===== F1: output rho uniqueness (faerie-gold defense) =====

    it("output rho is bound to Poseidon(TAG_RHO, nullifier[0], out_index)", async () => {
        const nsk = 11n;
        const { root, inA, inB } = twoRealInputs([100n, 50n], nsk);
        const outA = tx.note(75n, nsk, 9n);
        const outB = tx.note(75n, nsk, 11n);
        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        // build() overrides note.rho with the Orchard-style derivation.
        const nf0 = inA.nf;
        expect((input.out_rho as string[])[0]).to.equal(buildRho(tx.P, nf0, 0).toString());
        expect((input.out_rho as string[])[1]).to.equal(buildRho(tx.P, nf0, 1).toString());
        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    it("FAILS (faerie-gold) when two outputs share a rho, even with cm rebound", async () => {
        // Force both outputs to the SAME rho and recompute out_cm[1] so the cm
        // binding still passes — isolating the new DeriveRho equality constraint,
        // which rejects because out_rho[1] != Poseidon(TAG_RHO, nullifier[0], 1).
        const nsk = 11n;
        const { root, inA, inB } = twoRealInputs([100n, 50n], nsk);
        const outA = tx.note(75n, nsk, 9n);
        const outB = tx.note(75n, nsk, 11n);
        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        const sharedRho = (input.out_rho as string[])[0];
        (input.out_rho as string[])[1] = sharedRho;
        // Rebind out_cm[1] to the shared rho so cm binding is not what fails.
        // cv / cv_dep are rho-independent, so only DeriveRho can reject here.
        (input.out_cm as string[])[1] = commit(tx.P, {
            asset: outB.asset, value: outB.value, pk: outB.pk,
            rho: BigInt(sharedRho), rcm: outB.rcm,
        }).toString();
        await expectWitnessFails(circuit, input);
    });
});
