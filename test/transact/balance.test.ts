// Value conservation and dummy / padding slot semantics. Per asset id,
// Σ in_value = Σ out_value, plus public_out for the id the public bucket names.

import { expect } from "chai";

import { commit, dummyOutput, nullifier, type Note } from "../helpers";
import { expectAccepts, expectWitnessFails } from "../lib/expect";
import { ALICE_NSK, BOB_NSK, MALLORY_NSK, TIMEOUT_CIRCUIT } from "../lib/constants";
import { DEFAULT_ASSET as ASSET } from "../lib/transact";
import { useTransactCircuit } from "./setup";

describe("transact_4x6 / value balance", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    it("internal 2-in-2-out balanced same asset", async () => {
        const { tx, circuit } = ctx;
        await expectAccepts(circuit, tx.spend(
            tx.twoRealInputs([100n, 50n], ALICE_NSK),
            [tx.note(30n, BOB_NSK, 100n), tx.note(120n, ALICE_NSK, 200n)],
        ));
    });

    it("withdraw: 1 real input, 1 dummy input, public_out > 0", async () => {
        const { tx, circuit } = ctx;
        await expectAccepts(circuit, tx.spend(
            tx.oneRealOneDummy(500n, ALICE_NSK),
            [tx.note(200n, ALICE_NSK, 50n), tx.note(0n, ALICE_NSK, 60n)],
            { publicOut: 300n },
        ));
    });

    // ===== the transparent bucket =====
    //
    // `public_out == 0` forces `public_asset_id == 0`, so a shielded transfer
    // does not publish the id it moves.

    it("a transfer names no public asset", async () => {
        const { tx, circuit } = ctx;
        const w = tx.spend(
            tx.twoRealInputs([100n, 50n], ALICE_NSK),
            [tx.note(30n, BOB_NSK, 100n), tx.note(120n, ALICE_NSK, 200n)],
        );
        expect(w.public_out).to.equal("0");
        expect(w.public_asset_id, "the builder's default for a transfer").to.equal("0");
        await expectAccepts(circuit, w);
    });

    it("FAILS when a transfer names the asset it moves", async () => {
        // Balanced, and public_out is 0, so only the bucket constraint rejects.
        const { tx, circuit } = ctx;
        await expectWitnessFails(circuit, tx.spend(
            tx.twoRealInputs([100n, 50n], ALICE_NSK),
            [tx.note(30n, BOB_NSK, 100n), tx.note(120n, ALICE_NSK, 200n)],
            { publicAssetId: ASSET },
        ), "public_out == 0 must force public_asset_id == 0");
    });

    it("FAILS when a transfer names an asset nothing in it carries", async () => {
        const { tx, circuit } = ctx;
        await expectWitnessFails(circuit, tx.spend(
            tx.twoRealInputs([100n, 50n], ALICE_NSK),
            [tx.note(30n, BOB_NSK, 100n), tx.note(120n, ALICE_NSK, 200n)],
            { publicAssetId: 4242n },
        ), "public_out == 0 must force public_asset_id == 0, whatever id is named");
    });

    it("FAILS on a withdrawal under asset id 0", async () => {
        // Needs no constraint of its own: no real note carries id 0, so nothing
        // funds the withdrawal.
        const { tx, circuit } = ctx;
        await expectWitnessFails(circuit, tx.spend(
            tx.oneRealOneDummy(500n, ALICE_NSK),
            [tx.note(200n, ALICE_NSK, 50n), tx.note(0n, ALICE_NSK, 60n)],
            { publicOut: 300n, publicAssetId: 0n },
        ), "a withdrawal under id 0 must be unbalanced");
    });

    it("FAILS on a withdrawal of an asset no input carries", async () => {
        const { tx, circuit } = ctx;
        await expectWitnessFails(circuit, tx.spend(
            tx.oneRealOneDummy(500n, ALICE_NSK),
            [tx.note(500n, ALICE_NSK, 50n)],
            { publicOut: 300n, publicAssetId: 99n },
        ), "nothing funds 300 units of asset 99");
    });

    it("FAILS on an all-dummy transaction", async () => {
        // With every slot dummy, every Merkle check is skipped and nothing but
        // the coefficient digest reads `merkle_root`.
        const { tx, circuit } = ctx;
        await expectWitnessFails(
            circuit,
            tx.spend(
                tx.allDummyInputs(),
                [dummyOutput(tx.P, 0), dummyOutput(tx.P, 1)],
                { publicAssetId: 0n },
            ),
            "an all-dummy transaction opens no leaf under merkle_root and must be rejected",
        );
    });

    it("FAILS on unbalanced values", async () => {
        const { tx, circuit } = ctx;
        await expectWitnessFails(circuit, tx.spend(
            tx.twoRealInputs([100n, 50n], ALICE_NSK),
            [tx.note(10n, ALICE_NSK, 9n), tx.note(10n, ALICE_NSK, 11n)],
        ), "150 in must not balance against 20 out");
    });

    it("FAILS when dummy input has nonzero value", async () => {
        // The dummy is re-sealed and the outputs balance against 100 + 50, so
        // only DummyZeroValue rejects: a dummy proves no membership, so a
        // nonzero value would mint.
        const { tx, circuit } = ctx;
        const scenario = tx.oneRealOneDummy(100n, ALICE_NSK);
        const dummy = scenario.inputs[1];
        dummy.asset = ASSET;
        dummy.value = 50n;
        dummy.cm = commit(tx.P, dummy);
        dummy.nf = nullifier(tx.P, dummy.nsk, dummy.rho, dummy.cm);
        await expectWitnessFails(circuit, tx.spend(
            scenario,
            [tx.note(150n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
        ), "DummyZeroValue must pin a dummy slot's value to 0");
    });

    it("FAILS on wrong nsk for given pk", async () => {
        // The note is in the tree; only the claimed spending key is wrong.
        const { tx, circuit } = ctx;
        const tree = tx.newTree();
        const n = tx.note(100n, ALICE_NSK, 1n);
        const cm = commit(tx.P, n);
        const idx = tree.insert(cm);
        let inB = tx.insert(tree, tx.note(0n, ALICE_NSK, 2n), ALICE_NSK);
        const root = tree.root();
        inB = tx.finalize(tree, inB);
        const proof = tree.proof(idx);

        const forged = {
            ...n, nsk: MALLORY_NSK, cm,
            nf: nullifier(tx.P, MALLORY_NSK, n.rho, cm),
            leafIndex: idx,
            pathElements: proof.pathElements,
            pathIndices: proof.pathIndices,
            isDummy: false,
        };

        await expectWitnessFails(circuit, tx.spend(
            { root, inputs: [forged, inB] },
            [tx.note(100n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
        ), "pk === DerivePk(nsk) must reject a mismatched key");
    });

    // ===== dummy and padding slot semantics =====
    //
    // A dummy input bypasses the key and Merkle checks and may carry arbitrary
    // fields; value = 0 keeps it balance-neutral. A padding output is a real
    // value-0 note: its commitment is constrained and asset_id = 0 is rejected.

    it("dummy input with garbage non-zero pk/rho/rcm still accepted (key + Merkle bypassed)", async () => {
        const { tx, circuit } = ctx;
        const scenario = tx.oneRealOneDummy(100n, ALICE_NSK);
        const dummy = scenario.inputs[1];
        dummy.pk = 0xbadc0den;
        dummy.rcm = 0xdeadn;
        dummy.pathElements[0][0] = 12345n;
        // nf binds cm, and cm covers pk/rcm — re-seal after mutating them.
        dummy.cm = commit(tx.P, dummy);
        dummy.nf = nullifier(tx.P, dummy.nsk, dummy.rho, dummy.cm);

        await expectAccepts(circuit, tx.spend(
            scenario,
            [tx.note(100n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
        ));
    });

    it("dummy with arbitrary asset_id accepted (value=0 ⇒ no balance contribution)", async () => {
        const { tx, circuit } = ctx;
        const scenario = tx.oneRealOneDummy(100n, ALICE_NSK);
        const dummy = scenario.inputs[1];
        dummy.asset = 12345n;
        dummy.cm = commit(tx.P, dummy);
        dummy.nf = nullifier(tx.P, dummy.nsk, dummy.rho, dummy.cm);

        await expectAccepts(circuit, tx.spend(
            scenario,
            [tx.note(100n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
        ));
    });

    it("padding output: value=0 note with a different asset accepted", async () => {
        const { tx, circuit } = ctx;
        const padding: Note = { asset: 999n, value: 0n, pk: 0n, rho: 0n, rcm: 0n };
        await expectAccepts(circuit, tx.spend(
            tx.oneRealOneDummy(100n, ALICE_NSK),
            [tx.note(100n, ALICE_NSK, 9n), padding],
        ));
    });

    it("FAILS when a padding output has asset_id == 0 (ghost-note defense, no dummy bypass)", async () => {
        const { tx, circuit } = ctx;
        const ghost: Note = { asset: 0n, value: 0n, pk: 0n, rho: 0n, rcm: 0n };
        await expectWitnessFails(circuit, tx.spend(
            tx.oneRealOneDummy(100n, ALICE_NSK),
            [tx.note(100n, ALICE_NSK, 9n), ghost],
        ), "asset_id = 0 must be rejected even in a padding slot");
    });

    it("FAILS when a non-dummy input has asset_id == 0", async () => {
        const { tx, circuit } = ctx;
        await expectWitnessFails(circuit, tx.spend(
            tx.twoRealInputs([100n, 50n], ALICE_NSK, 0n),
            [tx.note(75n, ALICE_NSK, 9n), tx.note(75n, ALICE_NSK, 11n)],
        ), "asset_id = 0 must be rejected on the input side");
    });

    it("FAILS when a non-dummy output has asset_id == 0", async () => {
        const { tx, circuit } = ctx;
        await expectWitnessFails(circuit, tx.spend(
            tx.oneRealOneDummy(100n, ALICE_NSK),
            [tx.note(100n, ALICE_NSK, 9n, 0n), tx.note(0n, ALICE_NSK, 11n)],
        ), "asset_id = 0 must be rejected on the output side");
    });

    it("spends at leaf indices covering every quaternary path_index slot", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs: planted } = tx.plant(
            Array.from({ length: 21 }, (_, i) => tx.note(10n, ALICE_NSK, BigInt(i + 1))),
            ALICE_NSK,
        );
        const inA = planted[17];
        const inB = planted[20];

        // 17 and 20 differ in their path digits at both low levels.
        expect(inA.pathIndices[0]).to.equal(1);
        expect(inB.pathIndices[1]).to.equal(1);

        await expectAccepts(circuit, tx.spend(
            { root, inputs: [inA, inB] },
            [tx.note(5n, ALICE_NSK, 9n), tx.note(15n, ALICE_NSK, 11n)],
        ));
    });

    it("FAILS on a tampered Merkle path", async () => {
        const { tx, circuit } = ctx;
        const scenario = tx.twoRealInputs([100n, 50n], ALICE_NSK);
        scenario.inputs[0].pathElements[3][0] += 1n;
        await expectWitnessFails(circuit, tx.spend(
            scenario,
            [tx.note(75n, ALICE_NSK, 9n), tx.note(75n, ALICE_NSK, 11n)],
        ), "a perturbed sibling must not recompute to the declared root");
    });

    it("FAILS on cross-asset rejection (in=A,A out=B,B same scalar sums)", async () => {
        const { tx, circuit } = ctx;
        await expectWitnessFails(circuit, tx.spend(
            tx.twoRealInputs([100n, 50n], ALICE_NSK, ASSET),
            [tx.note(75n, ALICE_NSK, 9n, 99n), tx.note(75n, ALICE_NSK, 11n, 99n)],
        ), "per-asset conservation must reject a matched scalar total");
    });
});
