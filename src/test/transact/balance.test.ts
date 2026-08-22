// Value conservation and dummy / padding slot semantics.
//
// The circuit balances as points rather than scalars: Σ in_cv + public_in·V^public
// must equal Σ out_cv + public_out·V^public. Each case is a shape that must
// balance or one that must not.

import { expect } from "chai";

import { commit, dummyOutput, nullifier, type Note } from "../helpers";
import { expectAccepts, expectWitnessFails } from "../lib/expect";
import { ALICE_NSK, BOB_NSK, MALLORY_NSK, TIMEOUT_CIRCUIT } from "../lib/constants";
import { DEFAULT_ASSET as ASSET } from "../lib/transact";
import { useTransactCircuit } from "./setup";

describe("transact_2x2 / value balance", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    it("internal 2-in-2-out balanced same asset", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.twoRealInputs([100n, 50n], ALICE_NSK);
        await expectAccepts(circuit, tx.build({
            inputs,
            outputs: [tx.note(30n, BOB_NSK, 100n), tx.note(120n, ALICE_NSK, 200n)],
            merkleRoot: root,
        }));
    });

    it("deposit: 2 dummy inputs, 1 real output, public_in > 0", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.allDummyInputs();
        await expectAccepts(circuit, tx.build({
            publicIn: 1000n,
            inputs,
            outputs: [tx.note(1000n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            merkleRoot: root,
        }));
    });

    it("withdraw: 1 real input, 1 dummy input, public_out > 0", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.oneRealOneDummy(500n, ALICE_NSK);
        await expectAccepts(circuit, tx.build({
            publicOut: 300n,
            inputs,
            outputs: [tx.note(200n, ALICE_NSK, 50n), tx.note(0n, ALICE_NSK, 60n)],
            merkleRoot: root,
        }));
    });

    it("simultaneous deposit + withdraw (both public_in and public_out > 0) accepted if balanced", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.oneRealOneDummy(100n, ALICE_NSK);
        await expectAccepts(circuit, tx.build({
            publicIn: 50n, publicOut: 70n,
            inputs,
            outputs: [tx.note(80n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            merkleRoot: root,
        }));
    });

    it("all-dummy zero tx is accepted", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.allDummyInputs();
        await expectAccepts(circuit, tx.build({
            publicAssetId: 0n,
            inputs,
            outputs: [dummyOutput(), dummyOutput()],
            merkleRoot: root,
        }));
    });

    it("FAILS on unbalanced values", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.twoRealInputs([100n, 50n], ALICE_NSK);
        await expectWitnessFails(circuit, tx.build({
            inputs,
            outputs: [tx.note(10n, ALICE_NSK, 9n), tx.note(10n, ALICE_NSK, 11n)],
            merkleRoot: root,
        }), "150 in must not balance against 20 out");
    });

    it("FAILS when dummy input has nonzero value", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.allDummyInputs();
        inputs[0].value = 50n;
        await expectWitnessFails(circuit, tx.build({
            publicIn: 50n,
            inputs,
            outputs: [tx.note(50n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            merkleRoot: root,
        }), "DummyZeroValue must pin a dummy slot's value to 0");
    });

    it("FAILS on wrong nsk for given pk", async () => {
        // The note is in the tree; only the claimed spending key is wrong.
        // pk = DerivePk(nsk) is recomputed in-circuit.
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

        await expectWitnessFails(circuit, tx.build({
            inputs: [forged, inB],
            outputs: [tx.note(100n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            merkleRoot: root,
        }), "pk === DerivePk(nsk) must reject a mismatched key");
    });

    // ===== dummy and padding slot semantics =====
    //
    // A dummy INPUT bypasses the key and Merkle checks and may carry arbitrary
    // fields; value = 0 keeps it balance-neutral. A padding OUTPUT is a real
    // value-0 note, so its commitment is still constrained, and asset_id = 0 is
    // rejected to prevent minting a ghost note.

    it("dummy input with garbage non-zero pk/rho/rcm still accepted (key + Merkle bypassed)", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.oneRealOneDummy(100n, ALICE_NSK);
        const dummy = inputs[1];
        dummy.pk = 0xbadc0den;
        dummy.rcm = 0xdeadn;
        dummy.pathElements[0][0] = 12345n;
        // nf binds cm, and cm covers pk/rcm — re-seal after mutating them.
        dummy.cm = commit(tx.P, dummy);
        dummy.nf = nullifier(tx.P, dummy.nsk, dummy.rho, dummy.cm);

        await expectAccepts(circuit, tx.build({
            inputs,
            outputs: [tx.note(100n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            merkleRoot: root,
        }));
    });

    it("dummy with arbitrary asset_id and rcv accepted (value=0 ⇒ no balance contribution)", async () => {
        // asset feeds packed_av inside cm, and the generator is still computed,
        // then multiplied by 0 to give the identity.
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.oneRealOneDummy(100n, ALICE_NSK);
        const dummy = inputs[1];
        dummy.asset = 12345n;
        dummy.rcv = 0n;
        dummy.cm = commit(tx.P, dummy);
        dummy.nf = nullifier(tx.P, dummy.nsk, dummy.rho, dummy.cm);

        await expectAccepts(circuit, tx.build({
            inputs,
            outputs: [tx.note(100n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            merkleRoot: root,
        }));
    });

    it("padding output: value=0 note with a different asset accepted", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.oneRealOneDummy(100n, ALICE_NSK);
        // Real value-0 note with a real cm. asset_id must be non-zero; value = 0
        // makes value·gen the identity, so the slot is balance-neutral.
        const padding: Note = { asset: 999n, value: 0n, pk: 0n, rho: 0n, rcm: 0n, rcv: 0n, rcvDep: 0n };
        await expectAccepts(circuit, tx.build({
            inputs,
            outputs: [tx.note(100n, ALICE_NSK, 9n), padding],
            merkleRoot: root,
        }));
    });

    it("FAILS when a padding output has asset_id == 0 (ghost-note defense, no dummy bypass)", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.oneRealOneDummy(100n, ALICE_NSK);
        const ghost: Note = { asset: 0n, value: 0n, pk: 0n, rho: 0n, rcm: 0n, rcv: 0n, rcvDep: 0n };
        await expectWitnessFails(circuit, tx.build({
            inputs,
            outputs: [tx.note(100n, ALICE_NSK, 9n), ghost],
            merkleRoot: root,
        }), "asset_id = 0 must be rejected even in a padding slot");
    });

    it("FAILS when a non-dummy input has asset_id == 0", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.twoRealInputs([100n, 50n], ALICE_NSK, 0n);
        await expectWitnessFails(circuit, tx.build({
            inputs,
            outputs: [tx.note(75n, ALICE_NSK, 9n), tx.note(75n, ALICE_NSK, 11n)],
            merkleRoot: root,
        }), "asset_id = 0 must be rejected on the input side");
    });

    it("FAILS when a non-dummy output has asset_id == 0", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.oneRealOneDummy(100n, ALICE_NSK);
        await expectWitnessFails(circuit, tx.build({
            inputs,
            outputs: [tx.note(100n, ALICE_NSK, 9n, 0n), tx.note(0n, ALICE_NSK, 11n)],
            merkleRoot: root,
        }), "asset_id = 0 must be rejected on the output side");
    });

    it("spends at leaf indices covering every quaternary path_index slot", async () => {
        const { tx, circuit } = ctx;
        const tree = tx.newTree();
        const planted = [];
        for (let i = 0; i < 21; i++) {
            planted.push(tx.insert(tree, tx.note(10n, ALICE_NSK, BigInt(i + 1)), ALICE_NSK));
        }
        const root = tree.root();
        const inA = tx.finalize(tree, planted[17]);
        const inB = tx.finalize(tree, planted[20]);

        // 17 and 20 were picked so the path digits differ at both low levels.
        expect(inA.pathIndices[0]).to.equal(1);
        expect(inB.pathIndices[1]).to.equal(1);

        await expectAccepts(circuit, tx.build({
            inputs: [inA, inB],
            outputs: [tx.note(5n, ALICE_NSK, 9n), tx.note(15n, ALICE_NSK, 11n)],
            merkleRoot: root,
        }));
    });

    it("FAILS on a tampered Merkle path", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.twoRealInputs([100n, 50n], ALICE_NSK);
        inputs[0].pathElements[3][0] = inputs[0].pathElements[3][0] + 1n;
        await expectWitnessFails(circuit, tx.build({
            inputs,
            outputs: [tx.note(75n, ALICE_NSK, 9n), tx.note(75n, ALICE_NSK, 11n)],
            merkleRoot: root,
        }), "a perturbed sibling must not recompute to the declared root");
    });

    it("FAILS on cross-asset rejection (in=A,A out=B,B same scalar sums)", async () => {
        // Point balance is per asset, so matching scalar totals across different
        // assets must not pass.
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.twoRealInputs([100n, 50n], ALICE_NSK, ASSET);
        await expectWitnessFails(circuit, tx.build({
            inputs,
            outputs: [tx.note(75n, ALICE_NSK, 9n, 99n), tx.note(75n, ALICE_NSK, 11n, 99n)],
            merkleRoot: root,
        }), "per-asset conservation must reject a matched scalar total");
    });
});
