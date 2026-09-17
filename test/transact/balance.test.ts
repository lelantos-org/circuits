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

    it("deposit: one real input carried through, public_in > 0", async () => {
        // The circuit requires at least one real input slot (see the all-dummy
        // case below), so the deposit carries a real note through.
        const { tx, circuit } = ctx;
        await expectAccepts(circuit, tx.spend(
            tx.oneRealOneDummy(1n, ALICE_NSK),
            [tx.note(1001n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            { publicIn: 1000n },
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

    it("simultaneous deposit + withdraw (both public_in and public_out > 0) accepted if balanced", async () => {
        const { tx, circuit } = ctx;
        await expectAccepts(circuit, tx.spend(
            tx.oneRealOneDummy(100n, ALICE_NSK),
            [tx.note(80n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            { publicIn: 50n, publicOut: 70n },
        ));
    });

    it("FAILS on an all-dummy transaction", async () => {
        // With every slot dummy, every Merkle check is skipped and `merkle_root`
        // is a PolyEval coefficient no constraint pins. `PolyEval` is affine in
        // each coefficient and the prover reads `z` before choosing a witness, so
        // one free coefficient is one linear equation in one unknown: solving it
        // matches the contract's `y` with a proof of an unrelated transaction.
        //
        // `MASP.withdraw` and `MASP.transfer` both require `publicIn == 0` and
        // shielding goes through the deposit escrow, so an all-dummy transact is
        // a no-op and rejecting it removes no valid use.
        const { tx, circuit } = ctx;
        await expectWitnessFails(
            circuit,
            tx.spend(
                tx.allDummyInputs(),
                [dummyOutput(tx.P, 0), dummyOutput(tx.P, 1)],
                { publicAssetId: 0n },
            ),
            "an all-dummy transaction leaves merkle_root unpinned and must be rejected",
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
        const { tx, circuit } = ctx;
        const scenario = tx.allDummyInputs();
        scenario.inputs[0].value = 50n;
        await expectWitnessFails(circuit, tx.spend(
            scenario,
            [tx.note(50n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            { publicIn: 50n },
        ), "DummyZeroValue must pin a dummy slot's value to 0");
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

        await expectWitnessFails(circuit, tx.spend(
            { root, inputs: [forged, inB] },
            [tx.note(100n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
        ), "pk === DerivePk(nsk) must reject a mismatched key");
    });

    // ===== dummy and padding slot semantics =====
    //
    // A dummy INPUT bypasses the key and Merkle checks and may carry arbitrary
    // fields; value = 0 keeps it balance-neutral. A padding OUTPUT is a real
    // value-0 note, so its commitment is still constrained, and asset_id = 0 is
    // rejected to prevent minting a ghost note.

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

    it("dummy with arbitrary asset_id and rcv accepted (value=0 ⇒ no balance contribution)", async () => {
        // asset feeds packed_av inside cm; the generator is computed and
        // multiplied by 0, giving the identity.
        const { tx, circuit } = ctx;
        const scenario = tx.oneRealOneDummy(100n, ALICE_NSK);
        const dummy = scenario.inputs[1];
        dummy.asset = 12345n;
        dummy.rcv = 0n;
        dummy.cm = commit(tx.P, dummy);
        dummy.nf = nullifier(tx.P, dummy.nsk, dummy.rho, dummy.cm);

        await expectAccepts(circuit, tx.spend(
            scenario,
            [tx.note(100n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
        ));
    });

    it("padding output: value=0 note with a different asset accepted", async () => {
        const { tx, circuit } = ctx;
        // Real value-0 note with a real cm. asset_id must be non-zero; value = 0
        // makes value·gen the identity, so the slot is balance-neutral.
        const padding: Note = { asset: 999n, value: 0n, pk: 0n, rho: 0n, rcm: 0n, rcv: 0n, rcvDep: 0n };
        await expectAccepts(circuit, tx.spend(
            tx.oneRealOneDummy(100n, ALICE_NSK),
            [tx.note(100n, ALICE_NSK, 9n), padding],
        ));
    });

    it("FAILS when a padding output has asset_id == 0 (ghost-note defense, no dummy bypass)", async () => {
        const { tx, circuit } = ctx;
        const ghost: Note = { asset: 0n, value: 0n, pk: 0n, rho: 0n, rcm: 0n, rcv: 0n, rcvDep: 0n };
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
        // Point balance is per asset, so matching scalar totals across different
        // assets must not pass.
        const { tx, circuit } = ctx;
        await expectWitnessFails(circuit, tx.spend(
            tx.twoRealInputs([100n, 50n], ALICE_NSK, ASSET),
            [tx.note(75n, ALICE_NSK, 9n, 99n), tx.note(75n, ALICE_NSK, 11n, 99n)],
        ), "per-asset conservation must reject a matched scalar total");
    });
});
