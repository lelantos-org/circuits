// Note-identity defences against faerie-gold notes.
//
// Output rho is forced to Poseidon(TAG_RHO, nullifier[0], out_index), so two
// outputs of one transaction cannot share a rho.
//
// The nullifier binds cm: the deposit path (tree_update_batch's cms[])
// constrains no rho, so without cm in the preimage a dust note sent to a
// victim's pk with a rho the victim already holds produces a colliding
// nullifier.

import { expect } from "chai";

import { buildRho, commit, deriveNk, nullifier, TAG_NF } from "../helpers";
import { expectAccepts, expectWitnessFails } from "../lib/expect";
import { ALICE_NSK, TIMEOUT_CIRCUIT } from "../lib/constants";
import { useTransactCircuit } from "./setup";

describe("transact_4x6 / rho and nullifier binding", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    it("nullifier separates two notes that share (nk, rho)", () => {
        const { tx } = ctx;
        const rho = 42n;
        const real = tx.note(1000n, ALICE_NSK, rho);
        const dust = tx.note(1n, ALICE_NSK, rho);
        const cmReal = commit(tx.P, real);
        const cmDust = commit(tx.P, dust);
        expect(cmReal).to.not.equal(cmDust);
        expect(nullifier(tx.P, ALICE_NSK, rho, cmReal)).to.not.equal(
            nullifier(tx.P, ALICE_NSK, rho, cmDust),
        );
    });

    it("FAILS when the nullifier omits cm from the preimage", async () => {
        const { tx, circuit } = ctx;
        const scenario = tx.twoRealInputs([100n, 50n], ALICE_NSK);
        const [inA] = scenario.inputs;
        // Derivation without cm: Poseidon(TAG_NF, nk, rho).
        inA.nf = tx.P.hash([TAG_NF, deriveNk(tx.P, ALICE_NSK), inA.rho]);

        await expectWitnessFails(circuit, tx.spend(
            scenario,
            [tx.note(75n, ALICE_NSK, 9n), tx.note(75n, ALICE_NSK, 11n)],
        ), "the nullifier must not verify without cm in the preimage");
    });

    it("output rho is bound to Poseidon(TAG_RHO, nullifier[0], out_index)", async () => {
        const { tx, circuit } = ctx;
        const scenario = tx.twoRealInputs([100n, 50n], ALICE_NSK);
        const input = tx.spend(scenario, [tx.note(75n, ALICE_NSK, 9n), tx.note(75n, ALICE_NSK, 11n)]);
        // build() overrides whatever rho the caller's notes carried.
        const nf0 = scenario.inputs[0].nf;
        expect(input.out_rho[0]).to.equal(buildRho(tx.P, nf0, 0).toString());
        expect(input.out_rho[1]).to.equal(buildRho(tx.P, nf0, 1).toString());
        await expectAccepts(circuit, input);
    });

    it("FAILS when two outputs share a rho, even with cm rebound", async () => {
        // out_cm[1] is recomputed against the shared rho, so the commitment
        // binding holds and only DeriveRho can reject.
        const { tx, circuit } = ctx;
        const outB = tx.note(75n, ALICE_NSK, 11n);
        const input = tx.spend(tx.twoRealInputs([100n, 50n], ALICE_NSK), [tx.note(75n, ALICE_NSK, 9n), outB]);

        const sharedRho = input.out_rho[0];
        input.out_rho[1] = sharedRho;
        input.out_cm[1] = commit(tx.P, {
            asset: outB.asset, value: outB.value, pk: outB.pk,
            rho: BigInt(sharedRho), rcm: outB.rcm,
        }).toString();

        await expectWitnessFails(
            circuit,
            input,
            "out_rho[1] !== Poseidon(TAG_RHO, nullifier[0], 1) must reject",
        );
    });
});
