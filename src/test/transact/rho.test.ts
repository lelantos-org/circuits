// Note-identity defences against faerie-gold notes, tracked as audit findings
// F1 and F3.
//
// F1 — output rho uniqueness. Output rho is forced to
//      rho = Poseidon(TAG_RHO, nullifier[0], out_index), so two outputs of one
//      transaction cannot share a rho.
//
// F3 — the nullifier binds cm. Output rho is publicly derivable from
//      nullifier[0], and the deposit path (tree_update_batch's cms[])
//      constrains no rho, so rho alone is not a safe nullifier key. Without cm
//      in the preimage, a dust note planted at a victim's pk reusing a rho they
//      already hold produces a colliding nullifier.

import { expect } from "chai";

import { buildRho, commit, deriveNk, nullifier, TAG_NF } from "../helpers";
import { expectAccepts, expectWitnessFails } from "../lib/expect";
import { ALICE_NSK, TIMEOUT_CIRCUIT } from "../lib/constants";
import { useTransactCircuit } from "./setup";

describe("transact_2x2 / rho and nullifier binding", function () {
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
        const { root, inputs } = tx.twoRealInputs([100n, 50n], ALICE_NSK);
        // The pre-fix derivation: Poseidon(TAG_NF, nk, rho), no cm.
        inputs[0].nf = tx.P.hash([TAG_NF, deriveNk(tx.P, ALICE_NSK), inputs[0].rho]);

        await expectWitnessFails(circuit, tx.build({
            inputs,
            outputs: [tx.note(75n, ALICE_NSK, 9n), tx.note(75n, ALICE_NSK, 11n)],
            merkleRoot: root,
        }), "the nullifier must not verify without cm in the preimage");
    });

    it("output rho is bound to Poseidon(TAG_RHO, nullifier[0], out_index)", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.twoRealInputs([100n, 50n], ALICE_NSK);
        const input = tx.build({
            inputs,
            outputs: [tx.note(75n, ALICE_NSK, 9n), tx.note(75n, ALICE_NSK, 11n)],
            merkleRoot: root,
        });
        // build() overrides whatever rho the caller's notes carried.
        const nf0 = inputs[0].nf;
        expect(input.out_rho[0]).to.equal(buildRho(tx.P, nf0, 0).toString());
        expect(input.out_rho[1]).to.equal(buildRho(tx.P, nf0, 1).toString());
        await expectAccepts(circuit, input);
    });

    it("FAILS when two outputs share a rho, even with cm rebound", async () => {
        // Recomputing out_cm[1] against the shared rho keeps the commitment
        // binding satisfied, leaving DeriveRho as the only constraint that can
        // reject. cv and cv_dep are rho-independent.
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.twoRealInputs([100n, 50n], ALICE_NSK);
        const outB = tx.note(75n, ALICE_NSK, 11n);
        const input = tx.build({
            inputs,
            outputs: [tx.note(75n, ALICE_NSK, 9n), outB],
            merkleRoot: root,
        });

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
