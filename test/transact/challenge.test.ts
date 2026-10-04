// The Fiat-Shamir challenge `z` is unconstrained in the circuit.
//
// `Transact` takes `z` as a public input and `PolyEval` emits y = Σ c[k]·z^k at
// any supplied challenge. Soundness requires the verifier to recompute `z` from
// calldata (`PubInputs.sol :: _finalizeTransactRaw`) and compare it with the
// public signal. The recomputation must never yield z = 1, where Horner reduces
// to a plain sum and layouts that differ by a transposition give the same `y`.

import { expect } from "chai";

import {
    BN254_FR,
    coeffs,
    hornerEval,
    type Field,
    type TransactWitnessBundle,
} from "../helpers";
import { expectWitnessFails, expectWitnessY } from "../lib/expect";
import { ALICE_NSK, TIMEOUT_CIRCUIT } from "../lib/constants";
import { TxBuilder } from "../lib/transact";
import { useTransactCircuit } from "./setup";

/** The `balanced()` shape, with the challenge left for `witnessAt` to set. */
function buildBase(tx: TxBuilder): TransactWitnessBundle {
    const input = tx.spend(
        tx.twoRealInputs([100n, 50n], ALICE_NSK),
        [tx.note(75n, ALICE_NSK, 9n), tx.note(75n, ALICE_NSK, 11n)],
        { z: 0n },
    );
    input.recipient_address = "12345";
    input.chain_id = "67890";
    return input;
}

/**
 * The base at a caller-chosen challenge. `build` only stores `z` and nothing
 * else in the bundle derives from it, so one built base serves every challenge.
 */
function witnessAt(base: TransactWitnessBundle, z: Field): TransactWitnessBundle {
    return { ...base, z: z.toString() };
}

describe("transact_4x6 / Fiat-Shamir challenge is unconstrained", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    let base: TransactWitnessBundle;
    before(() => {
        base = buildBase(ctx.tx);
    });

    // Each case also checks `y` against the reference Horner evaluation, so a
    // circuit that ignored `z` fails.
    const CHALLENGES: Array<{ label: string; z: () => Field }> = [
        { label: "z = 1", z: () => 1n },
        { label: "z = 2", z: () => 2n },
        { label: "an arbitrary attacker-chosen z", z: () => 0xdeadbeefcafef00dn },
        { label: "z = r - 1, the top of the scalar field", z: () => BN254_FR - 1n },
    ];

    for (const { label, z } of CHALLENGES) {
        it(`accepts ${label} — no constraint relates z to the coefficients`, async () => {
            const { circuit } = ctx;
            const input = witnessAt(base, z());
            await expectWitnessY(circuit, input, hornerEval(coeffs(input), z()));
        });
    }

    it("FAILS at z = 0, which would bind only the slot-0 coefficient", async () => {
        // At z = 0 Horner reduces to y === coeffs[0]. PolyEval rejects it rather
        // than relying on the consumer's keccak derivation to avoid it.
        const { circuit } = ctx;
        await expectWitnessFails(circuit, witnessAt(base, 0n), "z = 0 must be rejected");
    });

    it("accumulates from the high coefficient down, not the low one", async () => {
        const { circuit } = ctx;
        const z = 2n;
        const input = witnessAt(base, z);
        const forward = coeffs(input);
        const reversed = [...forward].reverse();

        expect(hornerEval(forward, z), "test is vacuous if the two agree").to.not.equal(
            hornerEval(reversed, z),
        );
        await expectWitnessY(circuit, input, hornerEval(forward, z));
    });

    it("one coefficient vector is accepted at two different z, with different y", async () => {
        // A verifier that reads `z` from calldata instead of recomputing it
        // accepts a proof at a prover-chosen evaluation point.
        const { circuit } = ctx;
        const zA = 7n;
        const zB = 0x1234_5678n;

        const inputA = witnessAt(base, zA);
        const inputB = { ...inputA, z: zB.toString() };

        const c = coeffs(inputA);
        const yA = hornerEval(c, zA);
        const yB = hornerEval(c, zB);
        expect(yA, "the two challenges must give different y for the case to say anything")
            .to.not.equal(yB);

        await expectWitnessY(circuit, inputA, yA);
        await expectWitnessY(circuit, inputB, yB);
    });

    // ===== why the recomputed z must never be 1 =====

    /**
     * Transpose two adjacent coefficients of a vector. Operates on the vector,
     * not a witness: every coefficient is pinned by another constraint, so no
     * pair can be swapped in an accepted witness.
     */
    function transposed(c: Field[], k: number): Field[] {
        const swapped = [...c];
        swapped[k] = c[k + 1];
        swapped[k + 1] = c[k];
        return swapped;
    }

    /** Slot 0 is `merkleRoot`; slot 1 is `nullifier[0]`. Always distinct. */
    const HEAD = 0;

    it("at z = 1 a transposed layout evaluates to an identical y", async () => {
        const { circuit } = ctx;
        const input = witnessAt(base, 1n);
        const c = coeffs(input);
        expect(c[HEAD], "the two slots must differ for the case to say anything").to.not.equal(
            c[HEAD + 1],
        );

        const y = hornerEval(c, 1n);
        expect(
            hornerEval(transposed(c, HEAD), 1n),
            "at z = 1 a transposition must not move y",
        ).to.equal(y);

        await expectWitnessY(circuit, input, y);
    });

    it("at z != 1 the same transposition moves y", async () => {
        const { circuit } = ctx;
        const z = 0x5eedn;
        const input = witnessAt(base, z);
        const c = coeffs(input);

        const y = hornerEval(c, z);
        expect(hornerEval(transposed(c, HEAD), z)).to.not.equal(y);

        await expectWitnessY(circuit, input, y);
    });
});
