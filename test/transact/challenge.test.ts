// The Fiat-Shamir challenge `z` is unconstrained in the circuit by design.
//
// `Transact` takes `z` as a public input and passes it to `PolyEval`, which
// computes y = Σ c[k]·z^k. No constraint ties `z` to the coefficient vector:
// the circuit evaluates the polynomial at any supplied challenge and emits the
// matching `y`, and both are public signals, so the proof verifies. Soundness
// requires the verifier to recompute `z` from calldata
// (`PubInputs.sol :: _finalizeTransactRaw`) and compare it with the public signal.
//
// Recomputation is necessary but not sufficient. Because `z` is an input, the
// prover reads it before choosing a witness, so the Schwartz-Zippel bound, which
// requires the coefficient vector to be fixed first, does not apply. The
// remaining argument is that every coefficient is pinned by another constraint,
// leaving no free variable to solve the linear equation `y = Σ c[k]·z^k` for.
// `binding.test.ts` checks that membership rule; this file checks the
// delegation of `z` itself.
//
// These tests are the only ones that run an attacker-chosen challenge through
// the circuit (`binding.test.ts` asserts only that the derived z is not 1).
// Removing the contract-side recomputation fails no circuit test, so these
// cases document that the circuit does not check `z` and name where the check
// lives.
//
// The final pair shows why the recomputation must never yield z = 1: at that
// challenge Horner reduces to a plain sum, and two coefficient layouts that
// differ by a transposition produce the same `y`.

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

/**
 * The `balanced()` witness, but evaluated at a caller-chosen challenge rather
 * than the one `build` derives.
 *
 * The address slots are non-zero and distinct so the transposition case below
 * has two different values to swap.
 */
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
 * The base at a caller-chosen challenge.
 *
 * `z` is a public input that `build` only stores; nothing else in the bundle
 * derives from it, so one built base serves every challenge and the callers
 * below share a single `TxBuilder` run.
 */
function witnessAt(base: TransactWitnessBundle, z: Field): TransactWitnessBundle {
    return { ...base, z: z.toString() };
}

describe("transact_4x6 / Fiat-Shamir challenge is unconstrained", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    // Built once: the cases vary only `z`, which `build` stores.
    let base: TransactWitnessBundle;
    before(() => {
        base = buildBase(ctx.tx);
    });

    // Each case asserts that the circuit accepts the challenge and emits the `y`
    // predicted by the reference Horner evaluation, so a circuit that ignored `z`
    // fails.
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
        // At z = 0 the Horner chain reduces to y === coeffs[0], leaving every
        // other coefficient absent from the public signals. PolyEval rejects it
        // rather than relying on the consumer's keccak derivation to avoid it.
        const { circuit } = ctx;
        await expectWitnessFails(circuit, witnessAt(base, 0n), "z = 0 must be rejected");
    });

    it("accumulates from the high coefficient down, not the low one", async () => {
        // Pins the Horner direction. A reversed accumulation would agree with a
        // reference `hornerEval` reversed the same way and pass every case above;
        // comparing against the reversed vector at the same z distinguishes them.
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
        // The prover picks the challenge, so a verifier that reads `z` from
        // calldata instead of recomputing it accepts a proof at a
        // prover-chosen evaluation point.
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
     * Transpose two adjacent coefficients of a vector.
     *
     * Operates on the vector rather than a witness: every coefficient is pinned
     * by another constraint, so no pair can be swapped in an accepted witness,
     * and the z = 1 degeneracy is stated about the evaluation itself.
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
        // Horner reduces to Σ c[k], which is permutation-invariant. A
        // `TransactCompressN` that emitted two slots in the wrong order would
        // agree with the contract at this challenge only, so a verifier that
        // recomputed z = 1 could not distinguish the two layouts.
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
        // Shows the case above is specific to z = 1.
        const { circuit } = ctx;
        const z = 0x5eedn;
        const input = witnessAt(base, z);
        const c = coeffs(input);

        const y = hornerEval(c, z);
        expect(hornerEval(transposed(c, HEAD), z)).to.not.equal(y);

        await expectWitnessY(circuit, input, y);
    });
});
