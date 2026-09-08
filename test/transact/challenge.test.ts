// `z` carries no constraint, and that is deliberate.
//
// `Transact` takes the Fiat-Shamir challenge as a public input and feeds it
// straight to `PolyEval`, which computes y = Σ c[k]·z^k. Nothing ties `z` to
// the coefficient vector: the circuit will evaluate the polynomial at whatever
// challenge the prover hands it and emit the matching `y`, and both are public
// signals, so the proof verifies. Soundness rests on the verifier RECOMPUTING
// `z` from calldata — `PubInputs.sol :: _finalizeTransactRaw` — and comparing it
// against the public signal.
//
// Recomputation is necessary and not sufficient. Because `z` is an input, the
// prover reads it before choosing a witness, so the Schwartz-Zippel bound the
// compression is usually justified by — which needs the coefficient vector fixed
// FIRST — does not apply. What carries the rest of the argument is that every
// coefficient is pinned by another constraint, leaving nothing to solve the one
// linear equation `y = Σ c[k]·z^k` with. `binding.test.ts` pins that membership
// rule; this file pins the delegation of `z` itself.
//
// This file states that property as executable tests rather than prose, for
// two reasons:
//
//   - Nothing else does. `reference.test.ts` notes in a comment that `z` is
//     unconstrained; `binding.test.ts` asserts the *derived* z is not 1. Neither
//     runs an attacker-chosen challenge through the circuit.
//   - It is negative space, and negative space rots silently. Someone deleting
//     the contract-side recomputation, on the reading that "the circuit checks
//     z", breaks nothing here or in any other suite. These cases say plainly
//     that the circuit does not, and name where the check lives.
//
// The final pair shows why the recomputation must never yield z = 1: at that
// challenge Horner collapses to a plain sum and the circuit accepts two
// witnesses that differ only by a transposition of the layout, emitting the
// same `y` for both.

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
    const { root, inputs } = tx.twoRealInputs([100n, 50n], ALICE_NSK);
    const input = tx.build({
        inputs,
        outputs: [tx.note(75n, ALICE_NSK, 9n), tx.note(75n, ALICE_NSK, 11n)],
        merkleRoot: root,
        z: 0n,
    });
    input.recipient_address = "12345";
    input.chain_id = "67890";
    return input;
}

/**
 * The base at a caller-chosen challenge.
 *
 * `z` is a plain public input that `build` only stores — nothing else in the
 * bundle derives from it, which is the very property this file exists to
 * demonstrate — so one built base serves every challenge and the eight callers
 * below cost one `TxBuilder` run between them instead of eight.
 */
function witnessAt(base: TransactWitnessBundle, z: Field): TransactWitnessBundle {
    return { ...base, z: z.toString() };
}

describe("transact_4x6 / Fiat-Shamir challenge is unconstrained", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    // Built once: `z` is the only thing the cases vary, and `build` merely
    // stores it.
    let base: TransactWitnessBundle;
    before(() => {
        base = buildBase(ctx.tx);
    });

    // Each case asserts BOTH that the circuit accepts the challenge and that it
    // emits the `y` the reference Horner evaluation predicts — so the test
    // cannot pass on a circuit that quietly ignored `z`.
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
        // Anchor on the Horner direction. A reversed accumulation would agree
        // with a reference `hornerEval` that was reversed the same way, so every
        // case above would still pass; comparing against the reversed vector at
        // the same z is what separates them.
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
        // The delegation stated directly: a prover picks the challenge, so a
        // verifier that reads `z` off calldata instead of recomputing it
        // accepts a proof about a polynomial the prover chose the evaluation
        // point for.
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
     * Done on the vector rather than on a witness: every coefficient is pinned
     * by some other constraint now, so no pair of them can be swapped in a
     * witness the circuit still accepts. That is the point of the membership
     * rule — but it also means the z = 1 degeneracy has to be stated about the
     * evaluation itself.
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
        // Horner degenerates to Σ c[k], which is permutation-invariant. A
        // `TransactCompressN` that emitted two slots in the wrong order would
        // therefore agree with the contract at this challenge and disagree
        // everywhere else, so a verifier that ever recomputed z = 1 could not
        // tell the two layouts apart.
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
        // The contrast that makes the case above specific to z = 1 rather than a
        // general statement about the layout.
        const { circuit } = ctx;
        const z = 0x5eedn;
        const input = witnessAt(base, z);
        const c = coeffs(input);

        const y = hornerEval(c, z);
        expect(hornerEval(transposed(c, HEAD), z)).to.not.equal(y);

        await expectWitnessY(circuit, input, y);
    });
});
