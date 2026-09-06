// `z` carries no constraint, and that is deliberate.
//
// `Transact` takes the Fiat-Shamir challenge as a public input and feeds it
// straight to `PolyEval`, which computes y = Σ c[k]·z^k. Nothing ties `z` to
// the coefficient vector: the circuit will evaluate the polynomial at whatever
// challenge the prover hands it and emit the matching `y`, and both are public
// signals, so the proof verifies. Soundness rests entirely on the verifier
// RECOMPUTING `z` from calldata — `PubInputs.sol :: _finalizeRaw` — and
// comparing it against the public signal.
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
    flatten,
    hornerEval,
    type CircomTransactInput,
    type Field,
} from "../helpers";
import { expectWitnessY } from "../lib/expect";
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
function witnessAt(tx: TxBuilder, z: Field): CircomTransactInput {
    const { root, inputs } = tx.twoRealInputs([100n, 50n], ALICE_NSK);
    const input = tx.build({
        inputs,
        outputs: [tx.note(75n, ALICE_NSK, 9n), tx.note(75n, ALICE_NSK, 11n)],
        merkleRoot: root,
        z,
    });
    input.recipient_address = "12345";
    input.chain_id = "67890";
    return input;
}

describe("transact_4x6 / Fiat-Shamir challenge is unconstrained", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    // Each case asserts BOTH that the circuit accepts the challenge and that it
    // emits the `y` the reference Horner evaluation predicts — so the test
    // cannot pass on a circuit that quietly ignored `z`.
    const CHALLENGES: Array<{ label: string; z: () => Field }> = [
        { label: "z = 0", z: () => 0n },
        { label: "z = 1", z: () => 1n },
        { label: "z = 2", z: () => 2n },
        { label: "an arbitrary attacker-chosen z", z: () => 0xdeadbeefcafef00dn },
        { label: "z = r - 1, the top of the scalar field", z: () => BN254_FR - 1n },
    ];

    for (const { label, z } of CHALLENGES) {
        it(`accepts ${label} — no constraint relates z to the coefficients`, async () => {
            const { tx, circuit } = ctx;
            const input = witnessAt(tx, z());
            await expectWitnessY(circuit, input, hornerEval(flatten(input), z()));
        });
    }

    it("at z = 0 the circuit emits y = merkle_root, the slot-0 coefficient", async () => {
        // Concrete anchor on the Horner direction: `PolyEval` accumulates from
        // the high coefficient down, so z = 0 leaves c[0]. A reversed
        // accumulation would emit out_aux_digest here instead, and every
        // reference-agreement case above would still pass, since `hornerEval`
        // could be reversed in the same way.
        const { tx, circuit } = ctx;
        const input = witnessAt(tx, 0n);
        await expectWitnessY(circuit, input, BigInt(input.merkle_root));
    });

    it("one coefficient vector is accepted at two different z, with different y", async () => {
        // The delegation stated directly: a prover picks the challenge, so a
        // verifier that reads `z` off calldata instead of recomputing it
        // accepts a proof about a polynomial the prover chose the evaluation
        // point for.
        const { tx, circuit } = ctx;
        const zA = 7n;
        const zB = 0x1234_5678n;

        const inputA = witnessAt(tx, zA);
        const inputB = { ...inputA, z: zB.toString() };

        const coeffs = flatten(inputA);
        const yA = hornerEval(coeffs, zA);
        const yB = hornerEval(coeffs, zB);
        expect(yA, "the two challenges must give different y for the case to say anything")
            .to.not.equal(yB);

        await expectWitnessY(circuit, inputA, yA);
        await expectWitnessY(circuit, inputB, yB);
    });

    // ===== why the recomputed z must never be 1 =====

    /** Swap the `recipient_address` and `chain_id` coefficient slots. */
    function transposed(input: CircomTransactInput): CircomTransactInput {
        return { ...input, recipient_address: input.chain_id, chain_id: input.recipient_address };
    }

    it("at z = 1 the circuit accepts a transposed layout with an identical y", async () => {
        // Horner degenerates to Σ c[k], which is permutation-invariant. Both
        // witnesses are honest — the two slots carry no in-circuit constraint —
        // so the circuit accepts each and emits the same public signals. A
        // verifier at z = 1 therefore cannot tell the recipient's address from
        // the chain id.
        const { tx, circuit } = ctx;
        const input = witnessAt(tx, 1n);
        const swapped = transposed(input);

        expect(input.recipient_address).to.not.equal(input.chain_id);

        const y = hornerEval(flatten(input), 1n);
        expect(hornerEval(flatten(swapped), 1n), "at z = 1 a transposition must not move y")
            .to.equal(y);

        await expectWitnessY(circuit, input, y);
        await expectWitnessY(circuit, swapped, y);
    });

    it("at z != 1 the same transposition moves y", async () => {
        // The contrast that makes the case above specific to z = 1 rather than
        // a general statement about unconstrained slots.
        const { tx, circuit } = ctx;
        const z = 0x5eedn;
        const input = witnessAt(tx, z);
        const swapped = transposed(input);

        const y = hornerEval(flatten(input), z);
        const ySwapped = hornerEval(flatten(swapped), z);
        expect(ySwapped).to.not.equal(y);

        await expectWitnessY(circuit, input, y);
        await expectWitnessY(circuit, swapped, ySwapped);
    });
});
