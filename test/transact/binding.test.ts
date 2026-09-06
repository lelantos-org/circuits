// PolyEval binding for the fields the circuit does not otherwise constrain.
//
// out_clue_*, out_aux_digest and the four address fields carry no in-circuit
// constraint. Their only binding is inclusion in the coefficient vector: change
// one and `y` changes, invalidating the proof against the original (z, y) pair.
// A TransactCompressN that dropped a slot would pass every constraint test and
// fail only here.
//
// The property holds only at a live Fiat-Shamir challenge. At z = 1 the Horner
// chain collapses to a plain sum, so `y` is permutation-invariant and a compress
// that transposed two slots would satisfy every assertion below.
// `TxBuilder.build` derives z from the coefficients for that reason, and the
// last case here pins it.
//
// For the clue fields, this is what stops a relayer leaving the clue intact — so
// the proof verifies and the recipient's FMD scan flags the note — while
// corrupting the ciphertext the recipient needs to open it.

import { expect } from "chai";

import { flatten, hornerEval, type CircomTransactInput } from "../helpers";
import { N_IN, N_OUT, TIMEOUT_CIRCUIT } from "../lib/constants";
import { expectWitnessY } from "../lib/expect";
import { rebindFiatShamir } from "../lib/transact";
import { useTransactCircuit } from "./setup";

/** Fields with no in-circuit constraint, so PolyEval is the only thing binding them. */
const BOUND_FIELDS = [
    "out_clue_Rx",
    "out_clue_Ry",
    "out_clue_bits",
] as const;

/** Same, but scalars rather than per-output arrays. */
const BOUND_SCALARS = [
    "out_aux_digest",
    "recipient_address",
    "chain_id",
    "payer_address",
    "relayer_address",
] as const;

/** Slot count of the 4x6 coefficient vector — out_aux_digest is the last one.
 * `9 + 3·N_IN + 8·N_OUT` = `9 + 12 + 48`. */
const COEFF_COUNT = 9 + 3 * N_IN + 8 * N_OUT;

describe("transact_4x6 / PolyEval binding", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    // Built once; each case derives its own tampered copy from it.
    let base: CircomTransactInput;

    before(() => {
        base = ctx.tx.balanced();
        // Non-zero address fields, so their coefficient slots are distinguishable
        // from one another and from a default.
        base.recipient_address = "12345";
        base.chain_id          = "67890";
        base.payer_address     = "11111";
        base.relayer_address   = "22222";
        // The four writes above are PolyEval coefficients, so the challenge
        // `balanced()` derived does not describe this witness.
        rebindFiatShamir(base);
    });

    /**
     * Assert that `patch` moves `y`, and that both witnesses report the `y` the
     * reference predicts.
     *
     * The inequality establishes that the field reaches the polynomial; the two
     * `expectWitnessY` calls establish that the circuit and the reference agree
     * on its evaluation over a checked constraint system.
     *
     * `z` is held fixed across the pair: that is the tamper the verifier sees, a
     * relayer rewriting a coefficient in calldata while replaying the original
     * challenge.
     */
    async function assertBinds(
        label: string,
        patch: (inp: CircomTransactInput) => void,
    ): Promise<void> {
        const { circuit } = ctx;
        const z = BigInt(base.z);
        const yBase = hornerEval(flatten(base), z);

        const tampered = { ...base };
        patch(tampered);
        const yTampered = hornerEval(flatten(tampered), z);

        expect(yBase, `${label}: y must differ when the field changes`).to.not.equal(yTampered);

        // No constraint covers these fields, so both witnesses generate and `y`
        // carries the entire signal.
        await expectWitnessY(circuit, base, yBase);
        await expectWitnessY(circuit, tampered, yTampered);
    }

    for (const field of BOUND_FIELDS) {
        for (const j of [0, 1]) {
            it(`BINDS ${field}[${j}]: altering it changes y`, async () => {
                await assertBinds(`${field}[${j}]`, inp => {
                    const next = [...inp[field]];
                    next[j] = (BigInt(next[j]) + 1n).toString();
                    inp[field] = next;
                });
            });
        }
    }

    for (const field of BOUND_SCALARS) {
        it(`BINDS ${field}: altering it changes y`, async () => {
            await assertBinds(field, inp => {
                inp[field] = (BigInt(inp[field]) + 1n).toString();
            });
        });
    }

    it("out_aux_digest occupies the final coefficient slot", () => {
        const coeffs = flatten(base);
        expect(coeffs.length).to.equal(COEFF_COUNT);
        expect(coeffs[COEFF_COUNT - 1]).to.equal(BigInt(base.out_aux_digest));
    });

    // Pins that `y` depends on coefficient ORDER, not only on which fields reach
    // the total. At z = 1 PolyEval degenerates to a plain sum, and a
    // TransactCompressN that transposed two slots would satisfy every case above.
    it("y is sensitive to slot order, not just slot membership", () => {
        const z = BigInt(base.z);
        expect(z, "z must not be 1: at z = 1 any permutation of the layout yields the same y")
            .to.not.equal(1n);

        // recipient_address and chain_id: adjacent slots, distinct values.
        const recipient = 1 + N_IN + N_OUT + 3 + 2 * N_IN + 2 * N_OUT;
        const coeffs = flatten(base);
        expect(coeffs[recipient]).to.equal(BigInt(base.recipient_address));
        expect(coeffs[recipient + 1]).to.equal(BigInt(base.chain_id));

        const swapped = [...coeffs];
        swapped[recipient] = coeffs[recipient + 1];
        swapped[recipient + 1] = coeffs[recipient];

        expect(
            hornerEval(swapped, z),
            "transposing two coefficients must move y",
        ).to.not.equal(hornerEval(coeffs, z));
    });
});
