// Where each logical public input of transact is bound.
//
// A logical public input reaches the proof one of two ways:
//
//   coefficient  it is a circuit signal and a `TransactCompressN` coefficient,
//                so it enters `y = Σ c[k]·z^k` directly;
//   challenge    it is not a signal, and enters only the keccak preimage
//                `PubInputs.compress` hashes into `z`, which moves `y` because
//                the circuit evaluates the polynomial at the supplied `z`.
//
// Both bind, under different requirements: a coefficient binds only if another
// constraint pins it, while a challenge word needs no constraint.
//
// `PolyEval` is affine in each coefficient, and `z` is an input the prover reads
// before choosing a witness, derived by the contract from prover-authored
// calldata. An unpinned coefficient is therefore one linear equation in one
// unknown: solving it lets any calldata verify against a proof of an unrelated
// transaction. Schwartz-Zippel does not apply, because it requires the vector
// to be fixed before the challenge.
//
// `recipient_address`, `chain_id`, `payer_address`, `relayer_address`,
// `intent_hash`, the FMD clue triples and `out_aux_digest` carry no in-circuit
// constraint, so each is a challenge word. This file checks that none of them
// is a signal or a coefficient, and that each one moves `z`.

import { expect } from "chai";

import {
    coeffs,
    fiatShamirZ,
    flatten,
    hornerEval,
    type TransactWitnessBundle,
} from "../helpers";
import { N_IN, N_OUT, TIMEOUT_CIRCUIT } from "../lib/constants";
import { expectWitnessY } from "../lib/expect";
import { loadCircuit } from "../lib/circuit";
import { circuitSignals } from "../ref/witness";
import { rebindFiatShamir } from "../lib/transact";
import { CIRCUIT, useTransactCircuit } from "./setup";

/** Per-output arrays with no in-circuit constraint. */
const CHALLENGE_ARRAYS = ["out_clue_Rx", "out_clue_Ry", "out_clue_bits"] as const;

/** Scalars with no in-circuit constraint. */
const CHALLENGE_SCALARS = [
    "out_aux_digest",
    "recipient_address",
    "chain_id",
    "payer_address",
    "relayer_address",
    "intent_hash",
] as const;

/** `4 + 3·N_IN + 5·N_OUT` = 46: what the polynomial evaluates. */
const COEFF_COUNT = 4 + 3 * N_IN + 5 * N_OUT;

/** `10 + 3·N_IN + 8·N_OUT` = 70: what the challenge hashes. */
const CHALLENGE_WORDS = 10 + 3 * N_IN + 8 * N_OUT;

describe("transact_4x6 / where each public input is bound", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    // Built once; each case derives its own tampered copy from it.
    let base: TransactWitnessBundle;

    before(() => {
        base = ctx.tx.balanced();
        // Non-zero and distinct, so their challenge words are distinguishable
        // from one another and from a default.
        base.recipient_address = "12345";
        base.chain_id = "67890";
        base.payer_address = "11111";
        base.relayer_address = "22222";
        base.intent_hash = "33333";
        // The five writes above are challenge words, so the `z` derived by
        // `balanced()` must be recomputed.
        rebindFiatShamir(base);
    });

    // ===== the coefficient vector holds only pinned slots =====

    it("evaluates 46 coefficients and hashes 70 challenge words", () => {
        expect(coeffs(base).length, "coefficient vector").to.equal(COEFF_COUNT);
        expect(flatten(base).length, "challenge preimage").to.equal(CHALLENGE_WORDS);
    });

    it("no unconstrained field appears in the coefficient vector", () => {
        const c = coeffs(base);
        for (const field of CHALLENGE_SCALARS) {
            expect(c, `${field} must not be a coefficient`).to.not.include(BigInt(base[field]));
        }
        for (const field of CHALLENGE_ARRAYS) {
            for (const v of base[field]) {
                expect(c, `${field} must not be a coefficient`).to.not.include(BigInt(v));
            }
        }
    });

    it("the coefficients are the challenge preimage's leading words", () => {
        // A prefix, not merely a subsequence: `PubInputs.compress` evaluates a
        // single span of the copied calldata (`_finalizeRaw(head, n, nCoeffs)`),
        // which is correct only while every unpinned word follows every pinned
        // one. The member order of `PubInputs.Transact` provides this; an
        // unpinned word placed among the coefficients would make the contract
        // evaluate the wrong 46 words.
        const c = coeffs(base);
        const pre = flatten(base);
        expect(pre.slice(0, c.length)).to.deep.equal(
            c,
            "coefficients must be the preimage's leading words, in order",
        );
    });

    // ===== the unconstrained fields are not signals =====

    it("the challenge-only fields are not circuit signals", async () => {
        // The projection in `setup.ts` drops these fields because the witness
        // calculator refuses them. Passing one through shows the circuit does
        // not declare it, so it cannot be a free variable.
        const circuit = await loadCircuit(CIRCUIT);
        const withExtra = { ...circuitSignals(base), recipient_address: base.recipient_address };
        let err: unknown;
        try {
            await circuit.calculateWitness(withExtra as never, true);
        } catch (e) {
            err = e;
        }
        expect(err, "recipient_address must not be a signal of 4x6.circom").to.not.equal(undefined);
        expect(String(err)).to.match(/Too many values for input signal/);
    });

    // ===== they still bind, through the challenge =====

    /**
     * Assert that `patch` moves `z`, and that the circuit's `y` moves with it.
     *
     * The contract recomputes `z` from calldata, so a relayer that rewrites one
     * of these fields produces a different challenge. The same witness
     * evaluated at that challenge emits a different `y`, so the proof no longer
     * matches the pair the verifier derived.
     */
    async function assertBindsThroughChallenge(
        label: string,
        patch: (inp: TransactWitnessBundle) => void,
    ): Promise<void> {
        const { circuit } = ctx;
        const zBase = fiatShamirZ(flatten(base));

        const tampered = { ...base };
        patch(tampered);
        const zTampered = fiatShamirZ(flatten(tampered));

        expect(zBase, `${label}: z must differ when the field changes`).to.not.equal(zTampered);

        // The field is not a coefficient, so the difference in `y` comes
        // entirely from the challenge.
        const c = coeffs(base);
        expect(coeffs(tampered), `${label}: coefficients must not move`).to.deep.equal(c);

        const yBase = hornerEval(c, zBase);
        const yTampered = hornerEval(c, zTampered);
        expect(yBase, `${label}: y must differ at the two challenges`).to.not.equal(yTampered);

        // Only the tampered challenge is run here. The honest-challenge check
        // does not depend on `label` or `patch`, so it is a standalone case.
        await expectWitnessY(circuit, { ...base, z: zTampered.toString() }, yTampered);
    }

    // Baseline for the BINDS rows: at the honest challenge the circuit emits the
    // reference `y`. Without it, each row's tampered assertion could compare
    // against a broken baseline.
    it("emits the reference y at the honest challenge", async () => {
        const zBase = fiatShamirZ(flatten(base));
        await expectWitnessY(
            ctx.circuit,
            { ...base, z: zBase.toString() },
            hornerEval(coeffs(base), zBase),
        );
    });

    for (const field of CHALLENGE_ARRAYS) {
        for (const j of [0, 1]) {
            it(`BINDS ${field}[${j}] through the challenge`, async () => {
                await assertBindsThroughChallenge(`${field}[${j}]`, inp => {
                    const next = [...inp[field]];
                    next[j] = (BigInt(next[j]) + 1n).toString();
                    inp[field] = next;
                });
            });
        }
    }

    for (const field of CHALLENGE_SCALARS) {
        it(`BINDS ${field} through the challenge`, async () => {
            await assertBindsThroughChallenge(field, inp => {
                inp[field] = (BigInt(inp[field]) + 1n).toString();
            });
        });
    }

    // ===== the pinned slots still bind through the coefficient vector =====

    it("y is sensitive to coefficient ORDER, not just membership", () => {
        // At z = 1 Horner reduces to a plain sum and every permutation yields the
        // same y, so the check uses the derived challenge. Slots 0 and 1 are
        // `merkleRoot` and `nullifier[0]`: adjacent and always distinct, unlike
        // the public scalars, which are both 0 in a transfer.
        const z = BigInt(base.z);
        expect(z, "z must not be 1: at z = 1 any permutation of the layout yields the same y")
            .to.not.equal(1n);

        const c = coeffs(base);
        expect(c[0]).to.equal(BigInt(base.merkle_root));
        expect(c[1]).to.equal(BigInt(base.nullifier[0]!));
        expect(c[0], "the two slots must differ for the case to say anything").to.not.equal(c[1]);

        const swapped = [...c];
        swapped[0] = c[1];
        swapped[1] = c[0];

        expect(hornerEval(swapped, z), "transposing two coefficients must move y").to.not.equal(
            hornerEval(c, z),
        );
    });
});
