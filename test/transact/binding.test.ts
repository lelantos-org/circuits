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
// Both bind, under different requirements. `PolyEval` is affine in each
// coefficient, and `z` is an input the prover reads before choosing a witness,
// derived by the contract from prover-authored calldata. The coefficients bind
// because the circuit also outputs a Poseidon commitment to them
// (`CoeffDigest`), which the contract takes from calldata, hashes into `z` and
// passes to the verifier: the witness's coefficients are fixed before the
// challenge, which is the order Schwartz-Zippel requires. A challenge word needs
// no constraint.
//
// `recipient_address`, `chain_id`, `payer_address`, `relayer_address`,
// `intent_hash`, the FMD clue triples and `out_aux_digest` carry no in-circuit
// constraint, so each is a challenge word. This file checks that none of them
// is a signal or a coefficient, and that each one moves `z`. It also checks what
// the digest argument places on the layout: the digest word is in the challenge
// preimage, is not evaluated, and equals the circuit's second public output.

import { expect } from "chai";

import {
    coeffs,
    fiatShamirZ,
    flatten,
    hornerEval,
    transactDigest,
    type TransactWitnessBundle,
} from "../helpers";
import { N_IN, N_OUT, TIMEOUT_CIRCUIT } from "../lib/constants";
import { expectWitnessPublic, expectWitnessY, readOutput } from "../lib/expect";
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

/** `3 + N_IN + N_OUT` = 13: what the polynomial evaluates. */
const COEFF_COUNT = 3 + N_IN + N_OUT;

/** `10 + N_IN + 4·N_OUT` = 38: what the challenge hashes. */
const CHALLENGE_WORDS = 10 + N_IN + 4 * N_OUT;

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

    // ===== the coefficient vector holds exactly the circuit's public signals =====

    it("evaluates 13 coefficients and hashes 38 challenge words", () => {
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
        // which is correct only while every challenge-only word follows every
        // coefficient. The member order of `PubInputs.Transact` provides this; a
        // challenge-only word placed among the coefficients would make the
        // contract evaluate the wrong 13 words.
        const c = coeffs(base);
        const pre = flatten(base);
        expect(pre.slice(0, c.length)).to.deep.equal(
            c,
            "coefficients must be the preimage's leading words, in order",
        );
    });

    // ===== the digest: hashed, output by the circuit, never evaluated =====

    it("the digest word follows the coefficients in the challenge preimage and is not one of them", () => {
        // Hashed, so it is fixed before `z` exists: that is what makes it a
        // commitment the witness cannot be chosen around. Not evaluated: it
        // reaches the verifier as a public signal of its own.
        const c = coeffs(base);
        const pre = flatten(base);
        const digest = transactDigest(base);
        expect(BigInt(base.digest), "the bundle carries the digest of its own coefficients").to.equal(digest);
        expect(pre[COEFF_COUNT], "preimage word right after the coefficients").to.equal(digest);
        expect(c.length).to.equal(COEFF_COUNT);
        expect(c, "the digest is not a coefficient").to.not.include(digest);

        const moved = { ...base, digest: (digest + 1n).toString() };
        expect(fiatShamirZ(flatten(moved)), "a different digest word must move z")
            .to.not.equal(fiatShamirZ(pre));
        expect(coeffs(moved), "and must not move a coefficient").to.deep.equal(c);
    });

    it("the circuit outputs the digest of its coefficients as its second public signal", async () => {
        // The word the contract passes to the verifier is compared against this
        // output, so it must be the reference digest, at output index 1.
        const w = await expectWitnessPublic(ctx.circuit, base, {
            y: hornerEval(coeffs(base), BigInt(base.z)),
            digest: transactDigest(base),
        });
        expect(readOutput(w, 1)).to.equal(BigInt(base.digest));
    });

    it("the digest covers every coefficient", () => {
        // Moving any one of the 13 signals moves the digest. A word left out
        // would be a coefficient the prover can change without changing the
        // commitment the contract checks.
        const digest = transactDigest(base);
        const bumped = (v: string) => (BigInt(v) + 1n).toString();
        const variants: [string, TransactWitnessBundle][] = [
            ["merkle_root", { ...base, merkle_root: bumped(base.merkle_root) }],
            ["public_asset_id", { ...base, public_asset_id: bumped(base.public_asset_id) }],
            ["public_out", { ...base, public_out: bumped(base.public_out) }],
        ];
        for (let i = 0; i < N_IN; i++) {
            const nullifier = [...base.nullifier];
            nullifier[i] = bumped(nullifier[i]);
            variants.push([`nullifier[${i}]`, { ...base, nullifier }]);
        }
        for (let j = 0; j < N_OUT; j++) {
            const out_cm = [...base.out_cm];
            out_cm[j] = bumped(out_cm[j]);
            variants.push([`out_cm[${j}]`, { ...base, out_cm }]);
        }
        expect(variants.length, "one variant per coefficient").to.equal(COEFF_COUNT);
        for (const [label, v] of variants) {
            expect(transactDigest(v), `${label} must move the digest`).to.not.equal(digest);
        }
    });

    it("the digest does not depend on the challenge or on any challenge-only word", () => {
        // It commits the coefficients before `z` is derived, so it cannot be a
        // function of `z`, and the challenge-only words have no witness copy.
        const digest = transactDigest(base);
        const otherChallenge: TransactWitnessBundle = { ...base, z: "12345" };
        const otherBinding: TransactWitnessBundle = { ...base, recipient_address: "999", intent_hash: "7" };
        expect(transactDigest(otherChallenge)).to.equal(digest);
        expect(transactDigest(otherBinding)).to.equal(digest);
    });

    it("the digest is not an input signal: the circuit computes its own", async () => {
        const circuit = await loadCircuit(CIRCUIT);
        const withExtra = { ...circuitSignals(base), digest: base.digest };
        let err: unknown;
        try {
            await circuit.calculateWitness(withExtra as never, true);
        } catch (e) {
            err = e;
        }
        expect(err, "digest must not be an input of 4x6.circom").to.not.equal(undefined);
        expect(String(err)).to.match(/Too many values for input signal/);
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

    // ===== the signals still bind through the coefficient vector =====

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
