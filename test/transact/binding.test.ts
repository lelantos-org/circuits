// Where each logical public input is bound, now that the two mechanisms differ.
//
// A logical public input reaches the proof one of two ways:
//
//   coefficient  it is a circuit signal and a `TransactCompressN` coefficient,
//                so it enters `y = Σ c[k]·z^k` directly;
//   challenge    it is not a signal at all, and enters only the keccak preimage
//                `PubInputs.compress` hashes into `z` — which moves `y`, since
//                the circuit evaluates the polynomial at whatever `z` it is
//                handed.
//
// Both bind. The difference is what they require: a coefficient is only binding
// if some other constraint pins it, and a challenge word needs nothing.
//
// `PolyEval` is affine in each coefficient, and `z` is an INPUT the prover reads
// before choosing a witness — the contract derives it from calldata the prover
// authored. An unpinned coefficient is therefore one linear equation in one
// unknown: solve it and any calldata verifies against a proof of an unrelated
// transaction. Schwartz-Zippel does not apply, because it needs the vector fixed
// before the challenge and here the challenge comes first.
//
// `recipient_address`, `chain_id`, `payer_address`, `relayer_address`, the FMD
// clue triples and `out_aux_digest` carry no in-circuit constraint. They used to
// be coefficients — 23 of the former 69 — and so were 23 such unknowns. They are
// challenge words now, and this file pins that: none of them is a signal, none
// of them is a coefficient, and every one of them still moves `z`.

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
] as const;

/** `4 + 3·N_IN + 5·N_OUT` = 46: what the polynomial evaluates. */
const COEFF_COUNT = 4 + 3 * N_IN + 5 * N_OUT;

/** `9 + 3·N_IN + 8·N_OUT` = 69: what the challenge hashes. */
const CHALLENGE_WORDS = 9 + 3 * N_IN + 8 * N_OUT;

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
        // The four writes above are challenge words, so the `z` `balanced()`
        // derived no longer describes this transaction.
        rebindFiatShamir(base);
    });

    // ===== the coefficient vector holds only pinned slots =====

    it("evaluates 46 coefficients and hashes 69 challenge words", () => {
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
        // Stronger than a subsequence, and the contract depends on the
        // difference: `PubInputs.compress` evaluates ONE span of the copied
        // calldata (`_finalizeRaw(head, n, nCoeffs)`). That is only correct
        // while every unpinned word sits after every pinned one, which is what
        // the member order of `PubInputs.Transact` is arranged to give. Move an
        // address word back into the middle and the contract silently evaluates
        // the wrong 46.
        const c = coeffs(base);
        const pre = flatten(base);
        expect(pre.slice(0, c.length)).to.deep.equal(
            c,
            "coefficients must be the preimage's leading words, in order",
        );
    });

    // ===== the unconstrained fields are not signals =====

    it("the challenge-only fields are not circuit signals", async () => {
        // The projection in `setup.ts` drops them precisely because the witness
        // calculator refuses them. Feeding one straight through proves the
        // circuit no longer declares it — which is what stops it being a free
        // variable in the first place.
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
     * The first half is the binding: the contract recomputes `z` from calldata,
     * so a relayer that rewrites one of these fields hands the verifier a
     * different challenge. The second half is what makes that fatal — the same
     * witness evaluated at the new challenge emits a different `y`, so the proof
     * no longer matches the pair the verifier derived.
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

        // Same coefficients either way — the field is not one — so the whole
        // difference in `y` comes from the challenge.
        const c = coeffs(base);
        expect(coeffs(tampered), `${label}: coefficients must not move`).to.deep.equal(c);

        const yBase = hornerEval(c, zBase);
        const yTampered = hornerEval(c, zTampered);
        expect(yBase, `${label}: y must differ at the two challenges`).to.not.equal(yTampered);

        // Only the TAMPERED challenge is run here. The base half —
        // `expectWitnessY(circuit, {...base, z: zBase}, yBase)` — does not depend
        // on `label` or `patch`, so it was the same witness generation eleven
        // times over; it is now the standalone case below.
        await expectWitnessY(circuit, { ...base, z: zTampered.toString() }, yTampered);
    }

    // The premise every BINDS row rests on: at the honest challenge the circuit
    // emits the reference `y`. If this failed, each row's tampered assertion
    // would be comparing against a broken baseline and the whole block would be
    // measuring nothing.
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
        // At z = 1 Horner collapses to a plain sum and any permutation of the
        // layout yields the same y, so this only says something at the derived
        // challenge. Slots 0 and 1 are `merkleRoot` and `nullifier[0]`, adjacent
        // and — unlike the public scalars, which are both 0 in a transfer —
        // always distinct.
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
