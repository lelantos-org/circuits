// The coefficient digest: the commitment that makes the evaluation bind.
//
// `PolyEval` is affine in each coefficient, and `z` is derived from
// prover-authored calldata, so the prover reads it before choosing a witness.
// Parameters that move only their own coefficient (each output's `rcm`, a dummy
// slot's `rho`, `merkle_root`) displace `y` additively, so `y` alone does not
// bind. The circuit's second public output, `digest`, is a Poseidon commitment
// to the same coefficients; the contract takes the digest word from calldata,
// hashes it into `z` and passes it to the verifier, which ties a witness to one
// coefficient vector before the challenge exists. See TransactCompressN's
// header in src/lib/poly_eval.circom for the argument and its assumptions.

import { expect } from "chai";

import {
    coeffs,
    hornerEval,
    mod,
    transactDigest,
    type Field,
    type TransactWitnessBundle,
} from "../helpers";
import { expectWitnessPublic, readOutput } from "../lib/expect";
import { ALICE_NSK, N_IN, N_OUT, TIMEOUT_CIRCUIT } from "../lib/constants";
import { TxBuilder } from "../lib/transact";
import { useTransactCircuit } from "./setup";

describe("transact_4x6 / coefficient digest", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    /** `3 + N_IN + N_OUT`: the coefficients, which the digest absorbs in order. */
    const COEFF_COUNT = 3 + N_IN + N_OUT;

    /**
     * The balanced two-in-two-out witness, with the `rcm` of output slots 0 and
     * 1 overridden and the challenge pinned to `z`.
     */
    function witnessWith(
        tx: TxBuilder,
        z: Field,
        override: { rcm0?: Field; rcm1?: Field },
    ): TransactWitnessBundle {
        const out0 = tx.note(75n, ALICE_NSK, 9n);
        const out1 = tx.note(75n, ALICE_NSK, 11n);
        return tx.spend(
            tx.twoRealInputs([100n, 50n], ALICE_NSK),
            [
                { ...out0, rcm: override.rcm0 ?? out0.rcm },
                { ...out1, rcm: override.rcm1 ?? out1.rcm },
            ],
            { z },
        );
    }

    // Shared by all four variants: a parameter that moves `y` at a fixed `z` is
    // one the prover holds after the challenge.
    const Z: Field = 0xdeadbeefcafef00dn;

    const RCM0_ALT: Field = 0x1234_5678_9abc_def0n;
    const RCM1_ALT: Field = 0x0fed_cba9_8765_4321n;

    type Variant = "base" | "a" | "b" | "both";
    const VARIANTS = ["base", "a", "b", "both"] as const;

    let bundle: Record<Variant, TransactWitnessBundle>;
    let y: Record<Variant, bigint>;
    let digest: Record<Variant, bigint>;

    before(async () => {
        // Sequential: `TxBuilder` is stateful, and concurrent builds differ in
        // more than the two overrides.
        const { tx, circuit } = ctx;
        bundle = {
            base: witnessWith(tx, Z, {}),
            a: witnessWith(tx, Z, { rcm0: RCM0_ALT }),
            b: witnessWith(tx, Z, { rcm1: RCM1_ALT }),
            both: witnessWith(tx, Z, { rcm0: RCM0_ALT, rcm1: RCM1_ALT }),
        };
        y = {} as Record<Variant, bigint>;
        digest = {} as Record<Variant, bigint>;
        for (const k of VARIANTS) {
            // Both outputs are checked against the reference on the way.
            const c = coeffs(bundle[k]);
            expect(c.length).to.equal(COEFF_COUNT);
            const w = await expectWitnessPublic(circuit, bundle[k], {
                y: hornerEval(c, Z),
                digest: transactDigest(bundle[k]),
            });
            y[k] = readOutput(w, 0);
            digest[k] = readOutput(w, 1);
        }
    });

    // Successful generation of all four witnesses shows both parameters are
    // free: nothing but each slot's own `out_cm` constrains its `rcm`.

    it("each out_rcm moves y at a fixed challenge", () => {
        expect(y.a, "out_rcm[0] is a free parameter and must move y").to.not.equal(y.base);
        expect(y.b, "out_rcm[1] is a free parameter and must move y").to.not.equal(y.base);
    });

    it("their contributions to y are additively separable: y alone does not bind", () => {
        // Each `rcm` moves one `out_cm` and nothing else, so the displacements
        // of `y` add. Expected to hold; the test above guards against the
        // vacuous 0 == 0 + 0.
        expect(mod(y.both - y.base).toString())
            .to.equal(mod(mod(y.a - y.base) + mod(y.b - y.base)).toString());
    });

    it("every one of those witnesses has a different digest", () => {
        // If two of these witnesses shared a digest, a prover could move between
        // them after seeing the challenge.
        const seen = new Set(VARIANTS.map(k => digest[k].toString()));
        expect(seen.size, "a free witness parameter did not move the digest output")
            .to.equal(VARIANTS.length);
    });

    it("the digest does not depend on the challenge", async () => {
        // Same witness, another challenge: `y` moves, the digest output does not.
        const other = witnessWith(ctx.tx, Z + 1n, {});
        const w = await expectWitnessPublic(ctx.circuit, other, {
            y: hornerEval(coeffs(other), Z + 1n),
            digest: digest.base,
        });
        expect(readOutput(w, 0)).to.not.equal(y.base);
    });
});
