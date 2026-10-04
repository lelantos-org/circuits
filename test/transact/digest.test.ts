// The coefficient digest: the commitment that makes the evaluation bind.
//
// `PolyEval` is affine in each coefficient with slope z^k, and `z` is derived
// from prover-authored calldata, so the prover reads it before choosing a
// witness. A witness has parameters nothing but its own coefficient depends on:
// each output's `rcm` moves only that slot's `out_cm`, a dummy slot's `rho`
// moves only its nullifier, and `merkle_root` follows whatever tree the prover
// builds. Each such parameter displaces `y` on its own and the displacements
// add exactly:
//
//     (y_both − y_base) ≡ (y_a − y_base) + (y_b − y_base)   (mod r)
//
// If `y` were the only thing tying a proof to calldata, making it match
// calldata the witness does not describe would be a modular k-sum over those
// parameters, which a k-tree solves far below a search of the field.
//
// So the circuit has a second public output, `digest`, a Poseidon commitment
// to the same coefficients. The contract takes the digest word from calldata,
// hashes it into `z` and passes it to the verifier. A witness is therefore
// tied to one coefficient vector before the challenge exists, and a different
// vector is a different polynomial that agrees at a random `z` with probability
// at most 12/r.
//
// This file pins the two halves of that at the circuit: `y` alone is separable,
// which is why it cannot be the binding; and every one of those parameters
// moves `digest`, which is why it can. `divergent.test.ts` runs the forgery
// attempts themselves. See TransactCompressN's header in
// src/lib/poly_eval.circom for the argument and its assumptions.

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
     *
     * Every variant is built through here, so the four differ only in those two
     * values: same notes, values, nullifiers, tree and `z`.
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

    // The challenge shared by all four variants. A parameter that moves `y` only
    // by also moving `z` is bound (the contract recomputes `z`); one that moves
    // `y` at a fixed `z` is a parameter the prover holds after the challenge.
    const Z: Field = 0xdeadbeefcafef00dn;

    const RCM0_ALT: Field = 0x1234_5678_9abc_def0n;
    const RCM1_ALT: Field = 0x0fed_cba9_8765_4321n;

    type Variant = "base" | "a" | "b" | "both";
    const VARIANTS = ["base", "a", "b", "both"] as const;

    // The four witnesses, generated once, so each assertion compares cached
    // values rather than rerunning the circuit.
    let bundle: Record<Variant, TransactWitnessBundle>;
    let y: Record<Variant, bigint>;
    let digest: Record<Variant, bigint>;

    before(async () => {
        // Sequential: `TxBuilder` is stateful (`newTree` plus inserts), and
        // concurrent builds interleave its internals so the bundles no longer
        // differ only in the two overrides.
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
        // Each `rcm` moves one `out_cm` and nothing else, so moving both
        // displaces `y` by exactly the sum of the separate displacements. This
        // is why the proof cannot be tied to calldata through `y` alone, and it
        // is expected to hold: if it ever fails, something other than the
        // coefficients has entered the evaluation.
        //
        // The test above guards against vacuity: at zero displacement this
        // reads 0 == 0 + 0.
        expect(mod(y.both - y.base).toString())
            .to.equal(mod(mod(y.a - y.base) + mod(y.b - y.base)).toString());
    });

    it("every one of those witnesses has a different digest", () => {
        // The assertion a regression must trip. The digest output is what the
        // verifier compares against the calldata digest word, which is fixed
        // before `z`. If two of these witnesses shared a digest, a prover could
        // move between them after seeing the challenge.
        const seen = new Set(VARIANTS.map(k => digest[k].toString()));
        expect(seen.size, "a free witness parameter did not move the digest output")
            .to.equal(VARIANTS.length);
    });

    it("the digest does not depend on the challenge", async () => {
        // A commitment made before `z` cannot be a function of it. Same witness,
        // another challenge: `y` moves, the digest output does not.
        const other = witnessWith(ctx.tx, Z + 1n, {});
        const w = await expectWitnessPublic(ctx.circuit, other, {
            y: hornerEval(coeffs(other), Z + 1n),
            digest: digest.base,
        });
        expect(readOutput(w, 0)).to.not.equal(y.base);
    });
});
