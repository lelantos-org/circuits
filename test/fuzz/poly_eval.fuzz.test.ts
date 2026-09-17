// Property-based coverage for `lib/poly_eval.circom`.
//
// The unit test [test/gadgets/poly_eval.test.ts](../gadgets/poly_eval.test.ts) pins a set
// of deterministic seeds. This file adds random coefficients and `z` values
// across BN254 Fr, plus the algebraic identities (linearity, z=1) that tie the
// gadget to its Horner-form specification, and the z = 0 rejection.
//
// The wrapper exposes `TestPolyEval26` (N=26). The contract-side
// `SnarkCompression` implements the same Horner schedule, so a divergence here
// breaks the on-chain to in-circuit binding.

import { expect } from "chai";
import * as fc from "fast-check";

import { fixturePath } from "../lib/circuit";
import { expectWitnessFails } from "../lib/expect";
import { polyEvalInput as toInput } from "../lib/inputs";
import { hornerEval, mod } from "../helpers";
import { fcParamsFor, arbField, R, arbDistinctBigInt } from "./arbitraries";
import { TIMEOUT_HEAVY } from "../lib/constants";
import { useCircuit } from "../lib/harness";

const WRAPPER = fixturePath("test_poly_eval.circom");
const N = 26;
const fcParams = fcParamsFor("POLYEVAL");

// Coefficient array arbitrary — N entries clamped to [0, R).
const arbCoeffs = fc.array(arbField(R - 1n), { minLength: N, maxLength: N });
// z != 0. The gadget rejects zero (`z_nz.out === 0` in lib/poly_eval.circom)
// because at z = 0 the Horner chain reduces to y === coeffs[0] and the other N-1
// coefficients do not affect the public signals. The positive properties
// exclude it; the rejection is covered by "FAILS at z = 0".
const arbZ = fc.bigInt(1n, R - 1n);
// Permutation property needs z ∉ {0, 1} (those are sum-/index-invariant).
const arbZForPermutation = fc.bigInt(2n, R - 1n);

// Boundary coefficient vectors.
const ALL_ZERO_COEFFS = Array<bigint>(N).fill(0n);
const ALL_MAX_COEFFS = Array<bigint>(N).fill(R - 1n);
const COEFFS_Z_EXAMPLES: [bigint[], bigint][] = [
    [ALL_ZERO_COEFFS, 1n],
    [ALL_ZERO_COEFFS, R - 1n],
    [ALL_MAX_COEFFS, 1n],
    [ALL_MAX_COEFFS, R - 1n],
];
const COEFFS_ONLY_EXAMPLES: [bigint[]][] = [[ALL_ZERO_COEFFS], [ALL_MAX_COEFFS]];

describe("PolyEval [fuzz, N=26]", function () {
    this.timeout(TIMEOUT_HEAVY);

    const ctx = useCircuit(WRAPPER);

    /** Witness for `(coeffs, z)`, checked against the circuit's `y` output. */
    async function expectY(coeffs: bigint[], z: bigint, y: bigint): Promise<void> {
        const w = await ctx.circuit.calculateWitness(toInput(coeffs, z), true);
        await ctx.circuit.assertOut(w, { y: y.toString() });
    }

    it("matches hornerEval reference on random (coeffs, z)", async () => {
        await fc.assert(fc.asyncProperty(arbCoeffs, arbZ, async (coeffs, z) => {
            await expectY(coeffs, z, hornerEval(coeffs, z));
        }), fcParamsFor("POLYEVAL", { examples: COEFFS_Z_EXAMPLES }));
    });

    it("linearity: eval(a+b, z) = eval(a, z) + eval(b, z) mod R", async () => {
        await fc.assert(fc.asyncProperty(arbCoeffs, arbCoeffs, arbZ, async (a, b, z) => {
            const sum = a.map((ai, i) => mod(ai + b[i], R));
            const ya = hornerEval(a, z);
            const yb = hornerEval(b, z);
            const ys = hornerEval(sum, z);
            expect(ys).to.equal(mod(ya + yb, R));
            // Cross-check vs circuit for the summed polynomial.
            await expectY(sum, z, ys);
        }), fcParams);
    });

    it("scalar homogeneity: eval(k·a, z) = k · eval(a, z) mod R", async () => {
        await fc.assert(fc.asyncProperty(arbCoeffs, arbField(R - 1n), arbZ, async (a, k, z) => {
            const scaled = a.map(ai => mod(k * ai, R));
            const ya = hornerEval(a, z);
            const ys = hornerEval(scaled, z);
            expect(ys).to.equal(mod(k * ya, R));
            await expectY(scaled, z, ys);
        }), fcParams);
    });

    it("FAILS at z = 0 for any coefficient vector", async () => {
        await fc.assert(fc.asyncProperty(arbCoeffs, async coeffs => {
            await expectWitnessFails(
                ctx.circuit,
                toInput(coeffs, 0n),
                "z = 0 must be rejected",
            );
        }), fcParamsFor("POLYEVAL", { examples: COEFFS_ONLY_EXAMPLES }));
    });

    it("z = 1 ⇒ y = Σ coeffs mod R", async () => {
        await fc.assert(fc.asyncProperty(arbCoeffs, async coeffs => {
            const sum = mod(coeffs.reduce((s, c) => s + c, 0n), R);
            await expectY(coeffs, 1n, sum);
        }), fcParamsFor("POLYEVAL", { examples: COEFFS_ONLY_EXAMPLES }));
    });

    it("permutation alters y (Schwartz–Zippel sanity)", async () => {
        // (c0, cN-1) is drawn as a distinct pair so the swap is observable
        // without .filter or an early return; the other N-2 slots are uniform.
        const arbCoeffsDistinctEnds = fc.tuple(
            arbDistinctBigInt(0n, R - 1n),
            fc.array(arbField(R - 1n), { minLength: N - 2, maxLength: N - 2 }),
        ).map(([[c0, cLast], middle]) => [c0, ...middle, cLast]);

        await fc.assert(fc.asyncProperty(arbCoeffsDistinctEnds, arbZForPermutation, async (coeffs, z) => {
            const swapped = [...coeffs];
            [swapped[0], swapped[N - 1]] = [swapped[N - 1], swapped[0]];
            const yA = hornerEval(coeffs, z);
            const yB = hornerEval(swapped, z);
            expect(yA).to.not.equal(yB);
            await expectY(swapped, z, yB);
        }), fcParams);
    });
});
