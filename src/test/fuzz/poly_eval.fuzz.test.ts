// Property-based coverage for `lib/poly_eval.circom`.
//
// The unit test [src/test/poly_eval.test.ts](../poly_eval.test.ts) pins a
// handful of deterministic seeds. This file widens the surface with
// fast-check: random coefficients and `z` values across BN254 𝔽_r, plus
// algebraic identities (linearity, z=0, z=1) that lock the gadget to its
// Horner-form specification.
//
// Wrapper exposes `TestPolyEval26` (N=26 — the legacy 20-base + 6-clue
// Transact compress size). Property: contract-side `SnarkCompression`
// implements the SAME Horner schedule, so any Schwartz–Zippel divergence
// here would break the on-chain ↔ in-circuit binding.

import { expect } from "chai";
import * as fc from "fast-check";

import { fixturePath, loadCircuit } from "../lib/circuit";
import { fcParamsFor, arbField, mod, R, arbDistinctBigInt } from "./arbitraries";

const WRAPPER = fixturePath("test_poly_eval.circom");
const N = 26;
const fcParams = fcParamsFor("POLYEVAL");

function hornerEval(coeffs: bigint[], z: bigint): bigint {
    let acc = 0n;
    for (let i = coeffs.length - 1; i >= 0; i--) acc = mod(acc * z + coeffs[i], R);
    return acc;
}

function toInput(coeffs: bigint[], z: bigint) {
    return { coeffs: coeffs.map(c => c.toString()), z: z.toString() };
}

// Coefficient array arbitrary — N entries clamped to [0, R).
const arbCoeffs = fc.array(arbField(R - 1n), { minLength: N, maxLength: N });
const arbZ = arbField(R - 1n);
// Permutation property needs z ∉ {0, 1} (those are sum-/index-invariant).
const arbZForPermutation = fc.bigInt(2n, R - 1n);

// Boundary coefficient vectors.
const ALL_ZERO_COEFFS = Array<bigint>(N).fill(0n);
const ALL_MAX_COEFFS = Array<bigint>(N).fill(R - 1n);
const COEFFS_Z_EXAMPLES: [bigint[], bigint][] = [
    [ALL_ZERO_COEFFS, 0n],
    [ALL_ZERO_COEFFS, 1n],
    [ALL_ZERO_COEFFS, R - 1n],
    [ALL_MAX_COEFFS, 1n],
    [ALL_MAX_COEFFS, R - 1n],
];
const COEFFS_ONLY_EXAMPLES: [bigint[]][] = [[ALL_ZERO_COEFFS], [ALL_MAX_COEFFS]];

describe("PolyEval [fuzz, N=26]", function () {
    this.timeout(600_000);

    let circuit: any;
    before(async () => { circuit = await loadCircuit(WRAPPER); });

    it("matches hornerEval reference on random (coeffs, z)", async () => {
        await fc.assert(fc.asyncProperty(arbCoeffs, arbZ, async (coeffs, z) => {
            const expected = hornerEval(coeffs, z);
            const w = await circuit.calculateWitness(toInput(coeffs, z), true);
            await circuit.assertOut(w, { y: expected.toString() });
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
            const w = await circuit.calculateWitness(toInput(sum, z), true);
            await circuit.assertOut(w, { y: ys.toString() });
        }), fcParams);
    });

    it("scalar homogeneity: eval(k·a, z) = k · eval(a, z) mod R", async () => {
        await fc.assert(fc.asyncProperty(arbCoeffs, arbField(R - 1n), arbZ, async (a, k, z) => {
            const scaled = a.map(ai => mod(k * ai, R));
            const ya = hornerEval(a, z);
            const ys = hornerEval(scaled, z);
            expect(ys).to.equal(mod(k * ya, R));
            const w = await circuit.calculateWitness(toInput(scaled, z), true);
            await circuit.assertOut(w, { y: ys.toString() });
        }), fcParams);
    });

    it("z = 0 ⇒ y = coeffs[0] for any coefficient vector", async () => {
        await fc.assert(fc.asyncProperty(arbCoeffs, async coeffs => {
            const w = await circuit.calculateWitness(toInput(coeffs, 0n), true);
            await circuit.assertOut(w, { y: coeffs[0].toString() });
        }), fcParamsFor("POLYEVAL", { examples: COEFFS_ONLY_EXAMPLES }));
    });

    it("z = 1 ⇒ y = Σ coeffs mod R", async () => {
        await fc.assert(fc.asyncProperty(arbCoeffs, async coeffs => {
            const sum = mod(coeffs.reduce((s, c) => s + c, 0n), R);
            const w = await circuit.calculateWitness(toInput(coeffs, 1n), true);
            await circuit.assertOut(w, { y: sum.toString() });
        }), fcParamsFor("POLYEVAL", { examples: COEFFS_ONLY_EXAMPLES }));
    });

    it("permutation alters y (Schwartz–Zippel sanity)", async () => {
        // Build (c0, cN-1) as a distinct pair so swap is observable without
        // .filter / early-return; remaining N-2 slots stay uniform.
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
            const w = await circuit.calculateWitness(toInput(swapped, z), true);
            await circuit.assertOut(w, { y: yB.toString() });
        }), fcParams);
    });
});
