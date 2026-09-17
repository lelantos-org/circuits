import { expect } from "chai";

import { BN254_FR, hornerEval, mod } from "../helpers";
import { fixturePath } from "../lib/circuit";
import { expectThrows, expectWitnessFails } from "../lib/expect";
import { polyEvalInput } from "../lib/inputs";
import { TIMEOUT_CIRCUIT } from "../lib/constants";
import { useCircuit } from "../lib/harness";

const WRAPPER = fixturePath("test_poly_eval.circom");
// Must match `PolyEval(N)` in the fixture. The gadget is arity-generic; this size
// is specific to the test wrapper.
const N = 26;

describe("PolyEval (Horner-form binding gadget)", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useCircuit(WRAPPER);

    /** Witness for `(coeffs, z)`, checked against the circuit's `y` output. */
    async function expectY(coeffs: bigint[], z: bigint, y: bigint): Promise<bigint[]> {
        const w = await ctx.circuit.calculateWitness(polyEvalInput(coeffs, z), true);
        await ctx.circuit.assertOut(w, { y: y.toString() });
        return w;
    }

    it("matches manual Σ c_k·z^k for random inputs", async () => {
        for (const seed of [1n, 7n, 0xdeadbeefn, 1234567890123456n]) {
            const coeffs = Array.from({ length: N }, (_, i) =>
                mod(seed * BigInt(i + 1) * 0x9e3779b97f4a7c15n, BN254_FR),
            );
            const z = mod(seed * 0x100000001b3n + 17n, BN254_FR);
            await expectY(coeffs, z, hornerEval(coeffs, z));
        }
    });

    it("FAILS at z = 0, which would leave every coefficient above 0 unbound", async () => {
        const coeffs = Array.from({ length: N }, (_, i) => BigInt(i + 1) * 11n);
        await expectWitnessFails(ctx.circuit, polyEvalInput(coeffs, 0n), "z = 0 must be rejected");
    });

    it("z = 1 ⇒ y = Σ coeffs", async () => {
        const coeffs = Array.from({ length: N }, (_, i) => BigInt(i + 1));
        const sum = mod(coeffs.reduce((a, b) => a + b, 0n), BN254_FR);
        await expectY(coeffs, 1n, sum);
    });

    it("z = p - 1 ⇒ alternating-sign sum", async () => {
        const coeffs = Array.from({ length: N }, (_, i) => BigInt(i + 1) * 3n);
        const z = mod(BN254_FR - 1n, BN254_FR);
        await expectY(coeffs, z, hornerEval(coeffs, z));
    });

    it("permuting coefficients alters y (Schwartz–Zippel sanity)", async () => {
        const coeffs = Array.from({ length: N }, (_, i) =>
            mod((BigInt(i) + 1n) * 0xc0ffeedeadbeefn, BN254_FR),
        );
        const z = 9876543210n;
        const yBase = hornerEval(coeffs, z);
        const swapped = [...coeffs];
        // Swap two distinct entries: y depends on coefficient order.
        [swapped[0], swapped[1]] = [swapped[1], swapped[0]];
        const yPerm = hornerEval(swapped, z);
        expect(yBase).to.not.equal(yPerm);

        await expectY(swapped, z, yPerm);
    });

    it("rejects mismatched y output", async () => {
        const coeffs = Array.from({ length: N }, (_, i) => BigInt(i + 1));
        const z = 42n;
        const expected = hornerEval(coeffs, z);
        const w = await expectY(coeffs, z, expected);
        await expectThrows(
            () => ctx.circuit.assertOut(w, { y: mod(expected + 1n, BN254_FR).toString() }),
            "assertOut must reject a y one off the circuit's",
        );
    });
});
