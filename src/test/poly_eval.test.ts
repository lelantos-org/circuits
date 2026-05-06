import { expect } from "chai";

import { BN254_FR } from "@lelantos-org/sdk/crypto";
import { fixturePath, loadCircuit } from "./lib/circuit";

const WRAPPER = fixturePath("test_poly_eval.circom");
const N = 26;

function mod(a: bigint, p: bigint): bigint {
    const r = a % p;
    return r < 0n ? r + p : r;
}

function hornerEval(coeffs: bigint[], z: bigint): bigint {
    let acc = 0n;
    for (let i = coeffs.length - 1; i >= 0; i--) {
        acc = mod(acc * z + coeffs[i], BN254_FR);
    }
    return acc;
}

describe("PolyEval (Horner-form binding gadget)", function () {
    this.timeout(120000);

    let circuit: any;

    before(async () => {
        circuit = await loadCircuit(WRAPPER);
    });

    it("matches manual Σ c_k·z^k for random inputs", async () => {
        for (const seed of [1n, 7n, 0xdeadbeefn, 1234567890123456n]) {
            const coeffs = Array.from({ length: N }, (_, i) =>
                mod(seed * BigInt(i + 1) * 0x9e3779b97f4a7c15n, BN254_FR),
            );
            const z = mod(seed * 0x100000001b3n + 17n, BN254_FR);
            const expected = hornerEval(coeffs, z);
            const w = await circuit.calculateWitness(
                {
                    coeffs: coeffs.map((c) => c.toString()),
                    z: z.toString(),
                },
                true,
            );
            await circuit.assertOut(w, { y: expected.toString() });
        }
    });

    it("z = 0 ⇒ y = coeffs[0]", async () => {
        const coeffs = Array.from({ length: N }, (_, i) => BigInt(i + 1) * 11n);
        const w = await circuit.calculateWitness(
            { coeffs: coeffs.map((c) => c.toString()), z: "0" },
            true,
        );
        await circuit.assertOut(w, { y: coeffs[0].toString() });
    });

    it("z = 1 ⇒ y = Σ coeffs", async () => {
        const coeffs = Array.from({ length: N }, (_, i) => BigInt(i + 1));
        const sum = mod(coeffs.reduce((a, b) => a + b, 0n), BN254_FR);
        const w = await circuit.calculateWitness(
            { coeffs: coeffs.map((c) => c.toString()), z: "1" },
            true,
        );
        await circuit.assertOut(w, { y: sum.toString() });
    });

    it("z = p - 1 ⇒ alternating-sign sum", async () => {
        const coeffs = Array.from({ length: N }, (_, i) => BigInt(i + 1) * 3n);
        const z = mod(BN254_FR - 1n, BN254_FR);
        const expected = hornerEval(coeffs, z);
        const w = await circuit.calculateWitness(
            { coeffs: coeffs.map((c) => c.toString()), z: z.toString() },
            true,
        );
        await circuit.assertOut(w, { y: expected.toString() });
    });

    it("permuting coefficients alters y (Schwartz–Zippel sanity)", async () => {
        const coeffs = Array.from({ length: N }, (_, i) =>
            mod((BigInt(i) + 1n) * 0xc0ffeedeadbeefn, BN254_FR),
        );
        const z = 9876543210n;
        const yBase = hornerEval(coeffs, z);
        const swapped = [...coeffs];
        // swap two non-equal entries; coefficient ordering is load-bearing
        [swapped[0], swapped[1]] = [swapped[1], swapped[0]];
        const yPerm = hornerEval(swapped, z);
        expect(yBase).to.not.equal(yPerm);

        const w = await circuit.calculateWitness(
            { coeffs: swapped.map((c) => c.toString()), z: z.toString() },
            true,
        );
        await circuit.assertOut(w, { y: yPerm.toString() });
    });

    it("rejects mismatched y output", async () => {
        const coeffs = Array.from({ length: N }, (_, i) => BigInt(i + 1));
        const z = 42n;
        const expected = hornerEval(coeffs, z);
        const w = await circuit.calculateWitness(
            { coeffs: coeffs.map((c) => c.toString()), z: z.toString() },
            true,
        );
        let threw = false;
        try {
            await circuit.assertOut(w, { y: mod(expected + 1n, BN254_FR).toString() });
        } catch {
            threw = true;
        }
        expect(threw).to.equal(true);
    });
});
