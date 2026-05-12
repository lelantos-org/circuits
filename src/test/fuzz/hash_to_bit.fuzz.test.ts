// Property-based coverage for `lib/hash_to_bit.circom`.
//
// The unit file [src/test/hash_to_bit.test.ts](../hash_to_bit.test.ts) pins
// a handful of seeded QR / QNR cases. This file drives the gadget with
// fast-check over random 𝔽_r elements, asserting:
//   - honest (bit, y) witnesses from `fmdLegendreWitness` always verify;
//   - tampered `bit` always fails (with the same `y`);
//   - `(-y) mod R` re-verifies (gadget binds `y²`, not `y`);
//   - QR/QNR distribution is ~50/50 (sanity for the Legendre branch).

import { expect } from "chai";
import * as fc from "fast-check";

import {
    BN254_FR,
    FMD_LEGENDRE_QNR,
    fmdLegendreWitness,
    legendreSymbol,
} from "@lelantos-org/sdk/crypto";
import { fixturePath, loadCircuit } from "../lib/circuit";
import { expectWitnessFails } from "../lib/expect";
import { fcParams, arbField } from "./arbitraries";

const WRAPPER = fixturePath("test_hash_to_bit.circom");
const R = BN254_FR;

function mod(a: bigint, p: bigint): bigint {
    const r = a % p;
    return r < 0n ? r + p : r;
}

// Avoid hash = 0 (range-check edge tested separately in unit file).
const arbNonzeroHash = arbField(R - 1n).filter(h => h !== 0n);

describe("HashToBit [fuzz]", function () {
    this.timeout(600_000);

    let circuit: any;
    before(async () => { circuit = await loadCircuit(WRAPPER); });

    it("honest fmdLegendreWitness verifies for any nonzero hash", async () => {
        await fc.assert(fc.asyncProperty(arbNonzeroHash, async hash => {
            const w = fmdLegendreWitness(hash);
            // Sanity: SDK Legendre matches its own classifier.
            const expectedBit = legendreSymbol(hash, R) === 1 ? 1 : 0;
            expect(w.bit).to.equal(expectedBit);
            await circuit.calculateWitness({
                hash: hash.toString(),
                bit: w.bit.toString(),
                y: w.y.toString(),
            }, true);
        }), fcParams);
    });

    it("flipping bit (keeping same y) rejects", async () => {
        await fc.assert(fc.asyncProperty(arbNonzeroHash, async hash => {
            const w = fmdLegendreWitness(hash);
            const flipped = 1 - w.bit;
            // hash = y² · (Z if bit=0 else 1). Flipping bit changes the
            // constraint side; honest y cannot satisfy both branches unless
            // Z = 1, which it never is (Z = FMD_LEGENDRE_QNR = 5).
            await expectWitnessFails(circuit, {
                hash: hash.toString(),
                bit: flipped.toString(),
                y: w.y.toString(),
            }, "bit-flip with honest y must reject");
        }), fcParams);
    });

    it("y → -y mod R re-verifies (gadget binds y², not y)", async () => {
        await fc.assert(fc.asyncProperty(arbNonzeroHash, async hash => {
            const w = fmdLegendreWitness(hash);
            const yNeg = mod(R - w.y, R);
            if (yNeg === w.y) return; // y = 0 case — only at hash = 0, filtered out
            await circuit.calculateWitness({
                hash: hash.toString(),
                bit: w.bit.toString(),
                y: yNeg.toString(),
            }, true);
        }), fcParams);
    });

    it("QR / QNR distribution ~50/50 (Legendre branch coverage)", async () => {
        // Sample 200 random hashes; Legendre is ~uniform over {-1,+1}.
        // 3σ bound on a fair coin: |#QR - 100| < ~22 (i.e. binomial std·3 ≈ 21.2).
        const N = 200;
        let qrCount = 0;
        for (let i = 0; i < N; i++) {
            // Cheap PRNG seeded from i — deterministic for repro.
            const hash = mod(BigInt(i + 1) * 0x9e3779b97f4a7c15n + 0xc0ffeen, R);
            if (hash === 0n) continue;
            qrCount += fmdLegendreWitness(hash).bit;
        }
        expect(qrCount).to.be.greaterThan(75);
        expect(qrCount).to.be.lessThan(125);
    });

    it("Z constant matches FMD_LEGENDRE_QNR and is a QNR in 𝔽_r", () => {
        // If this fails the gadget's hardcoded Z is out of sync with the
        // SDK and any "QNR" hash will be misclassified.
        expect(FMD_LEGENDRE_QNR).to.equal(5n);
        expect(legendreSymbol(FMD_LEGENDRE_QNR, R)).to.equal(-1);
    });
});
