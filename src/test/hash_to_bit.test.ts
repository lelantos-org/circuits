import { expect } from "chai";

import {
    BN254_FR,
    FMD_LEGENDRE_QNR,
    fmdLegendreWitness,
    legendreSymbol,
    modInverse,
    modSqrt,
    Poseidon,
} from "@lelantos-org/sdk/crypto";
import { fixturePath, loadCircuit } from "./lib/circuit";
import { expectWitnessFails } from "./lib/expect";

const WRAPPER = fixturePath("test_hash_to_bit.circom");

function mod(a: bigint, p: bigint): bigint {
    const r = a % p;
    return r < 0n ? r + p : r;
}

describe("HashToBit (Legendre symbol gadget)", function () {
    this.timeout(180000);

    let circuit: any;
    let P: Poseidon;

    before(async () => {
        P = await Poseidon.build();
        circuit = await loadCircuit(WRAPPER);
    });

    it("Z=5 is a QNR in BN254 scalar field", () => {
        // Sanity check: gadget hardcodes Z=5; if this assertion fails, the
        // circuit constant must change in lockstep with FMD_LEGENDRE_QNR.
        expect(FMD_LEGENDRE_QNR).to.equal(5n);
        expect(legendreSymbol(FMD_LEGENDRE_QNR, BN254_FR)).to.equal(-1);
    });

    it("accepts honest witness for QR hashes", async () => {
        // Pick a known QR: any nonzero square.
        for (const seed of [1n, 7n, 12345n, 0xdeadbeefn]) {
            const hash = mod(seed * seed, BN254_FR);
            const w = fmdLegendreWitness(hash);
            expect(w.bit).to.equal(1);
            await circuit.calculateWitness(
                { hash: hash.toString(), bit: w.bit.toString(), y: w.y.toString() },
                true,
            );
        }
    });

    it("accepts honest witness for QNR hashes", async () => {
        // Construct a QNR: Z · (square) is a non-residue since Z is QNR.
        for (const seed of [3n, 11n, 0xc0den]) {
            const hash = mod(FMD_LEGENDRE_QNR * seed * seed, BN254_FR);
            expect(legendreSymbol(hash, BN254_FR)).to.equal(-1);
            const w = fmdLegendreWitness(hash);
            expect(w.bit).to.equal(0);
            await circuit.calculateWitness(
                { hash: hash.toString(), bit: w.bit.toString(), y: w.y.toString() },
                true,
            );
        }
    });

    it("agrees with Poseidon-output Legendre on random inputs", async () => {
        // Honest distribution check: ~50/50 split across many samples.
        const N = 64;
        let qrCount = 0;
        for (let i = 0; i < N; i++) {
            const h = P.hash([BigInt(i), BigInt(i * i + 7)]);
            const w = fmdLegendreWitness(h);
            qrCount += w.bit;
            await circuit.calculateWitness(
                { hash: h.toString(), bit: w.bit.toString(), y: w.y.toString() },
                true,
            );
        }
        // 64 fair coins: probability of <12 or >52 ≈ 2^-30. Loose bound.
        expect(qrCount).to.be.greaterThan(12);
        expect(qrCount).to.be.lessThan(52);
    });

    it("rejects hash = 0", async () => {
        await expectWitnessFails(circuit, { hash: "0", bit: "1", y: "0" });
    });

    it("rejects flipped bit (claiming QNR is QR)", async () => {
        const seed = 17n;
        const qnr = mod(FMD_LEGENDRE_QNR * seed * seed, BN254_FR);
        // No y exists with y² == qnr in 𝔽_r, so no witness can satisfy
        // bit=1. Try any y; constraint hash === y² · 1 fails.
        await expectWitnessFails(circuit, {
            hash: qnr.toString(),
            bit: "1",
            y: seed.toString(),
        });
    });

    it("rejects flipped bit (claiming QR is QNR)", async () => {
        const seed = 23n;
        const qr = mod(seed * seed, BN254_FR);
        // Claiming QNR with bit=0 forces hash == y² · Z. Need y² · Z == seed²;
        // y² = seed² · Z⁻¹. Z⁻¹ is QNR (inverse of QNR is QNR), so y² is QNR
        // and no y exists. Constraint fails.
        const zInv = modInverse(FMD_LEGENDRE_QNR, BN254_FR);
        const target = mod(qr * zInv, BN254_FR);
        const fakeY = modSqrt(target, BN254_FR); // null
        expect(fakeY).to.equal(null);
        await expectWitnessFails(circuit, {
            hash: qr.toString(),
            bit: "0",
            y: seed.toString(),
        });
    });

    it("rejects non-boolean bit", async () => {
        const hash = mod(7n * 7n, BN254_FR);
        await expectWitnessFails(circuit, {
            hash: hash.toString(),
            bit: "2",
            y: "7",
        });
    });
});
