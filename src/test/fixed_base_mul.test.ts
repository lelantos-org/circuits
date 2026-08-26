import { expect } from "chai";

import { Jubjub, H_BASE, BABYJUB_SUBGROUP_ORDER, type Field } from "./helpers";
import { fixturePath, loadCircuit, type CircuitTester } from "./lib/circuit";
import { expectWitnessFails } from "./lib/expect";
import { lcg } from "./lib/rand";
import { RCV_BITS as WIDTH, TIMEOUT_CIRCUIT } from "./lib/constants";

const WRAPPER = fixturePath("test_fixed_base_mul.circom");
const WIDTHS = fixturePath("test_fixed_base_mul_widths.circom");
const REFERENCE = fixturePath("test_fixed_base_mul_reference.circom");
const RAW_BITS = fixturePath("test_fixed_base_mul_bits.circom");
// Coverage for the FixedBaseMul gadget MulH uses: the compile-time window
// tables, the 4-bit mux factorisation, and the accumulator chain across window
// boundaries. Agreement with the reference implementation on concrete witnesses
// is pinned separately by the committed vectors under vectors/.
describe("FixedBaseMul (fixed-base scalar mul on Baby-Jubjub)", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    let circuit: CircuitTester;
    let J: Jubjub;

    before(async () => {
        circuit = await loadCircuit(WRAPPER);
        J = await Jubjub.build();
    });

    async function scalarMul(scalar: Field): Promise<[bigint, bigint]> {
        const w = await circuit.calculateWitness({ scalar: scalar.toString() }, true);
        return [w[1], w[2]];
    }

    async function expectMatches(scalar: Field, label: string): Promise<void> {
        const got = await scalarMul(scalar);
        const want = J.mulPointEscalar(H_BASE, scalar);
        expect(got[0], `${label} x`).to.equal(want[0]);
        expect(got[1], `${label} y`).to.equal(want[1]);
    }

    it("agrees with the reference on the identity and small scalars", async () => {
        for (const s of [0n, 1n, 2n, 3n, 7n, 8n, 15n]) {
            await expectMatches(s, `scalar=${s}`);
        }
    });

    // Entry 0 of every window table is the identity, so the accumulator needs
    // no offset compensation. A scalar of 0 must therefore return the identity
    // exactly, not H.
    it("returns the Edwards identity for scalar 0", async () => {
        const [x, y] = await scalarMul(0n);
        expect(x).to.equal(0n);
        expect(y).to.equal(1n);
    });

    // The mux selects on 4 bits at a time and the accumulator adds once per
    // window, so a carry out of any window is where an off-by-one in the table
    // stride would show. Walk every boundary.
    it("agrees across every 4-bit window boundary", async () => {
        for (let w = 0; w < Number(WIDTH) / 4; w++) {
            const base = 1n << BigInt(4 * w);
            for (const j of [0n, 1n, 7n, 8n, 15n]) {
                await expectMatches(base * j, `window ${w} entry ${j}`);
            }
        }
    });

    it("agrees on scalars that exercise the top window", async () => {
        for (const s of [
            (1n << 248n) - 1n,
            1n << 248n,
            (1n << 251n) - 1n,
            1n << 251n,
            (1n << WIDTH) - 1n,
        ]) {
            await expectMatches(s, `scalar=${s}`);
        }
    });

    // `ell` is the subgroup order, so ell*H is the identity and (ell+k)*H == k*H.
    // The gadget never reduces the scalar; the group does.
    it("wraps at the subgroup order", async () => {
        const ell = BABYJUB_SUBGROUP_ORDER;
        await expectMatches(ell - 1n, "ell-1");
        await expectMatches(ell, "ell");
        await expectMatches(ell + 1n, "ell+1");

        const [x, y] = await scalarMul(ell);
        expect(x, "ell*H must be the identity").to.equal(0n);
        expect(y, "ell*H must be the identity").to.equal(1n);
    });

    it("agrees on pseudorandom scalars", async () => {
        const next = lcg(0xdeadbeefcafebaben, WIDTH);
        for (let i = 0; i < 12; i++) {
            await expectMatches(next(), `random ${i}`);
        }
    });

    it("is additively homomorphic in the scalar", async () => {
        const a = 0x1234567890abcdefn;
        const b = 0xfedcba0987654321n;
        const pa = await scalarMul(a);
        const pb = await scalarMul(b);
        const pab = await scalarMul(a + b);
        expect(J.addPoint(pa, pb)).to.deep.equal(pab);
    });

    it("always lands in the prime-order subgroup", async () => {
        for (const s of [1n, 42n, (1n << 200n) + 7n, BABYJUB_SUBGROUP_ORDER - 1n]) {
            const p = await scalarMul(s);
            expect(J.inSubgroup(p), `scalar=${s}`).to.equal(true);
        }
    });

    // Num2Bits(252) is what bounds the blinder. Above it the decomposition has
    // no representation and witness generation must fail rather than wrap.
    it("FAILS when the scalar exceeds 2^252", async () => {
        await expectWitnessFails(
            circuit,
            { scalar: (1n << WIDTH).toString() },
            "Num2Bits(252) should reject a 253-bit scalar",
        );
    });

    // The boundary sweep above selects only table entries 0, 1, 7, 8 and 15. A
    // scalar whose every nibble is `k` selects entry `k` in all 63 windows at
    // once, so 16 witnesses cover the full table in every window.
    it("exercises every table entry in every window", async () => {
        const nWindows = Number(WIDTH) / 4;
        for (let k = 0n; k < 16n; k++) {
            let scalar = 0n;
            for (let i = 0; i < nWindows; i++) scalar |= k << BigInt(4 * i);
            await expectMatches(scalar, `every nibble = ${k}`);
        }
    });
});

// `vectors/` pins agreement for the specific witnesses it carries; this pins it
// for arbitrary scalars. A divergence moves every cv, cv_dep, leaf and root.
describe("FixedBaseMul vs circomlib EscalarMulFix", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    let circuit: CircuitTester;
    before(async () => {
        circuit = await loadCircuit(REFERENCE);
    });

    async function bothAgree(scalar: Field): Promise<void> {
        const w = await circuit.calculateWitness({ scalar: scalar.toString() }, true);
        // outputs in declaration order: circomlib[2] then windowed[2]
        expect(w[1], `x mismatch at ${scalar}`).to.equal(w[3]);
        expect(w[2], `y mismatch at ${scalar}`).to.equal(w[4]);
    }

    it("agrees on edge scalars", async () => {
        for (const s of [
            0n,
            1n,
            15n,
            16n,
            (1n << 128n) - 1n,
            (1n << 251n) - 1n,
            1n << 251n,
            (1n << WIDTH) - 1n,
            BABYJUB_SUBGROUP_ORDER - 1n,
            BABYJUB_SUBGROUP_ORDER,
        ]) {
            await bothAgree(s);
        }
    });

    it("agrees on pseudorandom scalars", async () => {
        const next = lcg(0x5eed1234abcdn, WIDTH);
        for (let i = 0; i < 16; i++) {
            await bothAgree(next());
        }
    });
});

describe("FixedBaseMul edge widths", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    let circuit: CircuitTester;
    let J: Jubjub;

    before(async () => {
        circuit = await loadCircuit(WIDTHS);
        J = await Jubjub.build();
    });

    // One witness covers all three widths; vary the one under test and hold the
    // others at a value inside their own range.
    async function run(s4: Field, s6: Field, s8: Field): Promise<bigint[]> {
        return circuit.calculateWitness(
            { s4: s4.toString(), s6: s6.toString(), s8: s8.toString() },
            true,
        );
    }

    function expectPoint(w: bigint[], offset: number, scalar: Field, label: string): void {
        const want = J.mulPointEscalar(H_BASE, scalar);
        expect(w[offset], `${label} x`).to.equal(want[0]);
        expect(w[offset + 1], `${label} y`).to.equal(want[1]);
    }

    // nWindows == 1: the accumulator is skipped and the output is the bare mux.
    it("is exhaustively correct at 4 bits (single-window path)", async () => {
        for (let k = 0n; k < 16n; k++) {
            const w = await run(k, 0n, 0n);
            expectPoint(w, 1, k, `s4=${k}`);
        }
    });

    // 6 is not a multiple of 4, so the top window has two padded selector bits.
    it("is exhaustively correct at 6 bits (zero-padded top window)", async () => {
        for (let k = 0n; k < 64n; k++) {
            const w = await run(0n, k, 0n);
            expectPoint(w, 3, k, `s6=${k}`);
        }
    });

    // Two full windows: every table entry against every other, exhaustively.
    it("is exhaustively correct at 8 bits (all 16 entries x 2 windows)", async () => {
        for (let k = 0n; k < 256n; k++) {
            const w = await run(0n, 0n, k);
            expectPoint(w, 5, k, `s8=${k}`);
        }
    });

    it("FAILS when a scalar exceeds its declared width", async () => {
        await expectWitnessFails(circuit, { s4: "16", s6: "0", s8: "0" }, "Num2Bits(4) should reject 16");
        await expectWitnessFails(circuit, { s4: "0", s6: "64", s8: "0" }, "Num2Bits(6) should reject 64");
        await expectWitnessFails(circuit, { s4: "0", s6: "0", s8: "256" }, "Num2Bits(8) should reject 256");
    });
});

// FixedBaseMulBits is the unguarded interface. These tests demonstrate the
// failure its DANGER comment describes: a non-boolean selector takes the output
// off the curve, and only the Num2Bits that FixedBaseMul owns prevents it.
describe("FixedBaseMulBits (raw, caller-constrained bits)", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    let circuit: CircuitTester;
    let J: Jubjub;

    before(async () => {
        circuit = await loadCircuit(RAW_BITS);
        J = await Jubjub.build();
    });

    function bitsOf(scalar: Field): string[] {
        return Array.from({ length: Number(WIDTH) }, (_, i) => ((scalar >> BigInt(i)) & 1n).toString());
    }

    it("agrees with the reference on boolean bit arrays", async () => {
        for (const s of [0n, 1n, 255n, (1n << 200n) + 12345n, BABYJUB_SUBGROUP_ORDER - 1n]) {
            const w = await circuit.calculateWitness({ e: bitsOf(s) }, true);
            const want = J.mulPointEscalar(H_BASE, s);
            expect([w[1], w[2]], `scalar=${s}`).to.deep.equal(want);
        }
    });

    it("leaves the curve when a selector bit is not boolean", async () => {
        const zeros = bitsOf(0n);

        const clean = await circuit.calculateWitness({ e: zeros }, true);
        expect([clean[1], clean[2]], "boolean input must give the identity").to.deep.equal([0n, 1n]);

        const nonBoolean = [...zeros];
        nonBoolean[0] = "2";
        const dirty = await circuit.calculateWitness({ e: nonBoolean }, true);

        // The result is not a curve point at all. An off-curve mux output can
        // make BabyAdd's `(1 + d*tau) * xout === ...` degenerate, turning a lost
        // booleanity constraint into an under-constrained one.
        expect(J.inSubgroup([dirty[1], dirty[2]]), "non-boolean input escapes the subgroup").to.equal(false);
    });
});
