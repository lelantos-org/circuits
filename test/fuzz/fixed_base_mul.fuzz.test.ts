// Property-based coverage for `lib/fixed_base_mul.circom`.
//
// The unit suite [test/gadgets/fixed_base_mul.test.ts](../gadgets/fixed_base_mul.test.ts)
// enumerates the small widths exhaustively and sweeps the window boundaries at
// full width. This file covers the 252-bit scalar space, where 63 windows
// interact and a carry bug appears only for particular nibble patterns.
//
// Agreement with circomlib's EscalarMulFix is checked over arbitrary scalars.
// The committed `vectors/` pin the same equality for the witnesses they carry;
// identical group elements mean identical cv, cv_dep, leaves and roots.

import { expect } from "chai";
import * as fc from "fast-check";

import { H_BASE, BABYJUB_SUBGROUP_ORDER, type Field, type Point } from "../helpers";
import { fixturePath, readPoint } from "../lib/circuit";
import { scalarBits } from "../lib/inputs";
import { fcParamsFor, arbBlinder, MAX_BLINDER } from "./arbitraries";
import { RCV_BITS as WIDTH, TIMEOUT_HEAVY } from "../lib/constants";
import { useCircuits } from "../lib/harness";

const WRAPPER = fixturePath("test_fixed_base_mul.circom");
const REFERENCE = fixturePath("test_fixed_base_mul_reference.circom");
const RAW_BITS = fixturePath("test_fixed_base_mul_bits.circom");
const fcParams = fcParamsFor("FIXEDBASE");

describe("fuzz: FixedBaseMul", function () {
    this.timeout(TIMEOUT_HEAVY);

    const ctx = useCircuits({ current: WRAPPER, reference: REFERENCE, raw: RAW_BITS });

    async function mul(scalar: Field): Promise<Point> {
        return readPoint(await ctx.circuits.current.calculateWitness({ scalar: scalar.toString() }, true));
    }

    it("matches the reference scalar multiplication", async () => {
        await fc.assert(
            fc.asyncProperty(arbBlinder(), async (s) => {
                expect(await mul(s)).to.deep.equal(ctx.J.mulPointEscalar(H_BASE, s));
            }),
            fcParams,
        );
    });

    it("matches circomlib EscalarMulFix", async () => {
        await fc.assert(
            fc.asyncProperty(arbBlinder(), async (s) => {
                const w = await ctx.circuits.reference.calculateWitness({ scalar: s.toString() }, true);
                // circomlib[2] then windowed[2], in declaration order
                expect(readPoint(w, 0), `divergence at ${s}`).to.deep.equal(readPoint(w, 2));
            }),
            fcParams,
        );
    });

    // Homomorphism pins the gadget to scalar multiplication rather than another
    // function that agrees on the values enumerated elsewhere.
    // Both addends stay under 2^251 so the sum stays inside Num2Bits(252).
    it("is additively homomorphic in the scalar", async () => {
        const half = fc.bigInt(0n, (1n << 251n) - 1n);
        await fc.assert(
            fc.asyncProperty(half, half, async (a, b) => {
                const [pa, pb, pab] = [await mul(a), await mul(b), await mul(a + b)];
                expect(ctx.J.addPoint(pa, pb), `a=${a} b=${b}`).to.deep.equal(pab);
            }),
            fcParams,
        );
    });

    // The gadget does not reduce the scalar; the group does. Adding the subgroup
    // order must not change the result.
    it("is invariant under adding the subgroup order", async () => {
        const room = fc.bigInt(0n, MAX_BLINDER - BABYJUB_SUBGROUP_ORDER);
        await fc.assert(
            fc.asyncProperty(room, async (a) => {
                expect(await mul(a + BABYJUB_SUBGROUP_ORDER), `a=${a}`).to.deep.equal(await mul(a));
            }),
            fcParams,
        );
    });

    // An off-curve or small-order result indicates the window tables or the
    // accumulator left the group, as a wrong table constant would cause.
    it("always lands in the prime-order subgroup", async () => {
        await fc.assert(
            fc.asyncProperty(arbBlinder(), async (s) => {
                expect(ctx.J.inSubgroup(await mul(s)), `s=${s}`).to.equal(true);
            }),
            fcParams,
        );
    });

    // FixedBaseMul is FixedBaseMulBits plus a Num2Bits it owns, so the two must
    // agree on every boolean bit array.
    it("agrees with the raw bit interface", async () => {
        await fc.assert(
            fc.asyncProperty(arbBlinder(), async (s) => {
                const w = await ctx.circuits.raw.calculateWitness({ e: scalarBits(s, WIDTH) }, true);
                expect(readPoint(w), `s=${s}`).to.deep.equal(await mul(s));
            }),
            fcParams,
        );
    });
});
