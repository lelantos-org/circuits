// Property-based coverage for `lib/fixed_base_mul.circom`.
//
// The unit suite [src/test/fixed_base_mul.test.ts](../fixed_base_mul.test.ts)
// enumerates the small widths exhaustively and sweeps the window boundaries at
// full width. This file covers what enumeration cannot reach: the 252-bit
// scalar space, where 63 windows interact and a carry-shaped bug shows only for
// particular nibble patterns.
//
// Agreement with circomlib's EscalarMulFix is checked over arbitrary scalars.
// The committed `vectors/` pin the same equality for the witnesses they carry;
// identical group elements mean identical cv, cv_dep, leaves and roots.

import { expect } from "chai";
import * as fc from "fast-check";

import { Jubjub, H_BASE, BABYJUB_SUBGROUP_ORDER, type Field } from "../helpers";
import { fixturePath, loadCircuit } from "../lib/circuit";
import { fcParamsFor, arbBlinder, MAX_BLINDER } from "./arbitraries";
import { RCV_BITS as WIDTH, TIMEOUT_HEAVY } from "../lib/constants";

const WRAPPER = fixturePath("test_fixed_base_mul.circom");
const LEGACY = fixturePath("test_fixed_base_mul_legacy.circom");
const RAW_BITS = fixturePath("test_fixed_base_mul_bits.circom");
const fcParams = fcParamsFor("FIXEDBASE");

describe("fuzz: FixedBaseMul", function () {
    this.timeout(TIMEOUT_HEAVY);

    let current: any;
    let legacy: any;
    let raw: any;
    let J: Jubjub;

    before(async () => {
        [current, legacy, raw, J] = await Promise.all([
            loadCircuit(WRAPPER),
            loadCircuit(LEGACY),
            loadCircuit(RAW_BITS),
            Jubjub.build(),
        ]);
    });

    async function mul(scalar: Field): Promise<[bigint, bigint]> {
        const w = await current.calculateWitness({ scalar: scalar.toString() }, true);
        return [w[1], w[2]];
    }

    it("matches the reference scalar multiplication", async () => {
        await fc.assert(
            fc.asyncProperty(arbBlinder(), async (s) => {
                expect(await mul(s)).to.deep.equal(J.mulPointEscalar(H_BASE, s));
            }),
            fcParams,
        );
    });

    // The migration argument, at scale.
    it("matches circomlib EscalarMulFix", async () => {
        await fc.assert(
            fc.asyncProperty(arbBlinder(), async (s) => {
                const w = await legacy.calculateWitness({ scalar: s.toString() }, true);
                // legacy[2] then current[2], in declaration order
                expect([w[1], w[2]], `divergence at ${s}`).to.deep.equal([w[3], w[4]]);
            }),
            fcParams,
        );
    });

    // Homomorphism pins the gadget to scalar multiplication rather than to some
    // other function that happens to agree on the values enumerated elsewhere.
    // Both addends stay under 2^251 so the sum stays inside Num2Bits(252).
    it("is additively homomorphic in the scalar", async () => {
        const half = fc.bigInt(0n, (1n << 251n) - 1n);
        await fc.assert(
            fc.asyncProperty(half, half, async (a, b) => {
                const [pa, pb, pab] = [await mul(a), await mul(b), await mul(a + b)];
                expect(J.addPoint(pa, pb), `a=${a} b=${b}`).to.deep.equal(pab);
            }),
            fcParams,
        );
    });

    // The gadget never reduces the scalar; the group does. Adding the subgroup
    // order must be invisible.
    it("is invariant under adding the subgroup order", async () => {
        const room = fc.bigInt(0n, MAX_BLINDER - BABYJUB_SUBGROUP_ORDER);
        await fc.assert(
            fc.asyncProperty(room, async (a) => {
                expect(await mul(a + BABYJUB_SUBGROUP_ORDER), `a=${a}`).to.deep.equal(await mul(a));
            }),
            fcParams,
        );
    });

    // An off-curve or small-order result would mean the window tables or the
    // accumulator had left the group — the failure mode a wrong table constant
    // produces.
    it("always lands in the prime-order subgroup", async () => {
        await fc.assert(
            fc.asyncProperty(arbBlinder(), async (s) => {
                expect(J.inSubgroup(await mul(s)), `s=${s}`).to.equal(true);
            }),
            fcParams,
        );
    });

    // FixedBaseMul is FixedBaseMulBits plus a Num2Bits it owns. If the two ever
    // disagreed, the safe wrapper would not be wrapping the thing it claims to.
    it("agrees with the raw bit interface", async () => {
        await fc.assert(
            fc.asyncProperty(arbBlinder(), async (s) => {
                const bits = Array.from({ length: Number(WIDTH) }, (_, i) =>
                    ((s >> BigInt(i)) & 1n).toString(),
                );
                const w = await raw.calculateWitness({ e: bits }, true);
                expect([w[1], w[2]], `s=${s}`).to.deep.equal(await mul(s));
            }),
            fcParams,
        );
    });
});
