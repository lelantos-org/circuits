// Property-based coverage for `lib/clue.circom` (FMD2 ClueCheck gadget,
// γ = 5). The unit file [src/test/clue.test.ts](../clue.test.ts) seeds a
// handful of (r, dk) pairs. This file drives the gadget across random r
// ∈ [1, BABYJUB_SUBGROUP_ORDER) and random γ-tuples of detection-key
// scalars, asserting:
//   - the SDK-derived honest witness always verifies and matches `R = r·G_8`;
//   - flipping one bit of `clue_bits` rejects (and only that bit);
//   - replacing one `fk` row with a different subgroup point rejects.

import { expect } from "chai";
import * as fc from "fast-check";

import {
    BABYJUB_SUBGROUP_ORDER,
    BN254_FR,
    fmdLegendreWitness,
    Jubjub,
    Poseidon,
} from "@lelantos-org/sdk/crypto";
import { TAG_FMD_BIT } from "@lelantos-org/sdk";
import { fixturePath, loadCircuit } from "../lib/circuit";
import { expectWitnessFails } from "../lib/expect";
import { fcParamsFor, mod, arbDistinctBigInt } from "./arbitraries";

const WRAPPER = fixturePath("test_clue.circom");
const GAMMA = 5;
const fcParams = fcParamsFor("CLUE");

interface ClueWitness {
    r: bigint;
    fk: [bigint, bigint][];
    clue_bits: bigint;
    legendre_bit: number[];
    legendre_y: bigint[];
    Rx: bigint;
    Ry: bigint;
}

function buildHonest(J: Jubjub, P: Poseidon, r: bigint, dkScalars: bigint[]): ClueWitness {
    const rMod = mod(r, BABYJUB_SUBGROUP_ORDER);
    const R_ = J.mulPointEscalar(J.base8, rMod);
    const fk = dkScalars.map(x => J.mulPointEscalar(J.base8, x)) as [bigint, bigint][];

    const legendre_bit: number[] = [];
    const legendre_y: bigint[] = [];
    let cBitsPacked = 0n;
    for (let i = 0; i < GAMMA; i++) {
        const S = J.mulPointEscalar(fk[i], rMod);
        const h = P.hash([TAG_FMD_BIT, R_[0], R_[1], BigInt(i), S[0], S[1]]);
        const w = fmdLegendreWitness(h);
        legendre_bit.push(w.bit);
        legendre_y.push(w.y);
        const c = 1 - w.bit;
        if (c) cBitsPacked |= 1n << BigInt(i);
    }
    return { r: rMod, fk, clue_bits: cBitsPacked, legendre_bit, legendre_y, Rx: R_[0], Ry: R_[1] };
}

function toInput(w: ClueWitness): any {
    return {
        r: w.r.toString(),
        fk: w.fk.map(([x, y]) => [x.toString(), y.toString()]),
        clue_bits: w.clue_bits.toString(),
        legendre_bit: w.legendre_bit.map(b => b.toString()),
        legendre_y: w.legendre_y.map(y => y.toString()),
    };
}

// Subgroup scalar — keep away from 0 so r·G_8 is non-identity.
const arbSubgroupScalar = fc.bigInt(1n, BABYJUB_SUBGROUP_ORDER - 1n);
const arbDkVec = fc.array(arbSubgroupScalar, { minLength: GAMMA, maxLength: GAMMA });

// Pin boundary cases that uniform draws rarely hit.
const HONEST_EXAMPLES: [bigint, bigint[]][] = [
    [1n, [1n, 1n, 1n, 1n, 1n]],
    [BABYJUB_SUBGROUP_ORDER - 1n, [1n, 2n, 3n, 4n, 5n]],
    [2n, [BABYJUB_SUBGROUP_ORDER - 1n, BABYJUB_SUBGROUP_ORDER - 1n, BABYJUB_SUBGROUP_ORDER - 1n, BABYJUB_SUBGROUP_ORDER - 1n, BABYJUB_SUBGROUP_ORDER - 1n]],
];

describe("ClueCheck [fuzz, γ=5]", function () {
    this.timeout(1_800_000);

    let circuit: any;
    let J: Jubjub;
    let P: Poseidon;

    before(async () => {
        J = await Jubjub.build();
        P = await Poseidon.build();
        circuit = await loadCircuit(WRAPPER);
    });

    it("honest witness verifies; R = r·G_8 matches output", async () => {
        await fc.assert(fc.asyncProperty(arbSubgroupScalar, arbDkVec, async (r, dk) => {
            const w = buildHonest(J, P, r, dk);
            const wt = await circuit.calculateWitness(toInput(w), true);
            await circuit.assertOut(wt, { Rx: w.Rx.toString(), Ry: w.Ry.toString() });
        }), fcParamsFor("CLUE", { examples: HONEST_EXAMPLES }));
    });

    it("single-bit flip in clue_bits rejects", async () => {
        await fc.assert(fc.asyncProperty(arbSubgroupScalar, arbDkVec, fc.integer({ min: 0, max: GAMMA - 1 }),
            async (r, dk, idx) => {
                const w = buildHonest(J, P, r, dk);
                const tampered = { ...w, clue_bits: w.clue_bits ^ (1n << BigInt(idx)) };
                await expectWitnessFails(circuit, toInput(tampered), `flipping clue_bits[${idx}] must reject`);
            }), fcParams);
    });

    it("replacing fk[i] with a different subgroup point rejects", async () => {
        await fc.assert(fc.asyncProperty(
            arbSubgroupScalar, arbDkVec,
            fc.integer({ min: 0, max: GAMMA - 1 }),
            // Pick `otherScalar` distinct from a sentinel inside the dk vector
            // via arbDistinctBigInt; we then override the chosen index with
            // the second draw so swap always lands on a different point.
            arbDistinctBigInt(1n, BABYJUB_SUBGROUP_ORDER - 1n),
            async (r, dk, idx, [_anchor, otherScalar]) => {
                // Ensure otherScalar !== dk[idx]; if collision, bump.
                const safeOther = otherScalar === dk[idx]
                    ? (otherScalar === BABYJUB_SUBGROUP_ORDER - 1n ? 1n : otherScalar + 1n)
                    : otherScalar;
                const w = buildHonest(J, P, r, dk);
                const newFk = J.mulPointEscalar(J.base8, safeOther) as [bigint, bigint];
                const tampered = {
                    ...w,
                    fk: w.fk.map((p, i) => (i === idx ? newFk : p)),
                };
                await expectWitnessFails(circuit, toInput(tampered), `swapping fk[${idx}] must reject`);
            }), fcParams);
    });

    it("rejects sender-forgot-flip (clue_bits === legendre_bit packing)", async () => {
        await fc.assert(fc.asyncProperty(arbSubgroupScalar, arbDkVec, async (r, dk) => {
            const w = buildHonest(J, P, r, dk);
            let unflipped = 0n;
            for (let i = 0; i < GAMMA; i++) if (w.legendre_bit[i]) unflipped |= 1n << BigInt(i);
            if (unflipped === w.clue_bits) return; // happens when all bits are 0
            await expectWitnessFails(circuit, toInput({ ...w, clue_bits: unflipped }),
                "unflipped clue_bits must reject");
        }), fcParams);
    });

    it("rejects r outside strict 𝔽_r range (Num2Bits_strict guard)", async () => {
        const w = buildHonest(J, P, 1n, [1n, 1n, 1n, 1n, 1n]);
        await expectWitnessFails(circuit, toInput({ ...w, r: BN254_FR }),
            "r = R must trip Num2Bits_strict");
    });
});
