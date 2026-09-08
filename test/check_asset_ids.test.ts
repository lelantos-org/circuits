// Coverage for the asset-id separation gate.
//
// `tree_update_batch` pins a deposit leaf only by
// `cv_dep == leaf_public_in · V^leaf_asset + rcv · H`, and every `V^a` is a
// known multiple `m(a) · BASE0`, so `v · m(a) == v' · m(a')` with both values
// under 2^64 would let a depositor pay one asset and spend the leaf as another.
// These cases pin the gate's multiplier model against the compiled
// `HashToAssetGen` and check that a colliding pair is flagged.

import { expect } from "chai";

import { BABYJUB_SUBGROUP_ORDER, POW_2_64 } from "./helpers";
import { TIMEOUT_FAST } from "./lib/constants";
import { assetMultiplier, classifyPair } from "../scripts/check-asset-ids";
import { useGadgets } from "./lib/harness";

/**
 * A pair whose multipliers share a factor large enough that the minimal
 * colliding values both land under 2^64.
 */
const COLLIDING: [bigint, bigint] = [0x067f8028c470047cn, 0x067f8028c472818bn];

describe("asset id separation", function () {
    this.timeout(TIMEOUT_FAST);

    const ctx = useGadgets();

    // The model is arithmetic over circomlib's signed 4-bit windows, so the
    // bounds the gate reports hold only while it tracks the compiled gadget.
    it("assetMultiplier reproduces HashToAssetGen", () => {
        const ell = BABYJUB_SUBGROUP_ORDER;
        const mod = (x: bigint) => ((x % ell) + ell) % ell;

        // Recover BASE0 from V^0 and m(0), so the comparison is a round trip
        // through circomlibjs rather than a restated constant.
        const m0 = assetMultiplier(0n);
        let [oldR, r] = [mod(m0), ell];
        let [oldS, s] = [1n, 0n];
        while (r !== 0n) {
            const q = oldR / r;
            [oldR, r] = [r, oldR - q * r];
            [oldS, s] = [s, oldS - q * s];
        }
        const base0 = ctx.J.mulPointEscalar(ctx.J.hashToAssetGen(0n), ((oldS % ell) + ell) % ell);

        for (const id of [0n, 1n, 2n, 3n, 7n, 99n, 0xdeadbeefn, ...COLLIDING]) {
            const modelled = ctx.J.mulPointEscalar(base0, mod(assetMultiplier(id)));
            const actual = ctx.J.hashToAssetGen(id);
            expect(modelled[0], `x at id ${id}`).to.equal(actual[0]);
            expect(modelled[1], `y at id ${id}`).to.equal(actual[1]);
        }
    });

    it("flags a pair that collides inside the 64-bit value range", () => {
        const v = classifyPair(COLLIDING[0], COLLIDING[1]);
        expect(v.colliding, "the known pair must be flagged").to.equal(true);
        expect(v.values).to.not.equal(null);
        // Plain comparisons: chai's numeric assertions reject bigint operands.
        expect(v.values!.va < POW_2_64, "va must fit the circuit's value range").to.equal(true);
        expect(v.values!.vb < POW_2_64, "vb must fit the circuit's value range").to.equal(true);
    });

    // The claimed collision must hold on the curve, not just in the model.
    it("the flagged pair really shares a value-commitment point", () => {
        const [a, b] = COLLIDING;
        const { va, vb } = classifyPair(a, b).values!;
        const pa = ctx.J.mulPointEscalar(ctx.J.hashToAssetGen(a), va);
        const pb = ctx.J.mulPointEscalar(ctx.J.hashToAssetGen(b), vb);
        expect(pa[0]).to.equal(pb[0]);
        expect(pa[1]).to.equal(pb[1]);
    });

    it("clears small sequential ids by a wide margin", () => {
        const ids = [1n, 2n, 3n, 4n, 5n, 7n, 99n, 1000n];
        for (let i = 0; i < ids.length; i++) {
            for (let j = i + 1; j < ids.length; j++) {
                const v = classifyPair(ids[i], ids[j]);
                expect(v.colliding, `${ids[i]} / ${ids[j]} must not collide`).to.equal(false);
            }
        }
    });
});
