// Unit tests for `lib/asset_gen.circom`: the per-asset value-commitment
// generator V^t = Pedersen(TAG_ASSET || asset_id_LE_64).
//
// Every value commitment in both circuits is taken against this point, and the
// asset-id registration gate (`scripts/check-asset-ids.ts`) models it
// arithmetically. Until now the model was only ever compared against the
// circomlibjs reference (`tooling/check_asset_ids.test.ts`), and the reference
// only against itself; nothing read the compiled gadget. These cases close that
// loop: circuit vs reference, and circuit vs the multiplier model the gate
// bounds are computed from.

import { expect } from "chai";

import { BABYJUB_SUBGROUP_ORDER, type Field, type Point } from "../helpers";
import { generatedFixture, readPoint } from "../lib/circuit";
import { expectWitnessFails } from "../lib/expect";
import { TIMEOUT_CIRCUIT, TWO_64 } from "../lib/constants";
import { useCircuit } from "../lib/harness";
import { assetMultiplier } from "../../scripts/check-asset-ids";

/** Ids spanning the range: the reserved 0, small sequential, and both ends. */
const IDS: Field[] = [0n, 1n, 2n, 3n, 7n, 16n, 0xffn, 0x1_0000_0000n, TWO_64 - 1n];

const ell = BABYJUB_SUBGROUP_ORDER;
const modEll = (x: bigint) => ((x % ell) + ell) % ell;

describe("HashToAssetGen (per-asset generator)", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useCircuit(generatedFixture("lib/asset_gen.circom", "HashToAssetGen", []));

    /** The compiled gadget's V^assetId. */
    async function gen(assetId: Field): Promise<Point> {
        const w = await ctx.circuit.calculateWitness({ asset_id: assetId.toString() }, true);
        await ctx.circuit.checkConstraints(w);
        return readPoint(w);
    }

    it("matches the circomlibjs reference across the id range", async () => {
        for (const id of IDS) {
            expect(await gen(id), `V^${id}`).to.deep.equal(ctx.J.hashToAssetGen(id));
        }
    });

    it("lands in the prime-order subgroup", async () => {
        for (const id of [0n, 1n, 0xdead_beefn, TWO_64 - 1n]) {
            expect(ctx.J.inSubgroup(await gen(id)), `V^${id}`).to.equal(true);
        }
    });

    it("separates distinct ids", async () => {
        const seen = new Map<string, Field>();
        for (const id of IDS) {
            const key = (await gen(id)).join(",");
            expect(seen.has(key), `V^${id} collides with V^${seen.get(key)}`).to.equal(false);
            seen.set(key, id);
        }
    });

    it("FAILS at 2^64, the Num2Bits(64) bound on the id", async () => {
        await expectWitnessFails(
            ctx.circuit,
            { asset_id: TWO_64.toString() },
            "an asset id wider than 64 bits must be rejected",
            { template: "Num2Bits" },
        );
    });

    // `check-asset-ids.ts` derives its separation bounds from
    // `m(a) = assetMultiplier(a)` with `V^a == m(a)·BASE0`. Compared against the
    // COMPILED gadget here: `tooling/check_asset_ids.test.ts` compares the model
    // against circomlibjs, which leaves the model and the circuit connected only
    // by the gadget header's claim that the two agree.
    it("agrees with the multiplier model the registration gate is built on", async () => {
        // Recover BASE0 = m(0)^-1 · V^0 from the circuit's own V^0.
        let [oldR, r] = [modEll(assetMultiplier(0n)), ell];
        let [oldS, s] = [1n, 0n];
        while (r !== 0n) {
            const q = oldR / r;
            [oldR, r] = [r, oldR - q * r];
            [oldS, s] = [s, oldS - q * s];
        }
        const base0 = ctx.J.mulPointEscalar(await gen(0n), modEll(oldS));

        for (const id of IDS) {
            expect(
                ctx.J.mulPointEscalar(base0, modEll(assetMultiplier(id))),
                `m(${id})·BASE0 must equal the compiled V^${id}`,
            ).to.deep.equal(await gen(id));
        }
    });

    // The consequence of that model, and the reason `PerAssetValueBalance`
    // compares asset ids as field elements instead of trusting the point sum:
    // the generators are not independent. `transact/multi_asset.test.ts` spends
    // this relation as a forgery attempt against the full circuit.
    it("has publicly known relative discrete logs: V^1 ⊕ V^3 == 2·V^2", async () => {
        const [v1, v2, v3] = [await gen(1n), await gen(2n), await gen(3n)];
        expect(ctx.J.addPoint(v1, v3)).to.deep.equal(ctx.J.mulPointEscalar(v2, 2n));
    });
});
