// Property-based coverage for `PerAssetValueBalance` in lib/balance.circom.
//
// The unit cases in [test/gadgets/balance.test.ts](../gadgets/balance.test.ts)
// pin one hand-built shape and every single-slot perturbation of it. This file
// varies the thing a fixed shape cannot: which asset sits in which slot. The
// gadget compares all N_IN + N_OUT + 1 candidates against all N_IN + N_OUT + 1
// slots, so the asset layout — duplicates, an asset in one slot only, a
// transparent bucket naming an asset no note carries — decides which of its
// ~110 IsEqual comparators are true, and a mis-indexed candidate row shows up
// only for the layouts that separate it from its neighbours.
//
// Driving this through `transact_4x6` is what makes such coverage unaffordable:
// a trial there costs a tree, N_IN authentication paths and a 100k-constraint
// witness. Here a trial is a field-array witness over ~1k constraints.
// `transact/multi_asset.test.ts` carries the end-to-end shapes.

import * as fc from "fast-check";

import { generatedFixture } from "../lib/circuit";
import { expectAccepts, expectWitnessFails } from "../lib/expect";
import { perAssetValueBalanceInput } from "../lib/inputs";
import { N_IN, N_OUT, TIMEOUT_HEAVY } from "../lib/constants";
import { useCircuit } from "../lib/harness";
import { arbBalancedAssetShape, fcParamsFor, type AssetBalanceShape } from "./arbitraries";

const fcParams = fcParamsFor("BALANCE");
const arbShape = arbBalancedAssetShape(N_IN, N_OUT);

/** Slot count the perturbation properties index into: 4 in, 6 out, 2 buckets. */
const SLOTS = N_IN + N_OUT + 2;

/** `shape` with `+1` on slot `k`, numbered inputs, then outputs, then buckets. */
function bump(shape: AssetBalanceShape, k: number): AssetBalanceShape {
    const out: AssetBalanceShape = {
        ...shape,
        inValue: [...shape.inValue],
        outValue: [...shape.outValue],
    };
    if (k < N_IN) out.inValue[k] += 1n;
    else if (k < N_IN + N_OUT) out.outValue[k - N_IN] += 1n;
    else if (k === N_IN + N_OUT) out.publicIn += 1n;
    else out.publicOut += 1n;
    return out;
}

describe("PerAssetValueBalance [fuzz]", function () {
    this.timeout(TIMEOUT_HEAVY);

    const ctx = useCircuit(
        generatedFixture("lib/balance.circom", "PerAssetValueBalance", [N_IN, N_OUT]),
    );

    it("accepts every per-asset balanced layout", async () => {
        await fc.assert(fc.asyncProperty(arbShape, async shape => {
            await expectAccepts(ctx.circuit, perAssetValueBalanceInput(shape));
        }), fcParams);
    });

    // One unit, anywhere: every value slot and both transparent buckets sit on
    // some candidate row, and no other slot can absorb the difference.
    it("rejects a single extra unit in any slot", async () => {
        await fc.assert(fc.asyncProperty(
            arbShape,
            fc.nat({ max: SLOTS - 1 }),
            async (shape, k) => {
                await expectWitnessFails(
                    ctx.circuit,
                    perAssetValueBalanceInput(bump(shape, k)),
                    `slot ${k} must sit on a candidate row that rejects +1`,
                );
            },
        ), fcParams);
    });

    // Relabelling moves a slot's value from one candidate row to another, so
    // both rows break. The drawn id is one no slot carries, which is also the
    // case a registry must worry about: an id that exists on chain but not in
    // this transaction.
    it("rejects relabelling a valued output to an asset nothing else carries", async () => {
        await fc.assert(fc.asyncProperty(
            arbShape,
            fc.nat({ max: N_OUT - 1 }),
            async (shape, j) => {
                fc.pre(shape.outValue[j] > 0n);
                const fresh = fresh64(shape);
                const outAsset = [...shape.outAsset];
                outAsset[j] = fresh;
                await expectWitnessFails(
                    ctx.circuit,
                    perAssetValueBalanceInput({ ...shape, outAsset }),
                    `out_asset[${j}] relabelled to ${fresh} must break two candidate rows`,
                );
            },
        ), fcParams);
    });

    it("rejects moving value between two differently-labelled output slots", async () => {
        await fc.assert(fc.asyncProperty(
            arbShape,
            fc.nat({ max: N_OUT - 1 }),
            fc.nat({ max: N_OUT - 1 }),
            async (shape, a, b) => {
                fc.pre(shape.outAsset[a] !== shape.outAsset[b]);
                fc.pre(shape.outValue[a] > 0n);
                const outValue = [...shape.outValue];
                outValue[a] -= 1n;
                outValue[b] += 1n;
                await expectWitnessFails(
                    ctx.circuit,
                    perAssetValueBalanceInput({ ...shape, outValue }),
                    "scalar totals are unchanged, so only the per-asset rows reject this",
                );
            },
        ), fcParams);
    });

    // The candidate list is built from the slots in order, so a permutation
    // reorders it. Conservation is a property of the multiset, not the order.
    it("is invariant under permuting the input slots", async () => {
        await fc.assert(fc.asyncProperty(
            arbShape,
            fc.nat({ max: N_IN - 1 }),
            fc.nat({ max: N_IN - 1 }),
            async (shape, a, b) => {
                const inAsset = [...shape.inAsset];
                const inValue = [...shape.inValue];
                [inAsset[a], inAsset[b]] = [inAsset[b], inAsset[a]];
                [inValue[a], inValue[b]] = [inValue[b], inValue[a]];
                await expectAccepts(
                    ctx.circuit,
                    perAssetValueBalanceInput({ ...shape, inAsset, inValue }),
                );
            },
        ), fcParams);
    });
});

/** An asset id no slot of `shape` carries, and not the public one either. */
function fresh64(shape: AssetBalanceShape): bigint {
    const taken = new Set([...shape.inAsset, ...shape.outAsset, shape.publicAssetId]);
    let id = 0xa55e7_0000n;
    while (taken.has(id)) id += 1n;
    return id;
}
