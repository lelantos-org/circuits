// Active-slot rules, on every slot of a full batch.
//
// Steps 1, 2 and 5 of tree_update_batch.circom are loops over slots. A loop that
// stops early, or reads slot 0 where it should read slot k, still rejects a
// defect planted in slot 0. Each row below plants its defect in every slot k of
// a batch with actual_count = MAX_L, so every slot is active and the padding
// constraint (step 4) cannot be what rejects. The tree is rebuilt over the
// defective leaf, so the roots agree with it and only the rule under test can.

import { TAG_CM, buildInner, commitWithInner, mod, type Field } from "../helpers";
import { rebindFiatShamir, type BatchWitness, type LeafWitness } from "../lib/batch";
import { MAX_L, TIMEOUT_HEAVY, TWO_64 } from "../lib/constants";
import { expectBatchAccepts, expectBatchRejects, useBatchCircuit } from "./setup";

describe("tree_update_batch / active-slot rules on every slot", function () {
    this.timeout(TIMEOUT_HEAVY);

    const ctx = useBatchCircuit();

    /** The depositor half of the leaf at slot `k`; distinct per slot. */
    function innerAt(k: number): Field {
        return buildInner(ctx.P, { pk: 0xc000n + BigInt(k), rho: 1n + 2n * BigInt(k), rcm: 3n + 2n * BigInt(k) });
    }

    /** Honest deposits in every slot except `k`, which holds `leaf`. */
    function fullBatchWith(k: number, leaf: LeafWitness): BatchWitness {
        const leaves = ctx.batch.seededMany(MAX_L, () => 1);
        leaves[k] = leaf;
        return ctx.batch.honest(0, leaves);
    }

    interface SlotCase {
        /** The constraint expected to reject, as it reads in the circom. */
        rule: string;
        /** The defective batch with its defect in slot `k`. */
        build: (k: number) => BatchWitness;
    }

    const CASES: SlotCase[] = [
        {
            // Step 1. A spend leaf is its word, so a leaf_asset on it reaches
            // nothing but the public inputs.
            rule: "(1 - is_deposit[k]) * leaf_asset[k] === 0",
            build: k => {
                const cm = commitWithInner(ctx.P, 7n, 5n, innerAt(k));
                return fullBatchWith(k, { word: cm, leaf: cm, leafAsset: 42n, leafPublicIn: 0n, isDeposit: 0 });
            },
        },
        {
            // Step 1. With both deposit fields zero, the leaf the circuit builds
            // at is_deposit = 2 is cms + 2·(cm − cms) = 2·cm − inner; inserting
            // exactly that leaves booleanity as the only failing constraint.
            rule: "is_deposit[k] * (1 - is_deposit[k]) === 0",
            build: k => {
                const inner = innerAt(k);
                const cm = commitWithInner(ctx.P, 0n, 0n, inner);
                const w = fullBatchWith(k, {
                    word: inner, leaf: mod(2n * cm - inner), leafAsset: 0n, leafPublicIn: 0n, isDeposit: 1,
                });
                w.isDeposit[k] = 2;
                rebindFiatShamir(w);
                return w;
            },
        },
        {
            // Step 5.
            rule: "IsZero(leaf_asset[k]) * leaf_public_in[k] === 0",
            build: k => fullBatchWith(k, ctx.batch.leafWith({
                asset: 0n, val: 100n, pk: 0xc000n + BigInt(k), rho: 1n, rcm: 3n, isDeposit: 1,
            })),
        },
        {
            // Step 2. (7, 2^64) packs to the same word as the in-range (8, 0).
            rule: "RangeCheck64(leaf_public_in[k])",
            build: k => {
                const inner = innerAt(k);
                const leaf = ctx.P.hash([TAG_CM, 7n * TWO_64 + TWO_64, inner]);
                return fullBatchWith(k, { word: inner, leaf, leafAsset: 7n, leafPublicIn: TWO_64, isDeposit: 1 });
            },
        },
        {
            // Step 2.
            rule: "RangeCheck64(leaf_asset[k])",
            build: k => {
                const inner = innerAt(k);
                const leaf = ctx.P.hash([TAG_CM, TWO_64 * TWO_64, inner]);
                return fullBatchWith(k, { word: inner, leaf, leafAsset: TWO_64, leafPublicIn: 0n, isDeposit: 1 });
            },
        },
    ];

    it("the base batch, a deposit in every slot, is accepted", async () => {
        const { batch, circuit } = ctx;
        await expectBatchAccepts(circuit, batch.honest(0, batch.seededMany(MAX_L, () => 1)));
    });

    for (const { rule, build } of CASES) {
        for (let k = 0; k < MAX_L; k++) {
            it(`FAILS at slot ${k}: ${rule}`, async () => {
                await expectBatchRejects(ctx.circuit, build(k), `${rule} did not reject slot ${k}`);
            });
        }
    }
});
