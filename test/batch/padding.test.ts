// Zeroing constraints and count bounds.
//
// Step 4 of tree_update_batch.circom asserts (1 - active[k]) * X === 0 for
// every per-leaf field of an inactive slot; step 1 also zeroes the two
// deposit-only fields on an active spend leaf. `actual_count - 1` is decomposed
// in COUNT_BITS bits, bounding the count to [1, MAX_L].

import { rebindFiatShamir, type BatchWitness } from "../lib/batch";
import { MAX_L, TIMEOUT_HEAVY } from "../lib/constants";
import { expectBatchRejects, useBatchCircuit } from "./setup";

describe("tree_update_batch / padding, counts and spend-leaf zeroing", function () {
    this.timeout(TIMEOUT_HEAVY);

    const ctx = useBatchCircuit();

    // ===== padding coverage =====
    //
    // With actual_count = 1, slots 1..MAX_L-1 are inactive. Every row runs on
    // each of them: the zeroing is a loop over slots, and a slot it skips is
    // satisfied by every witness that poisons another.

    interface PaddingCase {
        /** Names the per-leaf field, as it reads in the circom. */
        field: string;
        /** Write the non-zero value into inactive slot `k`. */
        poison: (w: BatchWitness, k: number) => void;
    }

    const PADDING_CASES: PaddingCase[] = [
        { field: "cms",            poison: (w, k) => { w.cms[k] = 0xbadcafen; } },
        // The next two leave is_deposit at 0, so the spend-slot zeroing of step 1
        // rejects them as well; the `as a deposit` rows set is_deposit, leaving
        // the padding constraint as the only one that can reject.
        { field: "leaf_asset",     poison: (w, k) => { w.leafAsset[k] = 42n; } },
        { field: "leaf_public_in", poison: (w, k) => { w.leafPublicIn[k] = 99n; } },
        { field: "is_deposit",     poison: (w, k) => { w.isDeposit[k] = 1; } },
        {
            field: "leaf_asset, as a deposit",
            poison: (w, k) => { w.isDeposit[k] = 1; w.leafAsset[k] = 42n; },
        },
        {
            field: "leaf_asset and leaf_public_in, as a deposit",
            poison: (w, k) => { w.isDeposit[k] = 1; w.leafAsset[k] = 42n; w.leafPublicIn[k] = 99n; },
        },
    ];

    for (const { field, poison } of PADDING_CASES) {
        for (let k = 1; k < MAX_L; k++) {
            it(`padding: non-zero ${field} in inactive slot ${k} is rejected`, async () => {
                const { batch, circuit } = ctx;
                const w = batch.single({ val: 9n, isDeposit: 1 });
                poison(w, k);
                // Every row is a PolyEval coefficient, so Fiat-Shamir is re-derived:
                // a stale `z` would reject before the padding constraint is reached.
                rebindFiatShamir(w);
                await expectBatchRejects(
                    circuit,
                    w,
                    `(1 - active[${k}]) * ${field} === 0 did not reject a non-zero inactive slot`,
                );
            });
        }
    }

    // ===== count bounds and booleanity =====

    it("FAILS when actual_count == 0 (Num2Bits(COUNT_BITS) rejects -1)", async () => {
        // actual_count - 1 = -1 is a 254-bit field element.
        const { batch, circuit } = ctx;
        const w = batch.single({ val: 1n, isDeposit: 1 });
        w.actualCount = 0;
        // Zero out the would-be-active slot fields so only the count check fires.
        w.cms[0] = 0n;
        w.leafAsset[0] = 0n; w.leafPublicIn[0] = 0n;
        w.isDeposit[0] = 0;
        rebindFiatShamir(w);
        await expectBatchRejects(circuit, w, "Num2Bits(COUNT_BITS) must reject actual_count - 1 = -1");
    });

    it("FAILS when actual_count > MAX_L (Num2Bits(COUNT_BITS) rejects it)", async () => {
        // At MAX_L + 1 the decomposition needs COUNT_BITS + 1 bits.
        const { batch, circuit } = ctx;
        const w = batch.single({ val: 1n, isDeposit: 1 });
        w.actualCount = MAX_L + 1;
        rebindFiatShamir(w);
        await expectBatchRejects(circuit, w, "Num2Bits(COUNT_BITS) must reject a count above MAX_L");
    });

    it("FAILS when is_deposit is non-boolean (=2)", async () => {
        const { batch, circuit } = ctx;
        const w = batch.single({ val: 1n, isDeposit: 1 });
        w.isDeposit[0] = 2;
        rebindFiatShamir(w);
        await expectBatchRejects(circuit, w, "is_deposit must be constrained boolean");
    });

    // ===== spend-leaf field zeroing (step 1) =====
    //
    // Neither deposit-only field reaches a spend leaf, so nothing else stops a
    // relayer pushing a nonzero leaf_asset or leaf_public_in into the public
    // inputs of a spend batch. These run on an active slot, where the padding
    // constraint is satisfied and cannot be what rejects.

    it("FAILS on a nonzero leaf_asset in an active spend leaf", async () => {
        const { batch, circuit } = ctx;
        const w = batch.single({ val: 100n, isDeposit: 0 });
        w.leafAsset[0] = 42n;
        rebindFiatShamir(w);
        await expectBatchRejects(circuit, w, "(1 - is_deposit[0]) * leaf_asset[0] === 0 did not reject a spend leaf");
    });

    it("FAILS on a nonzero leaf_public_in in an active spend leaf", async () => {
        const { batch, circuit } = ctx;
        const w = batch.single({ val: 100n, isDeposit: 0 });
        w.leafPublicIn[0] = 99n;
        rebindFiatShamir(w);
        await expectBatchRejects(
            circuit,
            w,
            "(1 - is_deposit[0]) * leaf_public_in[0] === 0 did not reject a spend leaf",
        );
    });
});
