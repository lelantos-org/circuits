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
    // Each row writes one inactive-slot field and expects rejection. With
    // actual_count = 1, slot 1 is inactive.

    interface PaddingCase {
        /** Names the per-leaf field, as it reads in the circom. */
        field: string;
        /** Write the non-zero value into the inactive slot. */
        poison: (w: BatchWitness) => void;
    }

    const PADDING_CASES: PaddingCase[] = [
        { field: "cms",            poison: w => { w.cms[1] = 0xbadcafen; } },
        // The next two write the field on a slot whose is_deposit is 0, so the
        // spend-slot zeroing of step 1 rejects them as well; `as a deposit`
        // below sets is_deposit with them, which that step permits, and leaves
        // the padding constraint as the only one that can reject.
        { field: "leaf_asset",     poison: w => { w.leafAsset[1] = 42n; } },
        { field: "leaf_public_in", poison: w => { w.leafPublicIn[1] = 99n; } },
        { field: "is_deposit",     poison: w => { w.isDeposit[1] = 1; } },
        {
            field: "leaf_asset, as a deposit",
            poison: w => { w.isDeposit[1] = 1; w.leafAsset[1] = 42n; },
        },
        {
            field: "leaf_asset and leaf_public_in, as a deposit",
            poison: w => { w.isDeposit[1] = 1; w.leafAsset[1] = 42n; w.leafPublicIn[1] = 99n; },
        },
    ];

    for (const { field, poison } of PADDING_CASES) {
        it(`padding: non-zero ${field} in inactive slot is rejected`, async () => {
            const { batch, circuit } = ctx;
            const w = batch.single({ val: 9n, isDeposit: 1 });
            poison(w);
            // Every row is a PolyEval coefficient, so Fiat-Shamir is re-derived:
            // otherwise a stale `z` rejects the witness before the padding
            // constraint is reached.
            rebindFiatShamir(w);
            await expectBatchRejects(
                circuit,
                w,
                `(1 - active[1]) * ${field} === 0 did not reject a non-zero inactive slot`,
            );
        });
    }

    // ===== count bounds and booleanity =====

    it("FAILS when actual_count == 0 (Num2Bits(COUNT_BITS) rejects -1)", async () => {
        // The circuit decomposes (actual_count - 1) in COUNT_BITS bits;
        // actual_count = 0 yields -1, a 254-bit field element that does not fit.
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
        // COUNT_BITS bounds (actual_count - 1) ∈ [0, MAX_L - 1], so
        // actual_count ≤ MAX_L. At MAX_L + 1 the decomposition needs
        // COUNT_BITS + 1 bits. Derived from MAX_L so it tracks the width.
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
    // Step 1 zeroes the two deposit-only fields on an active spend leaf, so a
    // relayer cannot push a nonzero leaf_asset or leaf_public_in into the public
    // inputs of a batch that carries no deposit. Neither field reaches a spend
    // leaf, so nothing else would pin them. These run on an active slot, where
    // the padding constraint is satisfied and cannot be what rejects.

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
