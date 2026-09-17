// Frontier binding and both roots.
//
// BatchAppend rebuilds `old_root` from `frontier_in`, so a relayer cannot pair a
// real `oldRoot` with a forged frontier, which would permanently corrupt the
// on-chain root; `new_root === append.new_root` binds the advanced tree.
// `gadgets/batch_append.test.ts` covers the gadget alone at small depth.

import { expect } from "chai";

import { quatDigit } from "../helpers";
import { rebindFiatShamir } from "../lib/batch";
import { BATCH_DEPTH, TIMEOUT_HEAVY } from "../lib/constants";
import { expectBatchAccepts, expectBatchRejects, useBatchCircuit } from "./setup";

describe("tree_update_batch / frontier and roots", function () {
    this.timeout(TIMEOUT_HEAVY);

    const ctx = useBatchCircuit();

    it("frontier binding: honest non-zero start_index passes", async () => {
        // start_index = 5 ⇒ digits [1,1,0,...]; exercises the pre/eq branches
        // at low levels.
        const { batch, circuit } = ctx;
        await expectBatchAccepts(circuit, batch.single({ val: 42n, isDeposit: 1 }, 5));
    });

    it("frontier binding: large prefill (start_index=21) honest passes", async () => {
        // 21 = 0b010101 ⇒ digits [1,1,1,0,...]; non-trivial frontier at the
        // three lowest levels.
        const { batch, circuit } = ctx;
        await expectBatchAccepts(circuit, batch.single({ val: 9n, isDeposit: 1 }, 21));
    });

    it("frontier binding: corrupted frontier entry rejected", async () => {
        // Honest oldRoot + cms but tampered frontier ⇒ the old-root rebuild
        // diverges from old_root ⇒ `old_root === append.old_root` fails.
        const { batch, circuit } = ctx;
        const w = batch.single({ val: 1000n, isDeposit: 1 }, 8);
        // Slot 1 at level 1 is read: 8 has digit 2 there.
        expect(quatDigit(8, 1)).to.be.greaterThan(1);
        w.frontier[1][1] = w.frontier[1][1] + 1n;
        await expectBatchRejects(
            circuit,
            w,
            "the old-root rebuild must diverge from old_root under a tampered frontier",
        );
    });

    it("frontier binding: empty-tree frontier with wrong oldRoot rejected", async () => {
        // Honest all-zero frontier with a forged oldRoot. BatchAppend rebuilds
        // the empty-tree root and the equality check rejects the mismatch.
        const { batch, circuit } = ctx;
        const w = batch.single({ val: 1n, isDeposit: 1 });
        w.oldRoot = w.oldRoot + 1n;
        rebindFiatShamir(w);
        await expectBatchRejects(circuit, w, "old_root === append.old_root must reject a forged old_root");
    });

    it("FAILS when new_root does not match the batched insert", async () => {
        // Counterpart of the old_root frontier test: old_root binds the input
        // frontier and `new_root === append.new_root` binds the resulting root,
        // so a relayer cannot name an arbitrary root for the advanced tree.
        const { batch, circuit } = ctx;
        const w = batch.single({ val: 100n, isDeposit: 1 }, 4);
        w.newRoot = w.newRoot + 1n;
        rebindFiatShamir(w);
        await expectBatchRejects(circuit, w, "new_root === append.new_root must reject a forged new_root");
    });

    it("FAILS on a non-zero frontier slot nothing reads", async () => {
        // The slot at the digit is the lowest unread slot. Checked at level 0,
        // where the digit is non-zero, and at the first level where it is 0;
        // both slots are pinned to zero.
        const { batch, circuit } = ctx;
        const start = 21;
        const honest = batch.single({ val: 9n, isDeposit: 1 }, start);
        const emptyLevel = [...Array(BATCH_DEPTH).keys()].find(d => quatDigit(start, d) === 0)!;
        for (const d of [0, emptyLevel]) {
            const k = quatDigit(start, d);
            const w = { ...honest, frontier: honest.frontier.map(lvl => lvl.slice()) };
            w.frontier[d][k] = 1n;
            await expectBatchRejects(
                circuit,
                w,
                `(1 - read) * frontier_in[${d}][${k}] === 0 must reject a non-zero unread slot`,
            );
        }
    });
});
