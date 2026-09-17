// Honest batches the circuit must accept, across leaf count, deposit/spend mix
// and start position, and the capacity bound at the end of the tree.
//
// Leaf format: leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y).

import { ARITY, BATCH_DEPTH, MAX_L, TIMEOUT_HEAVY } from "../lib/constants";
import type { LeafWitness } from "../lib/batch";
import { CAPACITY, expectBatchAccepts, expectBatchRejects, useBatchCircuit } from "./setup";

describe("tree_update_batch / honest shapes and capacity", function () {
    this.timeout(TIMEOUT_HEAVY);

    const ctx = useBatchCircuit();

    it("honest deposit: 1 active leaf, isDeposit=1, binding verifies", async () => {
        const { batch, circuit } = ctx;
        const leaf = batch.leafWith({
            asset: 7n,
            val: 1000n,
            pk: 0xabcn,
            rho: 1n,
            rcm: 3n,
            rcvDep: 5n,
            isDeposit: 1,
        });
        await expectBatchAccepts(circuit, batch.honest(0, [leaf]));
    });

    it("honest spend: 2 active leaves, isDeposit=0, binding skipped", async () => {
        const { batch, circuit } = ctx;
        const leaves = [
            batch.leafWith({ asset: 7n, val: 100n, pk: 0xdadn, rho: 11n, rcm: 33n, rcvDep: 55n, isDeposit: 0 }),
            batch.leafWith({ asset: 7n, val: 50n, pk: 0xdadn, rho: 22n, rcm: 44n, rcvDep: 66n, isDeposit: 0 }),
        ];
        await expectBatchAccepts(circuit, batch.honest(0, leaves));
    });

    // ===== multi-leaf / odd-count / capacity coverage =====
    //
    // actual_count is a leaf count, so odd batches are valid. These exercise the
    // padded leaf slots and the insert windows up to MAX_L.

    it("honest 2-leaf deposit batch passes", async () => {
        const { batch, circuit } = ctx;
        const leaves = [
            batch.leaf({ val: 33n, isDeposit: 1, asset: 7n, pk: 0xaa1n }),
            batch.leaf({ val: 77n, isDeposit: 1, asset: 7n, pk: 0xaa2n }),
        ];
        await expectBatchAccepts(circuit, batch.honest(0, leaves));
    });

    it("honest odd batch: 3 leaves, fewer than a spend's 6 outputs, passes", async () => {
        // A 3-output transact bundle emits three commitments, so the batch must
        // accept an odd leaf count.
        const { batch, circuit } = ctx;
        const leaves = [
            batch.leaf({ val: 11n, isDeposit: 0, pk: 0xb01n }),
            batch.leaf({ val: 22n, isDeposit: 0, pk: 0xb02n }),
            batch.leaf({ val: 33n, isDeposit: 0, pk: 0xb03n }),
        ];
        await expectBatchAccepts(circuit, batch.honest(0, leaves));
    });

    it("honest odd batch: MAX_L - 1 leaves passes", async () => {
        const { batch, circuit } = ctx;
        const leaves: LeafWitness[] = Array.from({ length: MAX_L - 1 }, (_, i) =>
            batch.leaf({ val: BigInt(300 + i), isDeposit: 1, pk: BigInt(0xbe00 + i) }));
        await expectBatchAccepts(circuit, batch.honest(0, leaves));
    });

    it("honest full-batch (actual_count = MAX_L) passes", async () => {
        const { batch, circuit } = ctx;
        const leaves: LeafWitness[] = Array.from({ length: MAX_L }, (_, i) =>
            batch.leaf({ val: BigInt(300 + 2 * i), isDeposit: 1, pk: BigInt(0xbf00 + i) }));
        await expectBatchAccepts(circuit, batch.honest(0, leaves));
    });

    it("mixed deposit + spend leaves in same batch passes", async () => {
        const { batch, circuit } = ctx;
        const leaves = [
            batch.leaf({ val: 50n, isDeposit: 1, pk: 0xc01n }),
            batch.leaf({ val: 7n, isDeposit: 0, pk: 0xc02n }),
            batch.leaf({ val: 100n, isDeposit: 1, pk: 0xc03n }),
        ];
        await expectBatchAccepts(circuit, batch.honest(0, leaves));
    });

    it("honest odd batch at non-zero start_index passes", async () => {
        // Exercises both roots at start_index = 13 (digits [1, 3, 0, ...]);
        // inserts land at indices 13..15, crossing a level-1 carry.
        const { batch, circuit } = ctx;
        const leaves = [
            batch.leaf({ val: 3n, isDeposit: 1, pk: 0xd01n }),
            batch.leaf({ val: 7n, isDeposit: 1, pk: 0xd02n }),
            batch.leaf({ val: 9n, isDeposit: 1, pk: 0xd03n }),
        ];
        await expectBatchAccepts(circuit, batch.honest(13, leaves));
    });

    // ===== batched insert at production depth =====
    //
    // BatchAppend sizes each level's window for the worst case, a run that
    // straddles a boundary at that level. `gadgets/batch_append.test.ts` sweeps
    // every start at depth 4 with distinct leaves; these place the straddle at
    // every level of the deployed shape, through the full circuit.

    let straddleLeaves: LeafWitness[];
    before(() => {
        straddleLeaves = ctx.batch.seededMany(MAX_L, () => 1);
    });

    for (let level = 1; level < BATCH_DEPTH; level++) {
        it(`honest full batch straddling a level-${level} boundary passes`, async () => {
            const start = ARITY ** level - 3;
            await expectBatchAccepts(ctx.circuit, ctx.batch.honest(start, straddleLeaves));
        });
    }

    it("honest full batch ending on the last index of the tree passes", async () => {
        const { batch, circuit } = ctx;
        await expectBatchAccepts(circuit, batch.honest(CAPACITY - MAX_L, batch.seededMany(MAX_L, () => 0)));
    });

    // ===== tree capacity =====
    //
    // The last inserted index, start_index + actual_count - 1, is range-checked
    // to 2·DEPTH bits. Bounding start_index + k for every slot would make the top
    // MAX_L - 1 leaves unreachable and an honest one-leaf batch at the last free
    // index unsatisfiable.

    it("accepts a single leaf at the last index in the tree", async () => {
        const { batch, circuit } = ctx;
        await expectBatchAccepts(circuit, batch.single({ val: 1n, isDeposit: 1 }, CAPACITY - 1));
    });

    it("FAILS when a batch runs past the end of the tree", async () => {
        // One free slot, two leaves: the last index is CAPACITY = 2^(2·DEPTH),
        // one past what Num2Bits(2·DEPTH) holds. The reference tree does not
        // bound-check, so the witness builds and the circuit must reject it.
        const { batch, circuit } = ctx;
        const leaves = [
            batch.leaf({ val: 1n, isDeposit: 1, pk: 0xe01n }),
            batch.leaf({ val: 2n, isDeposit: 1, pk: 0xe02n }),
        ];
        await expectBatchRejects(
            circuit,
            batch.honest(CAPACITY - 1, leaves),
            "Num2Bits(2·DEPTH) must reject an active insertion index at capacity",
        );
    });
});
