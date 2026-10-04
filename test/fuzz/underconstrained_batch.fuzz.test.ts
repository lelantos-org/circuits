// The R1CS-level second-witness search, over `tree_update_batch.circom`.
// `underconstrained.fuzz.test.ts` runs the same search over `4x6.circom`.
//
// Out of scope: the forgery in `batch/divergent.test.ts`. The searches walk
// straight lines from an honest witness, and that forgery is a differently
// shaped witness (`is_deposit` cleared, so the word is the leaf), not a null
// direction from a deposit witness. `just picus` decides the general case, at
// weak safety.

import * as fc from "fast-check";
import { expect } from "chai";

import { type CircuitInput } from "../lib/circuit";
import { logBitGroupCensus, useSearchSuite } from "../lib/underconstrained_suite";
import { formatReport, sweepSingleSignal } from "../lib/underconstrained";
import { BatchBuilder, type BatchWitness } from "../lib/batch";
import { treeUpdateBatchInputJson } from "../lib/inputs";
import { BATCH_DEPTH, MAX_L, TIMEOUT_HEAVY } from "../lib/constants";
import { fcParamsFor } from "./arbitraries";
import { useGadgets } from "../lib/harness";
import { CIRCUIT } from "../batch/setup";

const fcParams = fcParamsFor("UNDERCONSTRAINED_BATCH");

describe("underconstrained_tree_update_batch [fuzz]", function () {
    this.timeout(TIMEOUT_HEAVY);

    // ===== structural: bit decompositions =====
    //
    // Witness-independent, so a single run covers every instance in the circuit.
    const suite = useSearchSuite<BatchWitness>(
        CIRCUIT,
        w => treeUpdateBatchInputJson(w) as unknown as CircuitInput,
        1000,
    );
    const assertNoSecond = suite.assertNoSecond;

    const gadgets = useGadgets();
    let batch: BatchBuilder;
    before(() => {
        batch = new BatchBuilder(gadgets.P);
    });

    it("the detector sees the decompositions the circuit is known to contain", () => {
        const hist = logBitGroupCensus(suite.ctx);

        expect(hist.get(252), "expected no Num2Bits(252): the batch circuit carries " +
            "no curve arithmetic").to.equal(undefined);
        expect(hist.get(64), "expected two Num2Bits(64) per leaf slot: the leaf_asset and " +
            "leaf_public_in range checks, 2 * MAX_L of them").to.equal(2 * MAX_L);
        expect(hist.get(3), "expected one Num2Bits(COUNT_BITS) for actual_count - 1")
            .to.equal(1);
        expect(Math.max(...hist.keys()), "the widest decomposition should be a range check's")
            .to.equal(64);
    });


    // BatchAppend pins every frontier slot neither root reads to zero, so no
    // frontier signal may be free at any digit pattern. start_index = 0 has
    // every digit 0, so all 33 slots are unread.
    it("no frontier slot is free, at any digit pattern", async () => {
        for (const start of [0, 21, 4 ** 5 - 3, 4 ** 11 - 1]) {
            const witness = await suite.witnessFor(batch.single({ val: 42n, isDeposit: 1 }, start));
            const free = sweepSingleSignal(suite.ctx.view, witness, suite.ctx.symbols)
                .filter(f => /frontier_in\[\d+\]\[\d+\]$/.test(f.support[0].name))
                .map(f => f.support[0].name);
            expect(free, `start_index = ${start}: free frontier slots`).to.deep.equal([]);
        }
    });

    // ===== witness-level: both sweeps, over a spread of honest batches =====
    //
    // Which signals are free depends on how many slots are active, whether each
    // leaf is a deposit or a spend, and where the frontier sits. The scenarios
    // span those three axes.

    it("a single deposit leaf has no second witness", async () => {
        const findings = await assertNoSecond(
            "oneDeposit",
            batch.single({ val: 1000n, isDeposit: 1 }),
        );
        console.log(`    oneDeposit: ${findings.length} explained free signal(s)\n` +
            formatReport(findings));
    });

    it("a single spend leaf has no second witness", async () => {
        // The word is the leaf. The deposit hash is still computed and then not
        // selected: `dep_cm` is pinned by its own hash whether or not anything
        // reads it.
        await assertNoSecond(
            "oneSpend",
            batch.single({ val: 1000n, isDeposit: 0 }),
        );
    });

    it("a partial batch has no second witness", async () => {
        // Padding slots run the whole (1 - active[k]) * X === 0 block, where a
        // vanishing product can leave a constraint not restricting its signal.
        await assertNoSecond("partialBatch", batch.honest(0, batch.seededMany(3, () => 1)));
    });

    it("a full flush of principal/fee pairs with zero fees has no second witness", async () => {
        // Every fee note has zero value at asset 0, so every odd slot has both
        // `IsZero(leaf_asset)` and its product with `leaf_public_in` at zero.
        // Also the all-slots-active case.
        await assertNoSecond("fbps0Flush", batch.honest(0, batch.depositPairs(MAX_L)));
    });

    it("a batch at a non-trivial frontier has no second witness", async () => {
        // start_index = 21 = 0b010101 gives non-zero digits at the three lowest
        // levels, so both roots read filled frontier slots.
        await assertNoSecond(
            "frontier21",
            batch.single({ val: 42n, isDeposit: 1 }, 21),
        );
    });

    it("a full batch straddling a deep boundary has no second witness", async () => {
        // 4^5 - 3: the run crosses a level-5 boundary, so every level up to 5
        // uses both slots of its window and the level-1 window all three, with
        // filled frontier slots below.
        const leaves = batch.seededMany(MAX_L, i => (i % 2 === 0 ? 0 : 1));
        await assertNoSecond("straddle4^5", batch.honest(4 ** 5 - 3, leaves));
    });

    it("a batch on the last index of the tree has no second witness", async () => {
        // Every digit is 3: all 33 frontier slots are filled and read, and the
        // capacity check is tight.
        await assertNoSecond(
            "lastIndex",
            batch.single({ val: 42n, isDeposit: 1 }, 4 ** BATCH_DEPTH - 1),
        );
    });

    it("a single zero-value fee note has no second witness", async () => {
        // A zero-value leaf at asset 0 beside a valued one.
        await assertNoSecond(
            "zeroValueFee",
            batch.honest(0, batch.depositPairs(2)),
        );
    });

    it("a zero-value deposit leaf at a non-zero asset has no second witness", async () => {
        // The asset is an input of the leaf hash at any value, so nothing about
        // it is free here.
        await assertNoSecond(
            "zeroValueNamedAsset",
            batch.honest(0, [batch.seeded(0, 1), batch.seeded(1, 1, 0n, 7n)]),
        );
    });

    it("random batches have no second witness", async () => {
        await fc.assert(
            fc.asyncProperty(
                fc.integer({ min: 1, max: MAX_L }),
                // Mostly shallow, where the frontier changes shape fastest, and
                // sometimes anywhere in the production-depth tree.
                fc.oneof(
                    { weight: 3, arbitrary: fc.integer({ min: 0, max: 64 }) },
                    { weight: 1, arbitrary: fc.integer({ min: 0, max: 4 ** BATCH_DEPTH - MAX_L }) },
                ),
                fc.array(fc.constantFrom<0 | 1>(0, 1), { minLength: MAX_L, maxLength: MAX_L }),
                fc.array(fc.constantFrom<0 | 1>(0, 1), { minLength: MAX_L, maxLength: MAX_L }),
                async (count, prefill, flags, worthless) => {
                    // Every constraint is per-slot, so any interleaving is
                    // satisfiable. A deposit leaf is drawn with zero value at
                    // asset 0 on half the draws.
                    const leaves = Array.from({ length: count }, (_, i) =>
                        flags[i] === 1 && worthless[i] === 1
                            ? batch.seeded(i, 1, 0n, 0n)
                            : batch.seeded(i, flags[i]));
                    await assertNoSecond(
                        `random(count=${count}, prefill=${prefill})`,
                        batch.honest(prefill, leaves),
                    );
                },
            ),
            fcParams,
        );
    });
});
