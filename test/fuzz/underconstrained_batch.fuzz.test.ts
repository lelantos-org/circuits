// The R1CS-level second-witness search, over `tree_update_batch.circom`.
//
// `underconstrained.fuzz.test.ts` is the same search over `4x6.circom`, and
// carried `const CIRCUIT = srcPath("4x6.circom")` as a hard scope for as long as
// it has existed. The batch circuit therefore had NO constraint-system coverage
// at all: `tree_update_batch.test.ts` only ever asks the wasm whether it accepts
// an input object, and a signal the template computes but never constrains is
// invisible from there. This file closes that gap.
//
// It is a sibling rather than a parameterisation of that file because the
// per-circuit half does not transfer: the scenario builders are `TxBuilder`
// shapes there and batch witnesses here, and each suite's detector self-check
// pins its own gadget census. The search half is shared —
// `lib/underconstrained_suite.ts` owns loading both builds and judging a finding
// list, so a change to the verdict lands once.
//
// WHAT THIS SUITE DOES NOT COVER. The forgery in
// `tree_update_batch.test.ts :: divergent witness` is out of its reach, by
// construction and not by accident:
//
//   * The searches walk STRAIGHT LINES from an honest witness. That forgery is
//     not a step away from a deposit witness — it is a differently-shaped
//     witness (`is_deposit` cleared, the whole `active_dep` chain gated off)
//     reached by a jump, not a null direction.
//   * `severity: "break"` is defined as "some moving entry is an output or a
//     public input". The forgery holds `y` and `z` FIXED — that is the entire
//     point of it — so even if found it would grade as `malleable`.
//
// So the two suites are complements, not substitutes: this one decides local
// freedom around honest witnesses, and the divergent-witness block decides
// whether the witness may disagree with the calldata it is proved against.
// `just picus` decides the general case, at weak safety.

import * as fc from "fast-check";
import { expect } from "chai";

import { srcPath, type CircuitInput } from "../lib/circuit";
import {
    assertNoSecondWitness,
    loadSearchContext,
    registerStructuralTests,
    type SearchContext,
} from "../lib/underconstrained_suite";
import { formatReport, sweepSingleSignal } from "../lib/underconstrained";
import { widthHistogram } from "../lib/bit_groups";
import { buildHonest, depositPairs, seededLeaf, simpleLeaf, type BatchWitness } from "../lib/batch";
import { treeUpdateBatchInputJson } from "../lib/inputs";
import { Jubjub, Poseidon } from "../helpers";
import { BATCH_DEPTH, MAX_L, TIMEOUT_HEAVY } from "../lib/constants";
import { fcParamsFor } from "./arbitraries";
import { buildJubjub } from "../lib/harness";

const CIRCUIT = srcPath("tree_update_batch.circom");
const fcParams = fcParamsFor("UNDERCONSTRAINED_BATCH");

describe("underconstrained_tree_update_batch [fuzz]", function () {
    this.timeout(TIMEOUT_HEAVY);

    let ctx: SearchContext;
    let P: Poseidon;
    let J: Jubjub;

    before(async () => {
        // The circuit builds and the two gadget tables are mutually
        // independent, so start them together.
        const [context, poseidon, jubjub] = await Promise.all([
            loadSearchContext(CIRCUIT),
            Poseidon.build(),
            buildJubjub(),
        ]);
        ctx = context;
        P = poseidon;
        J = jubjub;
    });

    async function witnessFor(w: BatchWitness): Promise<bigint[]> {
        return ctx.tester.calculateWitness(
            treeUpdateBatchInputJson(w) as unknown as CircuitInput,
            true,
        );
    }

    /** Both searches over one honest batch, in this suite's witness shape. */
    async function assertNoSecond(label: string, w: BatchWitness) {
        return assertNoSecondWitness(ctx, label, await witnessFor(w));
    }

    // ===== structural: bit decompositions =====
    //
    // Witness-independent, so once covers every instance in the circuit rather
    // than the ones some witness happened to exercise.

    registerStructuralTests(() => ctx, 1000);

    it("the detector sees the decompositions the circuit is known to contain", () => {
        const hist = widthHistogram(ctx.bitGroups);
        const lines = [...hist].map(([w, n]) => `    ${String(n).padStart(5)}x  width ${w}`);
        console.log(`    bit-decomposition groups: ${ctx.bitGroups.length}\n${lines.join("\n")}`);

        expect(hist.get(252), "expected one Num2Bits(252) per leaf slot: MulH's blinder " +
            "decomposition, MAX_L of them").to.equal(MAX_L);
        expect(hist.get(64), "expected two Num2Bits(64) per leaf slot: the leaf_asset and " +
            "leaf_public_in range checks, 2 * MAX_L of them").to.equal(2 * MAX_L);
        expect(hist.get(3), "expected one Num2Bits(COUNT_BITS) for actual_count - 1")
            .to.equal(1);
        expect(Math.max(...hist.keys()), "the widest decomposition should be MulH's")
            .to.equal(252);
    });


    // BatchAppend pins every frontier slot neither root reads to zero, so no
    // frontier signal may be free at any digit pattern. The sweep
    // below would already fail on one, since nothing explains it; this names the
    // property directly, at the patterns where the unpinned circuit was loosest.
    // start_index = 0 has every digit 0, where all 33 slots used to be free.
    it("no frontier slot is free, at any digit pattern", async () => {
        for (const start of [0, 21, 4 ** 5 - 3, 4 ** 11 - 1]) {
            const w = buildHonest(P, start, [simpleLeaf({ J, P, val: 42n, isDeposit: 1 })]);
            const witness = await witnessFor(w);
            const free = sweepSingleSignal(ctx.view, witness, ctx.symbols)
                .filter(f => /frontier_in\[\d+\]\[\d+\]$/.test(f.support[0].name))
                .map(f => f.support[0].name);
            expect(free, `start_index = ${start}: free frontier slots`).to.deep.equal([]);
        }
    });

    // ===== witness-level: both sweeps, over a spread of honest batches =====
    //
    // Which signals are free is a property OF the witness. A batch's shape moves
    // along three axes the circuit branches on — how many slots are active,
    // whether each leaf is a deposit or a spend, and where in the tree the
    // frontier sits — so the scenarios spread over those rather than re-testing
    // one happy path.

    it("a single deposit leaf has no second witness", async () => {
        const findings = await assertNoSecond(
            "oneDeposit",
            buildHonest(P, 0, [simpleLeaf({ J, P, val: 1000n, isDeposit: 1 })]),
        );
        console.log(`    oneDeposit: ${findings.length} explained free signal(s)\n` +
            formatReport(findings));
    });

    it("a single spend leaf has no second witness", async () => {
        // The deposit binding is gated OFF here, so `cv_dep` is left carrying
        // only BabyCheck and `leaf_asset`/`leaf_public_in` only their zeroings —
        // the fewest constraints any active slot ever runs under.
        await assertNoSecond(
            "oneSpend",
            buildHonest(P, 0, [simpleLeaf({ J, P, val: 1000n, isDeposit: 0 })]),
        );
    });

    it("a partial batch has no second witness", async () => {
        // Padding slots run the whole (1 - active[k]) * X === 0 block, and a
        // vanishing product is exactly how a constraint stops restricting the
        // signal it was meant to pin.
        const leaves = Array.from({ length: 3 }, (_, i) => seededLeaf(P, J, i, 1));
        await assertNoSecond("partialBatch", buildHonest(P, 0, leaves));
    });

    it("a full flush of principal/fee pairs at fbps = 0 has no second witness", async () => {
        // The configuration that used to supply four free 64-bit dials on
        // `leaf_asset`: every fee note worthless, so every odd slot's deposit
        // binding is degenerate. Step 6a is what leaves nothing free here, and
        // this is the witness that would show it if it did not.
        //
        // Also the all-slots-active case. What the searches report depends on
        // the witness only through which slots are active — an inactive slot
        // contributes one free IsZero hint each — so a separate honest full
        // batch would sweep 113k entries to reach the same finding set.
        await assertNoSecond("fbps0Flush", buildHonest(P, 0, depositPairs(P, J, MAX_L)));
    });

    it("a batch at a non-trivial frontier has no second witness", async () => {
        // start_index = 21 = 0b010101 gives non-zero digits at the three lowest
        // levels, so both roots read filled frontier slots rather than an
        // all-empty frontier.
        await assertNoSecond(
            "frontier21",
            buildHonest(P, 21, [simpleLeaf({ J, P, val: 42n, isDeposit: 1 })]),
        );
    });

    it("a full batch straddling a deep boundary has no second witness", async () => {
        // 4^5 - 3: the run crosses a level-5 boundary, so every level up to 5
        // uses both slots of its window and the level-1 window all three, with
        // filled frontier slots below. The other scenarios start at 0 or 21,
        // where the upper windows hold one real node and one empty subtree.
        const leaves = Array.from({ length: MAX_L }, (_, i) => seededLeaf(P, J, i, i % 2 === 0 ? 0 : 1));
        await assertNoSecond("straddle4^5", buildHonest(P, 4 ** 5 - 3, leaves));
    });

    it("a batch on the last index of the tree has no second witness", async () => {
        // Every digit is 3: all 33 frontier slots are filled and read, the
        // opposite extreme from start 0, and the capacity check is tight.
        await assertNoSecond(
            "lastIndex",
            buildHonest(P, 4 ** BATCH_DEPTH - 1, [simpleLeaf({ J, P, val: 42n, isDeposit: 1 })]),
        );
    });

    it("a single zero-value fee note has no second witness", async () => {
        // The degenerate slot in isolation: at leaf_public_in == 0 the binding
        // reduces to cv_dep == rcv·H and the asset generator leaves the system,
        // so `leaf_asset` is held only by step 6a's canonicalisation of it to 0.
        // Slot position is irrelevant — 6a is per-slot and refers to no
        // neighbour, so a worthless leaf is legal anywhere in the batch.
        await assertNoSecond(
            "zeroValueFee",
            buildHonest(P, 0, depositPairs(P, J, 2)),
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
                    // Any interleaving is satisfiable: step 6a is per-slot and
                    // refers to no neighbour. A deposit leaf is drawn worthless
                    // at asset 0 on half the draws — at ANY slot, since the
                    // degenerate-binding case 6a governs is not tied to parity.
                    const leaves = Array.from({ length: count }, (_, i) =>
                        flags[i] === 1 && worthless[i] === 1
                            ? seededLeaf(P, J, i, 1, 0n, 0n)
                            : seededLeaf(P, J, i, flags[i]));
                    await assertNoSecond(
                        `random(count=${count}, prefill=${prefill})`,
                        buildHonest(P, prefill, leaves),
                    );
                },
            ),
            fcParams,
        );
    });
});
