// The R1CS-level second-witness search, over `tree_update_batch.circom`.
//
// `underconstrained.fuzz.test.ts` runs the same search over `4x6.circom`.
// `tree_update_batch.test.ts` only checks whether the wasm accepts an input
// object, where a signal the template computes but never constrains is not
// observable; this file provides constraint-system coverage for the batch
// circuit.
//
// It is a separate file rather than a parameterisation because the per-circuit
// part differs: the scenario builders are `TxBuilder` shapes there and batch
// witnesses here, and each suite's detector self-check pins its own gadget
// census. The search part is shared: `lib/underconstrained_suite.ts` loads both
// builds and judges a finding list.
//
// Out of scope: the forgery in `tree_update_batch.test.ts :: divergent witness`
// is not reachable by these searches, by construction:
//
//   * The searches walk straight lines from an honest witness. That forgery is
//     a differently shaped witness (`is_deposit` cleared, the whole `active_dep`
//     chain gated off), not a null direction from a deposit witness.
//   * `severity: "break"` means "some moving entry is an output or a public
//     input". The forgery holds `y` and `z` fixed, so even if found it would be
//     graded `malleable`.
//
// The two suites are complementary: this one decides local freedom around
// honest witnesses, and the divergent-witness block decides whether the witness
// may disagree with the calldata it is proved against. `just picus` decides the
// general case, at weak safety.

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
        // The circuit builds and the two gadget tables are independent, so they
        // load concurrently.
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
    // Witness-independent, so a single run covers every instance in the circuit.

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
    // frontier signal may be free at any digit pattern. The sweeps below would
    // also fail on one, since no explanation covers it; this states the property
    // directly. start_index = 0 has every digit 0, so all 33 slots are unread.
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
    // Which signals are free depends on the witness. The circuit branches on how
    // many slots are active, whether each leaf is a deposit or a spend, and where
    // the frontier sits, so the scenarios span those three axes.

    it("a single deposit leaf has no second witness", async () => {
        const findings = await assertNoSecond(
            "oneDeposit",
            buildHonest(P, 0, [simpleLeaf({ J, P, val: 1000n, isDeposit: 1 })]),
        );
        console.log(`    oneDeposit: ${findings.length} explained free signal(s)\n` +
            formatReport(findings));
    });

    it("a single spend leaf has no second witness", async () => {
        // The deposit binding is gated off, so `cv_dep` carries only BabyCheck
        // and `leaf_asset`/`leaf_public_in` only their zeroings: the fewest
        // constraints on any active slot.
        await assertNoSecond(
            "oneSpend",
            buildHonest(P, 0, [simpleLeaf({ J, P, val: 1000n, isDeposit: 0 })]),
        );
    });

    it("a partial batch has no second witness", async () => {
        // Padding slots run the whole (1 - active[k]) * X === 0 block, where a
        // vanishing product can leave a constraint not restricting its signal.
        const leaves = Array.from({ length: 3 }, (_, i) => seededLeaf(P, J, i, 1));
        await assertNoSecond("partialBatch", buildHonest(P, 0, leaves));
    });

    it("a full flush of principal/fee pairs at fbps = 0 has no second witness", async () => {
        // Every fee note has zero value, so every odd slot's deposit binding is
        // degenerate and `leaf_asset` there is pinned only by step 6a. Without
        // 6a this witness would expose four free 64-bit coefficients.
        //
        // Also the all-slots-active case. The search results depend on the
        // witness only through which slots are active (each inactive slot adds
        // one free IsZero hint), so a separate full batch would sweep 113k
        // entries for the same finding set.
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
        // reduces to cv_dep == rcv·H and the asset generator drops out, so
        // `leaf_asset` is pinned only by step 6a's canonicalisation to 0. 6a is
        // per-slot with no reference to a neighbour, so a zero-value leaf is
        // valid at any slot.
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
                    // refers to no neighbour. A deposit leaf is drawn with zero
                    // value at asset 0 on half the draws, at any slot, since the
                    // degenerate-binding case 6a handles is not tied to parity.
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
