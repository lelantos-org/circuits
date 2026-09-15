// Negative test generation against the constraint system rather than the
// witness calculator.
//
// `test/transact/tamper.test.ts` is the input-level counterpart: change one
// field of the circom input and require witness generation to fail.
// `calculateWitness` runs the template body, so any input it accepts becomes a
// self-consistent witness. A signal the template computes but never constrains
// is therefore not observable at the input level, yet a malicious prover
// controls it, because a Groth16 proof binds only the R1CS.
//
// This suite starts from an honest witness and edits the witness vector,
// checking satisfaction with `lib/r1cs.ts` rather than the wasm. Three searches
// run:
//
//   * `sweepSingleSignal` decides exactly, for each of the ~100k witness
//     entries, whether a second value is admissible on its own.
//   * `sweepGroups` covers signals that must move together (a pair moving in
//     step, a hint and the value it feeds) by walking the null space of the
//     Jacobian restricted to each gadget and each constraint. The single-signal
//     sweep misses these directions because each signal is individually pinned
//     by the others.
//   * `findBitGroups` rules out the two bit-decomposition bugs (aliasing, free
//     digits) structurally, over every instance in the circuit.
//
// Together they cover overflow/aliasing, missing equality constraints,
// unconstrained signals, range-check width and paired-signal freedom. They do
// not cover every underconstraint: the group search holds everything outside a
// group fixed, so freedom spanning unrelated components is not found, and
// null-space directions are straight lines, so freedom along a curved variety
// is not found either. `just picus` decides the general case.

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
import { explain, partitionExplained } from "../lib/explain";
import { widthHistogram } from "../lib/bit_groups";
import { buildTxBuilder, TxBuilder, DEFAULT_ASSET as ASSET } from "../lib/transact";
import { circuitSignals, type TransactWitnessBundle } from "../ref/witness";
import { ALICE_NSK, BOB_NSK, DEPTH, TIMEOUT_HEAVY, TWO_252 } from "../lib/constants";
import type { Field, Note, SpentNote } from "../helpers";
import { ASSET_B } from "../transact/setup";
import { arbBalancedSplit, arbNsk, MAX_VALUE, fcParamsFor } from "./arbitraries";

const CIRCUIT = srcPath("4x6.circom");
const fcParams = fcParamsFor("UNDERCONSTRAINED");

describe("underconstrained_4x6 [fuzz]", function () {
    this.timeout(TIMEOUT_HEAVY);

    let ctx: SearchContext;
    let tx: TxBuilder;

    before(async () => {
        const [context, builder] = await Promise.all([
            loadSearchContext(CIRCUIT),
            buildTxBuilder(DEPTH),
        ]);
        ctx = context;
        tx = builder;
    });

    /**
     * Insert notes into a fresh tree, freeze the root, then take the proofs.
     *
     * Order matters: `finalize` reads an authentication path, and a path taken
     * before the last insert authenticates against a stale root.
     * `TxBuilder.nRealInputs` does this for notes it builds itself; the
     * scenarios below pass pre-shaped notes (a second asset, a blinder at its
     * ceiling).
     */
    function spend(notes: Note[], nsk: Field): { root: Field; inputs: SpentNote[] } {
        const tree = tx.newTree();
        const inserted = notes.map(n => tx.insert(tree, n, nsk));
        const root = tree.root();
        return { root, inputs: inserted.map(i => tx.finalize(tree, i)) };
    }

    /** Honest witness vector for a bundle, with the challenge-only fields dropped. */
    async function witnessFor(bundle: TransactWitnessBundle): Promise<bigint[]> {
        return ctx.tester.calculateWitness(
            circuitSignals(bundle) as unknown as CircuitInput,
            true,
        );
    }

    /** Both searches over one honest bundle, in this suite's witness shape. */
    async function assertNoSecond(label: string, bundle: TransactWitnessBundle) {
        return assertNoSecondWitness(ctx, label, await witnessFor(bundle));
    }

    // ===== structural: bit decompositions =====
    //
    // Witness-independent, so a single run covers every instance in the circuit.
    // Runs against the `--O0` build (see `before`).

    registerStructuralTests(() => ctx, 1000);

    it("the detector sees the decompositions the circuit is known to contain", () => {
        const hist = widthHistogram(ctx.bitGroups);
        const lines = [...hist].map(([w, n]) => `    ${String(n).padStart(5)}x  width ${w}`);
        console.log(`    bit-decomposition groups: ${ctx.bitGroups.length}\n${lines.join("\n")}`);

        expect(hist.get(252), "expected 20 Num2Bits(252): one per blinder, " +
            "rcv and rcv_dep over N_IN + N_OUT slots").to.equal(20);
        expect(hist.get(2), "expected 44 Num2Bits(2): one path-index digit per " +
            "level per input, N_IN * DEPTH").to.equal(44);
        expect(Math.max(...hist.keys()), "the widest decomposition should be MulH's")
            .to.equal(252);
    });

    // An explainer that accepted everything would make every witness-level test
    // below pass vacuously. This takes findings the explainer accepts, falsifies
    // only the precondition each rests on, and requires the explainer to refuse.
    it("an explanation is refused once its precondition stops holding", async () => {
        const w = await witnessFor(tx.fullShape());
        const findings = sweepSingleSignal(ctx.view, w, ctx.symbols);
        const { explained } = partitionExplained(findings, w, ctx.symbols);
        expect(explained.length, "nothing was explained, so this proves nothing")
            .to.be.greaterThan(0);

        for (const f of explained.slice(0, 8)) {
            const base = f.support[0].name.slice(0, -".inv".length);
            const inIndex = ctx.symbols.indexOf(`${base}.in`);
            const outIndex = ctx.symbols.indexOf(`${base}.out`);

            // A non-zero IsZero input (equivalently out = 0) means the hint is
            // not free by design, so the explanation must not apply.
            const doctored = w.slice();
            if (inIndex !== undefined) doctored[inIndex] = 1n;
            else if (outIndex !== undefined) doctored[outIndex] = 0n;
            else throw new Error(`${base}: neither sibling survived; explain should not have accepted`);

            expect(explain(f, doctored, ctx.symbols), `${base}: the explanation survived ` +
                "its own precondition being false, so it is not checking it").to.equal(null);
        }
    });

    // ===== witness-level: both sweeps, over a spread of honest witnesses =====
    //
    // Which signals are free depends on the witness, not only the circuit: an
    // `IsZero` hint is free exactly when its input is zero, and a zero or
    // boundary value can leave an otherwise-pinned signal free. The scenarios
    // below therefore span the shapes and extremes the circuit admits.

    it("the fully-occupied shape has no second witness", async () => {
        const findings = await assertNoSecond("fullShape", tx.fullShape());
        console.log(`    fullShape: ${findings.length} explained free signal(s)\n` +
            formatReport(findings));
    });

    it("the balanced 2-in-2-out shape has no second witness", async () => {
        await assertNoSecond("balanced", tx.balanced());
    });

    // Not an all-dummy bundle: `Transact` asserts `all_dummy.out === 0`
    // (src/lib/transact.circom), so an all-dummy bundle has no honest witness.
    // One real input alongside `public_in` is the shape of a shielding spend.
    it("the deposit shape has no second witness", async () => {
        const { root, inputs } = tx.oneRealOneDummy(1000n, ALICE_NSK);
        await assertNoSecond("deposit", tx.build({
            publicIn: 500n,
            inputs,
            outputs: [tx.note(1500n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            merkleRoot: root,
        }));
    });

    it("the withdraw shape has no second witness", async () => {
        const { root, inputs } = tx.oneRealOneDummy(1000n, ALICE_NSK);
        await assertNoSecond("withdraw", tx.build({
            publicOut: 400n,
            inputs,
            outputs: [tx.note(600n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            merkleRoot: root,
        }));
    });

    // Both public buckets non-zero: `pub_eq` compares the public asset against
    // every slot's, so this witness leaves the fewest of those comparisons
    // trivially zero.
    it("a shape with both public buckets non-zero has no second witness", async () => {
        const { root, inputs } = tx.oneRealOneDummy(1000n, ALICE_NSK);
        await assertNoSecond("publicInAndOut", tx.build({
            publicIn: 700n,
            publicOut: 300n,
            inputs,
            outputs: [tx.note(1400n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            merkleRoot: root,
        }));
    });

    // Two assets. `PerAssetValueBalance` runs its comparisons per (slot, asset)
    // pair, so a second asset changes which of them hold and which `IsZero`
    // hints are free, exercising a different subset of the circuit.
    it("a two-asset shape has no second witness", async () => {
        const { root, inputs } = spend(
            [tx.note(100n, ALICE_NSK, 1n, ASSET), tx.note(50n, ALICE_NSK, 2n, ASSET_B)],
            ALICE_NSK,
        );
        await assertNoSecond("twoAssets", tx.build({
            inputs,
            outputs: [
                tx.note(100n, BOB_NSK, 100n, ASSET),
                tx.note(50n, ALICE_NSK, 200n, ASSET_B),
            ],
            merkleRoot: root,
        }));
    });

    // Range ceilings, where a Num2Bits sits one bit from rejecting: values at
    // 2^64 - 1 and blinders at 2^252 - 1. A decomposition whose top digit is the
    // only set one exercises constraints the mid-range witnesses never reach.
    it("a shape at the value and blinder ceilings has no second witness", async () => {
        const maxRcv = TWO_252 - 1n;
        const wide = { ...tx.note(MAX_VALUE, ALICE_NSK, 1n), rcv: maxRcv, rcvDep: maxRcv - 1n };
        const { root, inputs } = spend([wide], ALICE_NSK);

        const outA = { ...tx.note(MAX_VALUE, ALICE_NSK, 9n), rcv: maxRcv - 2n, rcvDep: maxRcv - 3n };
        await assertNoSecond("ceilings", tx.build({
            inputs,
            outputs: [outA],
            merkleRoot: root,
        }));
    });

    // All values zero: a real input of value 0 spending to outputs of value 0.
    // Zero makes products vanish, and a vanishing product can leave a
    // constraint not restricting the signal it pins.
    it("an all-zero-value shape has no second witness", async () => {
        const { root, inputs } = spend([tx.note(0n, ALICE_NSK, 1n)], ALICE_NSK);
        await assertNoSecond("zeroValues", tx.build({
            inputs,
            outputs: [tx.note(0n, ALICE_NSK, 9n), tx.note(0n, BOB_NSK, 11n)],
            merkleRoot: root,
        }));
    });

    it("random balanced spends have no second witness", async () => {
        await fc.assert(
            fc.asyncProperty(
                arbBalancedSplit(),
                arbNsk(),
                arbNsk(),
                async ({ v1, v2, o1, o2 }, aliceNsk, bobNsk) => {
                    const { root, inputs } = spend(
                        [tx.note(v1, aliceNsk, 1n, ASSET), tx.note(v2, aliceNsk, 2n, ASSET)],
                        aliceNsk,
                    );
                    await assertNoSecond(
                        `balanced(${v1}, ${v2} -> ${o1}, ${o2})`,
                        tx.build({
                            publicAssetId: ASSET,
                            inputs,
                            outputs: [tx.note(o1, bobNsk, 9n), tx.note(o2, aliceNsk, 11n)],
                            merkleRoot: root,
                        }),
                    );
                },
            ),
            fcParams,
        );
    });
});
