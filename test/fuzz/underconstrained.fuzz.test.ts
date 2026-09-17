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

import { type CircuitInput } from "../lib/circuit";
import { logBitGroupCensus, useSearchSuite } from "../lib/underconstrained_suite";
import { formatReport, sweepSingleSignal } from "../lib/underconstrained";
import { explain, partitionExplained } from "../lib/explain";
import { buildTxBuilder, TxBuilder, DEFAULT_ASSET as ASSET } from "../lib/transact";
import { circuitSignals, type TransactWitnessBundle } from "../ref/witness";
import { ALICE_NSK, BOB_NSK, DEPTH, TIMEOUT_HEAVY, TWO_252 } from "../lib/constants";
import { ASSET_B, CIRCUIT } from "../transact/setup";
import { arbBalancedSplit, arbNsk, MAX_VALUE, fcParamsFor } from "./arbitraries";

const fcParams = fcParamsFor("UNDERCONSTRAINED");

describe("underconstrained_4x6 [fuzz]", function () {
    this.timeout(TIMEOUT_HEAVY);

    // ===== structural: bit decompositions =====
    //
    // Witness-independent, so a single run covers every instance in the circuit.
    // Runs against the `--O0` build (see `loadSearchContext`).
    //
    // The challenge-only fields are dropped before the witness calculator sees
    // a bundle; see `projectingTester`.
    const suite = useSearchSuite<TransactWitnessBundle>(
        CIRCUIT,
        bundle => circuitSignals(bundle) as unknown as CircuitInput,
        1000,
    );
    const assertNoSecond = suite.assertNoSecond;

    let tx: TxBuilder;
    before(async () => {
        tx = await buildTxBuilder(DEPTH);
    });

    it("the detector sees the decompositions the circuit is known to contain", () => {
        const hist = logBitGroupCensus(suite.ctx);

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
        const { view, symbols } = suite.ctx;
        const w = await suite.witnessFor(tx.fullShape());
        const findings = sweepSingleSignal(view, w, symbols);
        const { explained } = partitionExplained(findings, w, symbols);
        expect(explained.length, "nothing was explained, so this proves nothing")
            .to.be.greaterThan(0);

        for (const f of explained.slice(0, 8)) {
            const base = f.support[0].name.slice(0, -".inv".length);
            const inIndex = symbols.indexOf(`${base}.in`);
            const outIndex = symbols.indexOf(`${base}.out`);

            // A non-zero IsZero input (equivalently out = 0) means the hint is
            // not free by design, so the explanation must not apply.
            const doctored = w.slice();
            if (inIndex !== undefined) doctored[inIndex] = 1n;
            else if (outIndex !== undefined) doctored[outIndex] = 0n;
            else throw new Error(`${base}: neither sibling survived; explain should not have accepted`);

            expect(explain(f, doctored, symbols), `${base}: the explanation survived ` +
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
        await assertNoSecond("deposit", tx.spend(
            tx.oneRealOneDummy(1000n, ALICE_NSK),
            [tx.note(1500n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            { publicIn: 500n },
        ));
    });

    it("the withdraw shape has no second witness", async () => {
        await assertNoSecond("withdraw", tx.spend(
            tx.oneRealOneDummy(1000n, ALICE_NSK),
            [tx.note(600n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            { publicOut: 400n },
        ));
    });

    // Both public buckets non-zero: `pub_eq` compares the public asset against
    // every slot's, so this witness leaves the fewest of those comparisons
    // trivially zero.
    it("a shape with both public buckets non-zero has no second witness", async () => {
        await assertNoSecond("publicInAndOut", tx.spend(
            tx.oneRealOneDummy(1000n, ALICE_NSK),
            [tx.note(1400n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            { publicIn: 700n, publicOut: 300n },
        ));
    });

    // Two assets. `PerAssetValueBalance` runs its comparisons per (slot, asset)
    // pair, so a second asset changes which of them hold and which `IsZero`
    // hints are free, exercising a different subset of the circuit.
    it("a two-asset shape has no second witness", async () => {
        await assertNoSecond("twoAssets", tx.spend(
            tx.plant([tx.note(100n, ALICE_NSK, 1n, ASSET), tx.note(50n, ALICE_NSK, 2n, ASSET_B)], ALICE_NSK),
            [tx.note(100n, BOB_NSK, 100n, ASSET), tx.note(50n, ALICE_NSK, 200n, ASSET_B)],
        ));
    });

    // Four assets across every slot, so all eleven candidate rows of
    // `PerAssetValueBalance` carry a different sum and its ~110 `IsEqual`
    // comparators are exercised in both directions. In the single- and
    // two-asset shapes above most of those comparisons are trivially equal or
    // trivially zero, which is exactly when an `IsZero` hint can be free.
    it("a four-asset shape has no second witness", async () => {
        await assertNoSecond("fourAssets", tx.fullShapeMultiAsset());
    });

    // Range ceilings, where a Num2Bits sits one bit from rejecting: values at
    // 2^64 - 1 and blinders at 2^252 - 1. A decomposition whose top digit is the
    // only set one exercises constraints the mid-range witnesses never reach.
    it("a shape at the value and blinder ceilings has no second witness", async () => {
        const maxRcv = TWO_252 - 1n;
        const wide = { ...tx.note(MAX_VALUE, ALICE_NSK, 1n), rcv: maxRcv, rcvDep: maxRcv - 1n };
        const outA = { ...tx.note(MAX_VALUE, ALICE_NSK, 9n), rcv: maxRcv - 2n, rcvDep: maxRcv - 3n };
        await assertNoSecond("ceilings", tx.spend(tx.plant([wide], ALICE_NSK), [outA]));
    });

    // All values zero: a real input of value 0 spending to outputs of value 0.
    // Zero makes products vanish, and a vanishing product can leave a
    // constraint not restricting the signal it pins.
    it("an all-zero-value shape has no second witness", async () => {
        await assertNoSecond("zeroValues", tx.spend(
            tx.plant([tx.note(0n, ALICE_NSK, 1n)], ALICE_NSK),
            [tx.note(0n, ALICE_NSK, 9n), tx.note(0n, BOB_NSK, 11n)],
        ));
    });

    it("random balanced spends have no second witness", async () => {
        await fc.assert(
            fc.asyncProperty(
                arbBalancedSplit(),
                arbNsk(),
                arbNsk(),
                async ({ v1, v2, o1, o2 }, aliceNsk, bobNsk) => {
                    await assertNoSecond(
                        `balanced(${v1}, ${v2} -> ${o1}, ${o2})`,
                        tx.transfer({ v1, v2, o1, o2 }, aliceNsk, bobNsk, [1n, 2n, 9n, 11n]),
                    );
                },
            ),
            fcParams,
        );
    });
});
