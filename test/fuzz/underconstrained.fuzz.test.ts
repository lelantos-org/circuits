// Negative test generation against the CONSTRAINT SYSTEM, not the witness
// calculator.
//
// `test/transact/tamper.test.ts` is the input-level half of this: change one
// field of the circom input, require witness generation to fail. It covers a lot
// and it has a blind spot it cannot close from where it stands.
// `calculateWitness` runs the template body, so whatever input it accepts it
// turns into a SELF-CONSISTENT witness — that is the generator's job. A signal
// the template computes but never constrains is therefore invisible to it, and
// that signal is exactly what a malicious prover controls, because a Groth16
// proof binds the R1CS and nothing else.
//
// So this suite starts from an honest witness and edits the witness VECTOR,
// asking `lib/r1cs.ts` — not the wasm — whether the result still satisfies.
// Three searches run:
//
//   * `sweepSingleSignal` decides, exactly and for every one of the ~100k
//     witness entries, whether any second value is admissible on its own.
//   * `sweepGroups` covers signals that must move TOGETHER — a pair sliding in
//     step, a hint and the value it feeds — by walking the null space of the
//     Jacobian restricted to each gadget and each constraint. Those directions
//     are invisible to the sweep above, since along them every individual
//     signal is still pinned by the others.
//   * `findBitGroups` rules out the two bit-decomposition bugs (aliasing, free
//     digits) structurally, over every instance in the circuit.
//
// Between them they cover overflow/aliasing, missing equality constraints,
// unconstrained signals, range-check width and paired-signal freedom. They do
// NOT cover every underconstraint — the group search holds everything outside a
// group fixed, so a conspiracy spanning unrelated components is out of reach,
// and null-space directions are straight lines, so freedom along a curved
// variety is too. `just picus` decides the general case.

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
     * The order is the point: `finalize` reads an authentication path, and a
     * path taken before the last insert authenticates against a root that no
     * longer exists. `TxBuilder.nRealInputs` does this for notes it builds
     * itself; the scenarios below need to hand over notes they have already
     * shaped — a second asset, a blinder at its ceiling — so they build them.
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
    // Witness-independent, so once is enough and the result covers every
    // instance in the circuit rather than the ones some witness happened to
    // exercise. Run against the `--O0` build (see `before`).

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

    // The group search must actually be looking at something. Both sources are
    // derived from the compiled circuit, so a change to either could silently
    // reduce them to nothing and every group result below would be vacuous.

    // An explainer that accepted everything would turn every witness-level test
    // below green while checking nothing — the same vacuity trap the bit-group
    // detector fell into. So verify the precondition is load-bearing: take a
    // finding the explainer accepts, break only the fact it rests on, and
    // require it to refuse.
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

            // Falsify the precondition and nothing else: a non-zero IsZero input
            // (equivalently out = 0) means the hint is NOT free by design, so the
            // explanation must not stand.
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
    // Which signals are free is a property OF the witness, not only of the
    // circuit: an `IsZero` hint is free exactly when its input is zero, and a
    // zero or a boundary value anywhere can leave an otherwise-pinned signal
    // loose. So the scenarios below deliberately spread over the shapes and the
    // extremes the circuit admits rather than re-testing one happy path.

    it("the fully-occupied shape has no second witness", async () => {
        const findings = await assertNoSecond("fullShape", tx.fullShape());
        console.log(`    fullShape: ${findings.length} explained free signal(s)\n` +
            formatReport(findings));
    });

    it("the balanced 2-in-2-out shape has no second witness", async () => {
        await assertNoSecond("balanced", tx.balanced());
    });

    // Not an all-dummy bundle: `Transact` asserts `all_dummy.out === 0`
    // (src/lib/transact.circom), so every input slot being a dummy is rejected
    // outright and there would be no honest witness to mutate. One real input
    // alongside `public_in` is the shape a shielding spend actually takes.
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

    // Both public buckets non-zero at once: `pub_eq` compares the public asset
    // against every slot's, so this is the witness that leaves the fewest of
    // those comparisons trivially zero.
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

    // Two assets at once. `PerAssetValueBalance` runs its comparisons per
    // (slot, asset) pair, so a second asset changes WHICH of them hold and
    // therefore which `IsZero` hints go free — a different subset of the
    // circuit from every single-asset shape above.
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

    // Everything at zero that the circuit still accepts: a real input of value 0
    // spending to outputs of value 0. Zero is the value that makes products
    // vanish, and a vanishing product is exactly how a constraint stops
    // restricting the signal it was meant to pin.
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
