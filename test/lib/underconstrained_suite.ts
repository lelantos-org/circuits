// Shared scaffolding for the R1CS second-witness suites.
//
// `test/fuzz/underconstrained.fuzz.test.ts` (4x6) and
// `underconstrained_batch.fuzz.test.ts` run the same search over different
// circuits. Per-circuit parts stay in each suite: which honest witnesses to
// sweep, how to project a published witness into circom inputs, and which gadget
// census the detector must see.
//
// This module holds the shared parts: loading the two builds, assembling the
// group sources, and the verdict applied to a finding list, so a change to the
// verdict (a new severity, a different vacuity guard) applies to both suites.

import { expect } from "chai";

import {
    compileConstraintsOnly,
    loadCircuitArtifacts,
    type CircuitInput,
} from "./circuit";
import { loadR1cs, loadSymbols, type R1csView, type SymbolTable } from "./r1cs";
import { allGroups, confirm, formatReport, searchWitness, type Finding, type Group } from "./underconstrained";
import { partitionExplained } from "./explain";
import {
    aliasableGroups,
    findBitGroups,
    groupsWithFreeBits,
    MAX_SAFE_BITS,
    type BitGroup,
} from "./bit_groups";

/** Everything the searches need for one circuit, loaded once per suite. */
export interface SearchContext {
    view: R1csView;
    symbols: SymbolTable;
    tester: { calculateWitness(i: CircuitInput, s?: boolean): Promise<bigint[]> };
    groups: Group[];
    bitGroups: BitGroup[];
}

/**
 * Compile a circuit both ways and build the search inputs.
 *
 * Bit decompositions are searched in the unoptimized system: `--O2` substitutes
 * the weighted sum away and leaves no structure to match. See
 * `compileConstraintsOnly` for why a result there carries over to the optimized
 * system a proof binds.
 *
 * The two compiles are separate circom processes writing to separate
 * directories, so they run together.
 */
export async function loadSearchContext(circuitPath: string): Promise<SearchContext> {
    const [artifacts, o0] = await Promise.all([
        loadCircuitArtifacts(circuitPath),
        compileConstraintsOnly(circuitPath),
    ]);

    const [view, symbols, bitGroups] = await Promise.all([
        loadR1cs(artifacts.r1csPath),
        loadSymbols(artifacts.symPath),
        loadR1cs(o0.r1csPath).then(findBitGroups),
    ]);

    return { view, symbols, tester: artifacts.tester, groups: allGroups(view, symbols), bitGroups };
}

/**
 * Run both witness-level searches over one honest witness and assert the result.
 *
 * Takes the witness vector rather than a bundle, so each suite keeps its own
 * projection into circom inputs.
 *
 * Every finding is re-checked against the whole system by `confirm` before it is
 * judged. The algebra is exact, so a refutation indicates a bug in the search
 * rather than the circuit. It fails the test instead of being dropped from the
 * finding list, since a search that reports nothing is indistinguishable from a
 * circuit with nothing to report.
 */
export function assertNoSecondWitness(
    ctx: SearchContext,
    label: string,
    witness: bigint[],
): Finding[] {
    const { view, symbols, groups } = ctx;

    // Both searches assume `t = 0` is a root of every constraint they examine,
    // which holds only for a satisfying witness.
    expect(view.firstViolation(witness)).to.equal(
        -1,
        `${label}: the honest witness must satisfy the R1CS before it can be mutated`,
    );

    const findings = searchWitness(view, symbols, witness, groups);

    for (const f of findings) {
        const violated = confirm(view, witness, f);
        expect(violated).to.equal(
            -1,
            `${label}: search claimed ${f.family} admits a step of ${f.t}, but ` +
                `constraint ${violated} rejects it — the algebra is wrong`,
        );
    }

    const breaks = findings.filter(f => f.severity === "break");
    expect(breaks, `${label}: SOUNDNESS BREAK — a public signal admits a second value\n` +
        formatReport(breaks)).to.have.lengthOf(0);

    const { unexplained } = partitionExplained(findings, witness, symbols);
    expect(unexplained, `${label}: finding(s) with no verified explanation\n` +
        formatReport(unexplained) +
        "\n  (add an Explainer in lib/explain.ts, with its precondition " +
        "checked against the witness — do not widen a name list)").to.have.lengthOf(0);

    return findings;
}

/**
 * The three witness-independent structural checks, declared for one suite.
 *
 * They depend only on `ctx`, so both fuzz suites share them. The census test is
 * per-suite: the gadgets a circuit contains differ, and pinning them detects a
 * detector that matches nothing.
 *
 * `ctx` is passed as a thunk because `loadSearchContext` runs in `before`, after
 * the `it`s are declared.
 *
 * `minMultiGroups` is the floor for the group search having anything to walk;
 * derive it per circuit rather than copying a number across shapes.
 */
export function registerStructuralTests(ctx: () => SearchContext, minMultiGroups: number): void {
    it("no bit decomposition is wide enough to alias mod p", () => {
        const wide = aliasableGroups(ctx().bitGroups);
        const detail = wide
            .map(g => `  width ${g.width} at constraint ${g.constraint}.${g.slot} ` +
                `(signals ${g.signals.slice(0, 4).join(", ")}...)`)
            .join("\n");
        expect(wide, "a decomposition of width > " + MAX_SAFE_BITS + " does not determine " +
            "its input: the bits of v and of v + p both satisfy the sum\n" + detail)
            .to.have.lengthOf(0);
    });

    it("every weight in a bit decomposition is pinned to {0, 1}", () => {
        const leaky = groupsWithFreeBits(ctx().bitGroups);
        const detail = leaky
            .map(g => `  constraint ${g.constraint}.${g.slot} width ${g.width}: ` +
                `weights ${g.unconstrainedBits.join(", ")} carry no booleanity constraint`)
            .join("\n");
        expect(leaky, "a weight whose signal is a free field element makes the sum " +
            "reachable from any target, so the decomposition constrains nothing\n" + detail)
            .to.have.lengthOf(0);
    });

    it("the group search covers the circuit's gadgets and constraints", () => {
        const multi = ctx().groups.filter(g => g.signals.length >= 2);
        console.log(`    groups: ${ctx().groups.length} (${multi.length} with 2+ signals)`);
        expect(multi.length, "no group has two signals, so the multi-signal " +
            "search has nothing to walk and its results mean nothing")
            .to.be.greaterThan(minMultiGroups);
    });
}
