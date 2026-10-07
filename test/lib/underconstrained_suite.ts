// Shared scaffolding for the R1CS second-witness suites: loading the two
// builds, assembling the group sources, and the verdict applied to a finding
// list. Each suite supplies its honest witnesses, its projection into circom
// inputs, and its gadget census.

import { expect } from "chai";

import {
    compileConstraintsOnly,
    loadCircuitArtifacts,
    type CircuitInput,
} from "./circuit";
import { SEARCH_OPT } from "./constants";
import { loadR1cs, loadSymbols, type R1csView, type SymbolTable } from "./r1cs";
import { allGroups, confirm, formatReport, searchWitness, type Finding, type Group } from "./underconstrained";
import { partitionExplained } from "./explain";
import {
    aliasableGroups,
    findBitGroups,
    groupsWithFreeBits,
    widthHistogram,
    MAX_SAFE_BITS,
    type BitGroup,
} from "./bit_groups";
import { pendingCtx } from "./harness";

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
 * The witness-level searches read the `--O1` system, with the witness from the
 * same compile; see `SEARCH_OPT`.
 *
 * Bit decompositions are searched in the unoptimized system: `--O2` substitutes
 * the weighted sum away and leaves no structure to match. See
 * `compileConstraintsOnly` for why a result there carries over to the optimized
 * system a proof binds.
 *
 * The two compiles write to separate directories, so they run concurrently.
 */
export async function loadSearchContext(circuitPath: string): Promise<SearchContext> {
    const [artifacts, o0] = await Promise.all([
        loadCircuitArtifacts(circuitPath, SEARCH_OPT),
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
 * Every finding is first re-checked against the whole system by `confirm`. A
 * refutation indicates a bug in the search, so it fails the test rather than
 * being dropped: a search that reports nothing is indistinguishable from a
 * circuit with nothing to report.
 */
export function assertNoSecondWitness(
    ctx: SearchContext,
    label: string,
    witness: bigint[],
): Finding[] {
    const { view, symbols, groups } = ctx;

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
 * One circuit's search suite: the context, loaded in `before`, and the
 * assertion over a subject in the suite's own witness shape.
 */
export interface SearchSuite<T> {
    /** Populated by `before`; reading it earlier throws, see `pendingCtx`. */
    readonly ctx: SearchContext;
    witnessFor(subject: T): Promise<bigint[]>;
    /** `assertNoSecondWitness` over `subject`'s honest witness. */
    assertNoSecond(label: string, subject: T): Promise<Finding[]>;
}

/**
 * Register the `before` hook that loads `circuitPath`, and the structural
 * tests, for one suite. `toInput` projects a subject (a transact bundle, a batch
 * witness) to the circom input; `minMultiGroups` is passed to
 * `registerStructuralTests`.
 */
export function useSearchSuite<T>(
    circuitPath: string,
    toInput: (subject: T) => CircuitInput,
    minMultiGroups: number,
): SearchSuite<T> {
    const holder = pendingCtx<{ ctx: SearchContext }>(["ctx"], `useSearchSuite(${circuitPath})`);
    before(async () => {
        holder.ctx = await loadSearchContext(circuitPath);
    });

    const suite: SearchSuite<T> = {
        get ctx() {
            return holder.ctx;
        },
        witnessFor: subject => holder.ctx.tester.calculateWitness(toInput(subject), true),
        assertNoSecond: async (label, subject) =>
            assertNoSecondWitness(holder.ctx, label, await suite.witnessFor(subject)),
    };

    registerStructuralTests(() => holder.ctx, minMultiGroups);
    return suite;
}

/** Print the bit-decomposition census and return it, `width -> count`. */
export function logBitGroupCensus(ctx: SearchContext): Map<number, number> {
    const hist = widthHistogram(ctx.bitGroups);
    const lines = [...hist].map(([w, n]) => `    ${String(n).padStart(5)}x  width ${w}`);
    console.log(`    bit-decomposition groups: ${ctx.bitGroups.length}\n${lines.join("\n")}`);
    return hist;
}

/**
 * The three witness-independent structural checks, declared for one suite.
 *
 * `ctx` is a thunk because `loadSearchContext` runs in `before`, after the
 * `it`s are declared. `minMultiGroups` is the per-circuit count the
 * multi-signal groups must exceed for the group search to have anything to
 * walk.
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
