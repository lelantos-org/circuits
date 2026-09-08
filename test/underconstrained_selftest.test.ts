// Does the negative-test generator actually catch anything?
//
// `test/fuzz/underconstrained.fuzz.test.ts` reports that `4x6` has no second
// witness and no bad bit decomposition. That result is worth exactly as much as
// the detector under it, and a detector that matches NOTHING reports the same
// clean bill of health as a circuit with nothing to report. This is not a
// hypothetical: the first draft of `bit_groups.ts` matched zero groups in a
// circuit containing 87 of them, because circom emits the weighted sum with
// negative coefficients, and both checks built on it passed vacuously.
//
// So each check is pointed at a circuit that is broken in exactly the way the
// check exists to find, and is required to find it. The fixtures live in
// `test/fixtures/test_leak_*.circom` and are deliberately unsound; nothing under
// `src/` includes them.

import { expect } from "chai";

import {
    compileConstraintsOnly,
    fixturePath,
    loadCircuitArtifacts,
    type CircuitInput,
} from "./lib/circuit";
import { loadR1cs, loadSymbols } from "./lib/r1cs";
import {
    allGroups,
    confirm,
    formatReport,
    sweepGroups,
    sweepSingleSignal,
} from "./lib/underconstrained";
import { explain } from "./lib/explain";
import { aliasableGroups, findBitGroups, groupsWithFreeBits } from "./lib/bit_groups";
import { TIMEOUT_CIRCUIT } from "./lib/constants";

describe("underconstrained generator self-test", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    it("finds an output the circuit assigns but never constrains", async () => {
        const path = fixturePath("test_leak_missing_output_constraint.circom");
        const { tester, r1csPath, symPath } = await loadCircuitArtifacts(path);
        const [view, symbols] = await Promise.all([loadR1cs(r1csPath), loadSymbols(symPath)]);

        // The witness calculator is perfectly happy: it runs `out <-- in * in`
        // and returns a consistent witness. Nothing at the input level can see
        // the bug, which is the whole reason this module exists.
        const w = await tester.calculateWitness({ in: "7" } as CircuitInput, true);
        expect(view.firstViolation(w)).to.equal(-1, "the honest witness must satisfy");
        expect(w[1]).to.equal(49n, "the generator still computes in * in");

        const findings = sweepSingleSignal(view, w, symbols);
        const onOut = findings.filter(f => f.support.some(e => e.index === 1));

        expect(onOut, "the sweep must flag the unconstrained output").to.have.lengthOf(1);
        expect(onOut[0].severity).to.equal(
            "break",
            "an output that admits a second value is a soundness break, not malleability",
        );
        expect(onOut[0].kind).to.equal("unconstrained");
        // The alternate value really does satisfy the whole system.
        expect(confirm(view, w, onOut[0])).to.equal(-1);

        // And nothing explains it away: an unconstrained public output is the
        // thing the suite exists to catch, not a known-benign hint.
        expect(explain(onOut[0], w, symbols)).to.equal(
            null,
            "no explanation may account for an unconstrained output",
        );
    });

    // The group search earns its cost only if it sees something the unit sweep
    // cannot. This fixture is built so that it must: each signal of the pair is
    // pinned while the other holds still, so the unit sweep is required to find
    // NOTHING, and the freedom exists only along the direction where both move.
    it("finds a pair of signals that only move together", async () => {
        const path = fixturePath("test_leak_paired_signals.circom");
        const { tester, r1csPath, symPath } = await loadCircuitArtifacts(path);
        const [view, symbols] = await Promise.all([loadR1cs(r1csPath), loadSymbols(symPath)]);

        const w = await tester.calculateWitness({ in: "7", x: "5" } as CircuitInput, true);
        expect(view.firstViolation(w)).to.equal(-1, "the honest witness must satisfy");

        const single = sweepSingleSignal(view, w, symbols);
        expect(single, "the unit sweep must be blind to this bug, or the fixture " +
            "is not testing what the group search adds\n" + formatReport(single))
            .to.have.lengthOf(0);

        const found = sweepGroups(view, w, symbols, allGroups(view, symbols));

        expect(found.length, "the group search must find the paired freedom")
            .to.be.greaterThan(0);
        for (const f of found) {
            expect(f.support.length, "every group finding moves at least two signals")
                .to.be.greaterThan(1);
            expect(confirm(view, w, f)).to.equal(
                -1,
                `claimed direction ${f.family} does not actually satisfy the system`,
            );
        }
        // `out` rides along with the pair, so the public statement moves.
        expect(found.some(f => f.severity === "break"),
            "a direction that moves `out` must be reported as a break").to.equal(true);
    });

    it("finds a decomposition wide enough to alias mod p", async () => {
        const path = fixturePath("test_leak_alias_num2bits.circom");
        const { r1csPath } = await compileConstraintsOnly(path);
        const groups = findBitGroups(await loadR1cs(r1csPath));

        const wide = aliasableGroups(groups);
        expect(wide.length, "Num2Bits(254) must be reported as aliasable")
            .to.be.greaterThan(0);
        expect(Math.max(...wide.map(g => g.width))).to.equal(254);
    });

    it("finds a decomposition digit that carries no booleanity constraint", async () => {
        const path = fixturePath("test_leak_missing_booleanity.circom");
        const { r1csPath } = await compileConstraintsOnly(path);
        const groups = findBitGroups(await loadR1cs(r1csPath));

        const leaky = groupsWithFreeBits(groups);
        expect(leaky.length, "the digit with no booleanity constraint must be reported")
            .to.be.greaterThan(0);
        // The fixture frees index 5 of a 16-bit decomposition.
        const widest = leaky.reduce((a, b) => (b.width > a.width ? b : a));
        expect(widest.width).to.equal(16);
        expect(widest.unconstrainedBits).to.deep.equal([5]);
    });

    // The counterpart to the four above: the checks must also stay quiet on a
    // circuit that is correct, or "it fires" would be worth nothing either.
    it("stays quiet on a sound circuit", async () => {
        const path = fixturePath("test_merkle_d2.circom");
        const { r1csPath } = await compileConstraintsOnly(path);
        const bits = findBitGroups(await loadR1cs(r1csPath));

        expect(aliasableGroups(bits)).to.have.lengthOf(0);
        expect(groupsWithFreeBits(bits)).to.have.lengthOf(0);
    });
});
