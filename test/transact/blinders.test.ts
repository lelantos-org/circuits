// Value-commitment blinders: free to choose, and additively separable in `y`.
//
// `PolyEval` binds a coefficient only if another constraint pins it
// (src/README.md § 2a). `ValueCommitPair` pins `cv` only relative to a
// prover-chosen blinder:
//
//     cv     = value·V^asset + rcv·H
//     cv_dep = value·V^asset + rcv_dep·H
//
// and `PerAssetPointBalance` (src/lib/balance.circom) checks
//
//     Sum(in_cv) + Sum(out_rH) == Sum(out_cv) + Sum(in_rH)
//
// in which every blinder appears on both sides and cancels. Each `rcv` therefore
// appears in no constraint outside the one or two coefficients it produces.
// `rcv_dep` does not enter the point balance at all, and `ValueCommitPair.rH_dep`
// has no reader.
//
// Each blinder is a free parameter on `y` at a fixed challenge. Unlike the
// public-scalar case in `binding.test.ts`, the challenge does not remove it: `z`
// is derived from prover-authored calldata, and the witness `cv` need not equal
// the calldata `cv`. The parameters compose: `PolyEval` is affine in each
// coefficient with slope z^k, and each blinder moves a disjoint pair of
// coefficients, so the displacements add exactly:
//
//     (y_both − y_base) ≡ (y_cv − y_base) + (y_dep − y_base)   (mod r)
//
// This reduces forging `y` to a modular k-sum over ~22 parameters rather than a
// 254-bit search. This file asserts that identity as a regression test.
//
// The cost of the k-sum is not established here: a k-tree at k=16 needs 2^51 in
// memory as well as time, which ~22 parameters do not obviously supply. The
// tests check only the structural claim: the blinders are free and their
// contributions to `y` are additively separable.
//
// Two candidate mitigations and their limitations:
//
//   * Hashing the blinders into `cm`, so each also moves a Poseidon output
//     (+2.3k constraints). This makes each parameter's contribution non-linear,
//     but separability is a property across parameters, and displacements from
//     distinct parameters still add. The parameter count is unchanged, so the
//     k-sum is unaffected; the last test below detects this.
//   * Deriving the blinders from the note opening, `rcv = Poseidon(rcm, rho)`.
//     This removes them as independent degrees of freedom, at ~15k constraints
//     once the output is reduced to RCV_BITS alias-free. However, `rcv` is the
//     sender's fresh per-spend blinder: deriving it from the note makes `in_cv`
//     at spend time a deterministic function of the note, equal to the creating
//     transaction's `out_cv`, which links creation and spend. This is a privacy
//     design decision, not a constraint-level fix.
//
// NOTE: the freedom remains open; the k-sum cost should be measured before
// choosing a mitigation.

import { expect } from "chai";

import { mod, type Field, type Note, type TransactWitnessBundle } from "../helpers";
import { expectAccepts, readOutput } from "../lib/expect";
import { ALICE_NSK, TIMEOUT_CIRCUIT } from "../lib/constants";
import { TxBuilder } from "../lib/transact";
import { useTransactCircuit } from "./setup";

describe("transact_4x6 / value-commitment blinders", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    /**
     * The balanced two-in-two-out witness, with output slot 0's blinders
     * overridden and the challenge pinned to `z`.
     *
     * Every variant is built through here, so the four differ only in the
     * blinders: same notes, values, nullifiers, tree and `z`.
     */
    function witnessWith(
        tx: TxBuilder,
        z: Field,
        override: Partial<Pick<Note, "rcv" | "rcvDep">>,
    ): TransactWitnessBundle {
        const out0 = { ...tx.note(75n, ALICE_NSK, 9n), ...override };
        return tx.spend(
            tx.twoRealInputs([100n, 50n], ALICE_NSK),
            [out0, tx.note(75n, ALICE_NSK, 11n)],
            { z },
        );
    }

    /** The circuit's own `y` for a witness, not the reference evaluation. */
    async function circuitY(bundle: TransactWitnessBundle): Promise<bigint> {
        const { circuit } = ctx;
        return readOutput(await expectAccepts(circuit, bundle));
    }

    // The challenge shared by all four variants. A parameter that moves `y` only
    // by also moving `z` is bound (the contract recomputes `z`); one that moves
    // `y` at a fixed `z` is not.
    const Z: Field = 0xdeadbeefcafef00dn;

    // Well inside RCV_BITS = 252, so Num2Bits is not exercised.
    const RCV_ALT: Field = 0x1234_5678_9abc_def0n;
    const RCV_DEP_ALT: Field = 0x0fed_cba9_8765_4321n;

    // The four witnesses, generated once, so each assertion compares cached `y`
    // values rather than rerunning 100k constraints.
    let y: Record<"base" | "cv" | "dep" | "both", bigint>;

    before(async () => {
        // Sequential: `TxBuilder` is stateful (`newTree` plus inserts), and
        // concurrent builds interleave its internals so the bundles no longer
        // differ only in their blinders.
        const at = (o: Partial<Pick<Note, "rcv" | "rcvDep">>) =>
            circuitY(witnessWith(ctx.tx, Z, o));
        const base = await at({});
        const cv = await at({ rcv: RCV_ALT });
        const dep = await at({ rcvDep: RCV_DEP_ALT });
        const both = await at({ rcv: RCV_ALT, rcvDep: RCV_DEP_ALT });
        y = { base, cv, dep, both };
    });

    // Successful generation of all four witnesses shows the blinders are free.
    // `PerAssetPointBalance` cancels `rcv` on both sides, and `rcv_dep` does not
    // enter it; its only reader is the `out_cv_dep` coefficient. A constrained
    // blinder would fail witness generation in `before`.

    it("out_rcv moves y at a fixed challenge", () => {
        expect(y.cv, "if the blinder could not move y it would be pinned, and the " +
            "coefficient argument in src/README.md § 2a would hold for it")
            .to.not.equal(y.base);
    });

    it("out_rcv_dep moves y at a fixed challenge", () => {
        expect(y.dep).to.not.equal(y.base);
    });

    it("the two blinders' contributions to y are additively separable", () => {
        // Separability makes the parameters compose, which decides whether
        // forging `y` is a k-sum or a search. `PolyEval` is affine in each
        // coefficient with slope z^k, and each blinder moves a disjoint set of
        // coefficients, so moving both displaces `y` by exactly the sum of the
        // individual displacements:
        //
        //     (y_both - y_base) == (y_cv - y_base) + (y_dep - y_base)   (mod r)
        //
        // A mitigation must break this exact equality. Hashing the blinders into
        // `cm` does not: each contribution becomes non-linear but the parameters
        // stay independent, so the identity still holds.
        //
        // The two tests above guard against vacuity: at zero displacement this
        // reads 0 == 0 + 0.
        expect(mod(y.both - y.base).toString(), "the joint displacement must equal the sum " +
            "of the separate ones; if it does not, the two blinders now interact and the " +
            "additive k-sum model of this freedom is stale")
            .to.equal(mod(mod(y.cv - y.base) + mod(y.dep - y.base)).toString());
    });
});
