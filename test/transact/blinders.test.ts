// Value-commitment blinders: free to choose, and no longer separable.
//
// `PolyEval`'s binding argument is that every coefficient is pinned by a
// constraint elsewhere in the circuit (src/README.md § 2a). For the value
// commitments that was discharged with "the value commitments by ValueCommit" —
// but `ValueCommitPair` pins `cv` only RELATIVE to a prover-chosen blinder:
//
//     cv     = value·V^asset + rcv·H
//     cv_dep = value·V^asset + rcv_dep·H
//
// and `PerAssetPointBalance` (src/lib/balance.circom) checks
//
//     Sum(in_cv) + Sum(out_rH) == Sum(out_cv) + Sum(in_rH)
//
// in which every blinder appears on both sides and cancels identically. So each
// `rcv` appeared in no constraint outside the one or two coefficients it
// produces, and `rcv_dep` was looser still — it does not even enter the point
// balance, and `ValueCommitPair.rH_dep` is read by nobody.
//
// That was a free dial on `y` at a FIXED challenge, and unlike the public-scalar
// residue in `binding.test.ts` it survived the challenge: `z` is derived from
// calldata the prover authored, and the witness `cv` need not equal the calldata
// `cv`. Worse, the dials COMPOSED — `PolyEval` is affine in each coefficient
// with slope z^k, and each blinder moved a disjoint pair of coefficients, so the
// displacements added exactly:
//
//     (y_both − y_base) ≡ (y_cv − y_base) + (y_dep − y_base)   (mod r)
//
// which made forging `y` a modular k-sum over ~22 knobs rather than a 254-bit
// search. This file asserts that identity, as a machine-checked record of the
// hole.
//
// This file does NOT settle the cost of that k-sum — the audit that raised it
// left the work factor unresolved, and a k-tree at k=16 needs 2^51 in memory as
// well as time, which ~22 knobs do not obviously supply. What it does is turn
// the STRUCTURAL claim into a regression test: the blinders are free, and their
// contributions to `y` are additively separable, so the knobs compose.
//
// TWO FIXES WERE TRIED AND REJECTED, both recorded here so they are not retried
// blind:
//
//   * Hashing the blinders into `cm`, so each also moves a Poseidon output.
//     Cheap (+2.3k constraints) and it does make each knob's contribution
//     non-linear — but separability is a property ACROSS knobs, and displacements
//     from distinct knobs still add. The knob count is unchanged, so the k-sum is
//     unaffected. The last test below is what caught this.
//   * Deriving the blinders from the note opening, `rcv = Poseidon(rcm, rho)`.
//     This does remove them as independent degrees of freedom, at ~15k
//     constraints once the output is reduced to RCV_BITS alias-free. But `rcv` is
//     the sender's fresh per-spend blinder: deriving it from the note makes
//     `in_cv` at spend time a deterministic function of the note, and deriving
//     `out_rcv` the same way makes it equal the creating transaction's value —
//     a direct link between creation and spend. It is a privacy design decision,
//     not a constraint-level fix.
//
// So the residue stands. Measure the k-sum cost before choosing between them.

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
     * Every variant below is built through here, so the four differ in the
     * blinders and in nothing else — same notes, same values, same nullifiers,
     * same tree, same `z`.
     */
    function witnessWith(
        tx: TxBuilder,
        z: Field,
        override: Partial<Pick<Note, "rcv" | "rcvDep">>,
    ): TransactWitnessBundle {
        const { root, inputs } = tx.twoRealInputs([100n, 50n], ALICE_NSK);
        const out0 = { ...tx.note(75n, ALICE_NSK, 9n), ...override };
        return tx.build({
            inputs,
            outputs: [out0, tx.note(75n, ALICE_NSK, 11n)],
            merkleRoot: root,
            z,
        });
    }

    /** The circuit's own `y` for a witness, not the reference evaluation. */
    async function circuitY(bundle: TransactWitnessBundle): Promise<bigint> {
        const { circuit } = ctx;
        return readOutput(await expectAccepts(circuit, bundle));
    }

    // The challenge every variant is evaluated at. Fixed across the four, which
    // is the whole point: a knob that only moves `y` by also moving `z` is bound
    // (the contract recomputes `z`), and a knob that moves `y` at a FIXED `z` is
    // not.
    const Z: Field = 0xdeadbeefcafef00dn;

    // Chosen well inside RCV_BITS = 252 so Num2Bits is not the thing under test.
    const RCV_ALT: Field = 0x1234_5678_9abc_def0n;
    const RCV_DEP_ALT: Field = 0x0fed_cba9_8765_4321n;

    // The four witnesses, generated once. They differ in the blinders and in
    // nothing else — same notes, values, nullifiers, tree and `z` — so every
    // claim below is a comparison between cached `y` values rather than another
    // pass over 100k constraints.
    let y: Record<"base" | "cv" | "dep" | "both", bigint>;

    before(async () => {
        // Sequential, deliberately. `witnessWith` goes through `TxBuilder`, which
        // is stateful — `newTree` plus inserts — so building these concurrently
        // interleaves its internals and the four bundles stop differing only in
        // their blinders, which is the one property every assertion here rests
        // on. The four witness generations are the cost of that.
        const at = (o: Partial<Pick<Note, "rcv" | "rcvDep">>) =>
            circuitY(witnessWith(ctx.tx, Z, o));
        const base = await at({});
        const cv = await at({ rcv: RCV_ALT });
        const dep = await at({ rcvDep: RCV_DEP_ALT });
        const both = await at({ rcv: RCV_ALT, rcvDep: RCV_DEP_ALT });
        y = { base, cv, dep, both };
    });

    // That the four were generated at all is the premise everything rests on:
    // the blinders really are free. `PerAssetPointBalance` cancels `rcv` on both
    // sides so conservation is untouched, and `rcv_dep` does not even enter it —
    // its only reader is the `out_cv_dep` coefficient. A constrained blinder
    // would fail witness generation in `before` rather than here.

    it("out_rcv moves y at a fixed challenge", () => {
        expect(y.cv, "if the blinder could not move y it would be pinned, and the " +
            "coefficient argument in src/README.md § 2a would hold for it")
            .to.not.equal(y.base);
    });

    it("out_rcv_dep moves y at a fixed challenge", () => {
        expect(y.dep).to.not.equal(y.base);
    });

    it("the two blinders' contributions to y are additively separable", () => {
        // The property that makes the knobs COMPOSE, and therefore the one that
        // decides whether forging `y` is a k-sum or a search. `PolyEval` is
        // affine in each coefficient with slope z^k, and each blinder moves a
        // disjoint set of coefficients, so moving both displaces `y` by exactly
        // the sum of the two individual displacements:
        //
        //     (y_both - y_base) == (y_cv - y_base) + (y_dep - y_base)   (mod r)
        //
        // An exact equality, not an approximation. It is what a fix has to
        // break, and it is the check that rejected hashing the blinders into
        // `cm`: that makes each knob's contribution non-linear but leaves the
        // knobs independent, so this identity still held and nothing was gained.
        //
        // The two tests above are its vacuity guards: at zero displacement this
        // reads 0 == 0 + 0 and says nothing.
        expect(mod(y.both - y.base).toString(), "the joint displacement must equal the sum " +
            "of the separate ones; if it does not, the two blinders now interact and the " +
            "additive k-sum model of this freedom is stale")
            .to.equal(mod(mod(y.cv - y.base) + mod(y.dep - y.base)).toString());
    });
});
