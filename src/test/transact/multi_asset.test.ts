// Per-asset conservation (Sapling-style).
//
// Balance is checked as an Edwards point sum, so each asset has its own
// generator V^asset = Pedersen(TAG_ASSET || asset_id_bits) and conservation
// holds per asset rather than over scalar totals.

import { expect } from "chai";

import { expectAccepts, expectWitnessFails } from "../lib/expect";
import { ALICE_NSK, BOB_NSK, TIMEOUT_CIRCUIT } from "../lib/constants";
import { DEFAULT_ASSET as ASSET } from "../lib/transact";
import { ASSET_B, useTransactCircuit } from "./setup";

describe("transact_4x6 / multi-asset", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    /** Two inputs of different assets, inserted and finalized against one root. */
    function mixedInputs(valueA: bigint, valueB: bigint) {
        const { tx } = ctx;
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(valueA, ALICE_NSK, 1n, ASSET), ALICE_NSK);
        let inB = tx.insert(tree, tx.note(valueB, ALICE_NSK, 2n, ASSET_B), ALICE_NSK);
        const root = tree.root();
        return { root, inputs: [tx.finalize(tree, inA), tx.finalize(tree, inB)] };
    }

    it("balanced: in=[A,B], out=[A,B] per-asset balance holds", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = mixedInputs(100n, 50n);
        await expectAccepts(circuit, tx.build({
            inputs,
            outputs: [tx.note(100n, BOB_NSK, 100n, ASSET), tx.note(50n, ALICE_NSK, 200n, ASSET_B)],
            merkleRoot: root,
        }));
    });

    it("two assets conserved independently", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = mixedInputs(100n, 50n);
        await expectAccepts(circuit, tx.build({
            inputs,
            outputs: [tx.note(100n, ALICE_NSK, 9n, ASSET), tx.note(50n, ALICE_NSK, 11n, ASSET_B)],
            merkleRoot: root,
        }));
    });

    it("FAILS on per-asset imbalance even when scalar totals match", async () => {
        // in: A=80, B=120. out: A=120, B=80. Both total 200; neither asset
        // conserves.
        const { tx, circuit } = ctx;
        const { root, inputs } = mixedInputs(80n, 120n);
        await expectWitnessFails(circuit, tx.build({
            inputs,
            outputs: [tx.note(120n, ALICE_NSK, 9n, ASSET), tx.note(80n, ALICE_NSK, 11n, ASSET_B)],
            merkleRoot: root,
        }), "scalar totals matching must not satisfy the per-asset point balance");
    });

    it("FAILS when an output asset is swapped for one of equal total value", async () => {
        // Straight substitution: same numbers, wrong colour.
        const { tx, circuit } = ctx;
        const { root, inputs } = ctx.tx.twoRealInputs([100n, 50n], ALICE_NSK);
        await expectWitnessFails(circuit, tx.build({
            inputs,
            outputs: [tx.note(150n, ALICE_NSK, 9n, ASSET_B), tx.note(0n, ALICE_NSK, 11n, ASSET)],
            merkleRoot: root,
        }), "an output asset swap must not balance");
    });

    // ===== F2: cross-asset cancellation via the asset-generator DL =====
    //
    // HashToAssetGen is circomlib Pedersen over 72 bits, so it is a single
    // segment and V^a = m(a)·BASE[0] for a publicly computable m(·). m is affine
    // in the low nibbles of asset_id, so m(1) + m(3) == 2·m(2) exactly, and the
    // Edwards point balance is satisfied by spending X of asset 1 plus X of
    // asset 3 to mint 2X of asset 2. PerAssetValueBalance rejects it by
    // comparing assets as field elements rather than as points.
    it("FAILS on cross-asset cancellation V^1 + V^3 == 2·V^2", async () => {
        const { tx, circuit } = ctx;
        const X = 1000n;
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(X, ALICE_NSK, 1n, 1n), ALICE_NSK);
        let inB = tx.insert(tree, tx.note(X, ALICE_NSK, 2n, 3n), ALICE_NSK);
        const root = tree.root();
        inA = tx.finalize(tree, inA);
        inB = tx.finalize(tree, inB);

        // Confirms the point balance is satisfied by the forgery, so the
        // rejection below is attributable to the per-asset check rather than to
        // a malformed witness.
        const J = tx.J;
        const lhs = J.addPoint(
            J.mulPointEscalar(J.hashToAssetGen(1n), X),
            J.mulPointEscalar(J.hashToAssetGen(3n), X),
        );
        const rhs = J.mulPointEscalar(J.hashToAssetGen(2n), 2n * X);
        expect(lhs[0]).to.equal(rhs[0]);
        expect(lhs[1]).to.equal(rhs[1]);

        await expectWitnessFails(circuit, tx.build({
            inputs: [inA, inB],
            outputs: [tx.note(2n * X, ALICE_NSK, 9n, 2n), tx.note(0n, ALICE_NSK, 11n, 2n)],
            merkleRoot: root,
        }), "PerAssetValueBalance must reject a point-balanced cross-asset forgery");
    });
});
