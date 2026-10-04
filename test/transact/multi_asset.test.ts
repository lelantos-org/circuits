// Per-asset conservation.
//
// PerAssetValueBalance compares asset ids as field elements and sums values per
// id, so conservation holds per asset rather than over scalar totals, and an
// asset can only cancel against itself.

import { expectAccepts, expectWitnessFails } from "../lib/expect";
import { ALICE_NSK, BOB_NSK, TIMEOUT_CIRCUIT } from "../lib/constants";
import {
    DEFAULT_ASSET as ASSET,
    MULTI_ASSET_IN,
    MULTI_ASSET_OUT,
} from "../lib/transact";
import type { Field, Note, TransactWitnessBundle } from "../helpers";
import { ASSET_B, useTransactCircuit } from "./setup";

describe("transact_4x6 / multi-asset", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    /** Two inputs of different assets, inserted and finalized against one root. */
    function mixedInputs(valueA: bigint, valueB: bigint) {
        const { tx } = ctx;
        return tx.plant([tx.note(valueA, ALICE_NSK, 1n, ASSET), tx.note(valueB, ALICE_NSK, 2n, ASSET_B)], ALICE_NSK);
    }

    it("balanced: in=[A,B], out=[A,B] per-asset balance holds", async () => {
        const { tx, circuit } = ctx;
        await expectAccepts(circuit, tx.spend(
            mixedInputs(100n, 50n),
            [tx.note(100n, BOB_NSK, 100n, ASSET), tx.note(50n, ALICE_NSK, 200n, ASSET_B)],
        ));
    });

    it("two assets conserved independently", async () => {
        const { tx, circuit } = ctx;
        await expectAccepts(circuit, tx.spend(
            mixedInputs(100n, 50n),
            [tx.note(100n, ALICE_NSK, 9n, ASSET), tx.note(50n, ALICE_NSK, 11n, ASSET_B)],
        ));
    });

    it("FAILS on per-asset imbalance even when scalar totals match", async () => {
        // in: A=80, B=120. out: A=120, B=80. Both total 200; neither asset
        // conserves.
        const { tx, circuit } = ctx;
        await expectWitnessFails(circuit, tx.spend(
            mixedInputs(80n, 120n),
            [tx.note(120n, ALICE_NSK, 9n, ASSET), tx.note(80n, ALICE_NSK, 11n, ASSET_B)],
        ), "scalar totals matching must not satisfy per-asset conservation");
    });

    it("FAILS when an output asset is swapped for one of equal total value", async () => {
        // Same values, different asset ids.
        const { tx, circuit } = ctx;
        await expectWitnessFails(circuit, tx.spend(
            tx.twoRealInputs([100n, 50n], ALICE_NSK),
            [tx.note(150n, ALICE_NSK, 9n, ASSET_B), tx.note(0n, ALICE_NSK, 11n, ASSET)],
        ), "an output asset swap must not balance");
    });

    // ===== cross-asset combination =====
    //
    // X of asset 1 plus X of asset 3 against 2X of asset 2. Under the Pedersen
    // value commitments this circuit used to carry, the three generators were
    // known multiples of one base with m(1) + m(3) == 2·m(2), so a point-sum
    // balance accepted it. Asset ids are compared as field elements here, so no
    // linear relation between ids balances anything; kept as the regression for
    // that class.
    it("FAILS on a cross-asset combination: X of 1 and X of 3 for 2X of 2", async () => {
        const { tx, circuit } = ctx;
        const X = 1000n;
        const spent = tx.plant([tx.note(X, ALICE_NSK, 1n, 1n), tx.note(X, ALICE_NSK, 2n, 3n)], ALICE_NSK);

        await expectWitnessFails(circuit, tx.spend(
            spent,
            [tx.note(2n * X, ALICE_NSK, 9n, 2n), tx.note(0n, ALICE_NSK, 11n, 2n)],
        ), "PerAssetValueBalance must reject value moving between asset ids");
    });

    // ===== every slot a different asset =====
    //
    // The cases above reach two assets in two slots each, so ten of the eleven
    // candidate rows `PerAssetValueBalance` evaluates carry the same asset and
    // a row that is skipped or mis-indexed still balances. `fullShapeMultiAsset`
    // fills all four input and all six output slots with four assets and no
    // zero values; `test/gadgets/balance.test.ts` sweeps the gadget itself.
    describe("full shape, four assets", () => {
        /** `fullShapeMultiAsset` with the two tables edited. */
        function shaped(
            inTable: readonly (readonly [Field, bigint])[],
            outTable: readonly (readonly [Field, bigint])[],
            extra: Parameters<typeof ctx.tx.spend>[2] = {},
        ): TransactWitnessBundle {
            const { tx } = ctx;
            const inputs: Note[] = inTable.map(([asset, value], i) =>
                tx.note(value, ALICE_NSK, BigInt(i + 1) * 1_000n, asset));
            const outputs: Note[] = outTable.map(([asset, value], j) =>
                tx.note(value, ALICE_NSK, 1_000_000n + BigInt(j) * 1_000n, asset));
            return tx.spend(tx.plant(inputs, ALICE_NSK), outputs, extra);
        }

        it("accepts four assets spread across every input and output slot", async () => {
            await expectAccepts(ctx.circuit, ctx.tx.fullShapeMultiAsset());
        });

        it("FAILS when one unit moves between two different-asset outputs", async () => {
            // asset 103: 30 in, 29 out. asset 104: 20 in, 21 out. The scalar
            // total is unchanged, so only the per-asset rows reject this.
            const outputs = MULTI_ASSET_OUT.map(([asset, value]) =>
                asset === 103n ? [asset, value - 1n] as const :
                asset === 104n && value === 15n ? [asset, value + 1n] as const :
                [asset, value] as const);
            await expectWitnessFails(
                ctx.circuit,
                shaped(MULTI_ASSET_IN, outputs),
                "moving value between two assets must be rejected by their candidate rows",
            );
        });

        it("FAILS when an input note is relabelled to an unheld asset", async () => {
            // The note is built, committed and inserted under asset 105, so the
            // commitment and Merkle path are honest: only conservation breaks.
            // Asset 104 loses its 20 units of input and 105 gains an input with
            // no output.
            const inputs = MULTI_ASSET_IN.map(([asset, value]) =>
                asset === 104n ? [105n, value] as const : [asset, value] as const);
            await expectWitnessFails(
                ctx.circuit,
                shaped(inputs, MULTI_ASSET_OUT),
                "a relabelled input must not fund the asset it no longer declares",
            );
        });

        it("FAILS when two assets are exchanged one for the other", async () => {
            // Outputs swap the labels of assets 102 (50) and 103 (30) while
            // keeping their values, so both rows are off by 20 in opposite
            // directions and the scalar total is untouched.
            const outputs = MULTI_ASSET_OUT.map(([asset, value]) =>
                asset === 102n ? [103n, value] as const :
                asset === 103n ? [102n, value] as const :
                [asset, value] as const);
            await expectWitnessFails(
                ctx.circuit,
                shaped(MULTI_ASSET_IN, outputs),
                "swapping two output asset labels must not balance",
            );
        });

        it("accepts a withdrawal from one of the four assets", async () => {
            // The public candidate row is no longer the orphan 0 == 0: it
            // carries asset 101, whose outputs give up the 5 withdrawn.
            const outputs = MULTI_ASSET_OUT.map(([asset, value], j) =>
                j === 0 ? [asset, value - 5n] as const : [asset, value] as const);
            await expectAccepts(ctx.circuit, shaped(MULTI_ASSET_IN, outputs, {
                publicAssetId: 101n,
                publicOut: 5n,
            }));
        });

        it("FAILS when a withdrawal is claimed but no output gives it up", async () => {
            await expectWitnessFails(
                ctx.circuit,
                shaped(MULTI_ASSET_IN, MULTI_ASSET_OUT, { publicAssetId: 101n, publicOut: 5n }),
                "public_out must come out of the outputs of the public asset",
            );
        });

        it("FAILS when a withdrawal is funded by a different asset's outputs", async () => {
            // 5 leaves asset 102's outputs while the bucket names 101.
            const outputs = MULTI_ASSET_OUT.map(([asset, value]) =>
                asset === 102n ? [asset, value - 5n] as const : [asset, value] as const);
            await expectWitnessFails(
                ctx.circuit,
                shaped(MULTI_ASSET_IN, outputs, { publicAssetId: 101n, publicOut: 5n }),
                "the public bucket must balance against its own asset",
            );
        });

        it("FAILS on a withdrawal of an asset the transaction does not hold", async () => {
            // Asset 7 appears in no note, so its candidate row reads
            // 0 == public_out.
            await expectWitnessFails(
                ctx.circuit,
                shaped(MULTI_ASSET_IN, MULTI_ASSET_OUT, { publicAssetId: ASSET, publicOut: 1n }),
                "an orphan public asset cannot fund a withdrawal",
            );
        });
    });
});
