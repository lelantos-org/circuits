import * as fc from "fast-check";

import { MerkleTree, SpentNote, Note, Field, commit } from "../helpers";
import { loadCircuit, srcPath } from "../lib/circuit";
import { buildTxBuilder, TxBuilder, DEFAULT_ASSET as ASSET } from "../lib/transact";
import { expectWitnessFails } from "../lib/expect";
import {
    arbBalancedSplit, arbNsk, arbField, MAX_VALUE,
    fcParamsFor, arbDistinctBigInt,
} from "./arbitraries";

const DEPTH = 10;
const CIRCUIT = srcPath("2x2.circom");
const fcParams = fcParamsFor("TRANSACT");

// Pin balanced-split edge cases worth seeding into every fc.assert.
// Note: MAX_VALUE = 2^64 - 1 is odd, so 2 * (MAX_VALUE / 2n) = MAX_VALUE - 1.
// Each tuple must satisfy o1 + o2 === v1 + v2 (circuit rejects otherwise).
const BALANCED_EXAMPLES = [
    { v1: 0n, v2: 0n, o1: 0n, o2: 0n },
    { v1: MAX_VALUE / 2n, v2: MAX_VALUE / 2n, o1: MAX_VALUE - 1n, o2: 0n },
    { v1: MAX_VALUE / 2n, v2: MAX_VALUE / 2n, o1: 0n, o2: MAX_VALUE - 1n },
];

describe("transact_2x2 [fuzz]", function () {
    this.timeout(900000);

    let circuit: any;
    let tx: TxBuilder;

    before(async () => {
        tx = await buildTxBuilder(DEPTH);
        circuit = await loadCircuit(CIRCUIT);
    });

    // Two real inputs from `aliceNsk`; two outputs (o1 to bob, o2 back to alice).
    async function runValid(
        v1: bigint, v2: bigint, o1: bigint, o2: bigint,
        aliceNsk: bigint, bobNsk: bigint,
        rhoA: bigint, rhoB: bigint, rhoOA: bigint, rhoOB: bigint,
    ): Promise<{ input: any; tree: MerkleTree; root: Field }> {
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(v1, aliceNsk, rhoA), aliceNsk);
        let inB = tx.insert(tree, tx.note(v2, aliceNsk, rhoB), aliceNsk);
        const root = tree.root();
        inA = tx.finalize(tree, inA);
        inB = tx.finalize(tree, inB);

        const outA = tx.note(o1, bobNsk, rhoOA);
        const outB = tx.note(o2, aliceNsk, rhoOB);

        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        return { input, tree, root };
    }

    it("balanced random 2-in-2-out same-asset always passes", async () => {
        await fc.assert(fc.asyncProperty(
            arbBalancedSplit(),
            arbNsk(), arbNsk(),
            // rhoA/rhoB always distinct via chained arbitrary (no .filter shrink penalty).
            arbDistinctBigInt(1n, 1n << 200n),
            arbField(1n << 200n), arbField(1n << 200n),
            async ({ v1, v2, o1, o2 }, aliceNsk, bobNsk, [rhoA, rhoB], rhoOA, rhoOB) => {
                const { input } = await runValid(v1, v2, o1, o2, aliceNsk, bobNsk, rhoA, rhoB, rhoOA, rhoOB);
                const w = await circuit.calculateWitness(input, true);
                await circuit.checkConstraints(w);
            },
        ), fcParamsFor("TRANSACT", { examples: BALANCED_EXAMPLES.map(s => [s, 11n, 22n, [1n, 2n] as [bigint, bigint], 3n, 4n]) }));
    });

    it("unbalanced random tx (output mutated by +delta) always fails", async () => {
        // Generate (v1, v2, o1, o2, delta) so that delta > 0 and o2+delta ∈
        // (o1+o2, MAX_VALUE]. Result is always unbalanced AND in range — no
        // silent post-hoc skips.
        const arbUnbalancedDelta = arbBalancedSplit().chain(({ v1, v2, o1, o2 }) => {
            const headroom = MAX_VALUE - o2;
            if (headroom === 0n) return fc.constant({ v1, v2, o1, o2, delta: 0n, skip: true });
            return fc.bigInt(1n, headroom).map(delta => ({ v1, v2, o1, o2, delta, skip: false }));
        });

        await fc.assert(fc.asyncProperty(
            arbUnbalancedDelta,
            arbNsk(), arbNsk(),
            async ({ v1, v2, o1, o2, delta, skip }, aliceNsk, bobNsk) => {
                if (skip) return; // o2 already saturated at MAX_VALUE; rare.
                const { input } = await runValid(
                    v1, v2, o1, o2 + delta, aliceNsk, bobNsk,
                    101n, 102n, 103n, 104n,
                );
                await expectWitnessFails(circuit, input, "expected unbalanced tx to fail");
            },
        ), fcParams);
    });

    it("wrong asset_id on an output (ghost note) always fails", async () => {
        // o1 ≥ 1 forces an observable asset mismatch (commit binds asset·2^64+value).
        // Built directly without .filter to keep shrinking efficient.
        const arbSplitO1Nonzero = fc.tuple(
            fc.bigInt(1n, MAX_VALUE / 2n - 1n),
            fc.bigInt(0n, MAX_VALUE / 2n),
            fc.bigInt(0n, 1n << 60n),
        ).map(([v1, v2, splitSeed]) => {
            const total = v1 + v2;
            const o1 = 1n + (splitSeed % total);
            return { v1, v2, o1, o2: total - o1 };
        });
        await fc.assert(fc.asyncProperty(
            arbSplitO1Nonzero,
            arbField(1n << 60n),
            async ({ v1, v2, o1, o2 }, badAssetSeed) => {
                const badAsset = ASSET + 1n + badAssetSeed;
                const aliceNsk = 11n, bobNsk = 22n;
                const tree = tx.newTree();
                let inA = tx.insert(tree, tx.note(v1, aliceNsk, 1n), aliceNsk);
                let inB = tx.insert(tree, tx.note(v2, aliceNsk, 2n), aliceNsk);
                const root = tree.root();
                inA = tx.finalize(tree, inA);
                inB = tx.finalize(tree, inB);

                const outA: Note = { ...tx.note(o1, bobNsk, 100n), asset: badAsset };
                const outB = tx.note(o2, aliceNsk, 200n);

                const input = tx.build({
                    publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
                    inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
                });
                await expectWitnessFails(circuit, input, "expected ghost-note tx to fail");
            },
        ), fcParams);
    });

    it("note commitment binds asset even at value=0", async () => {
        await fc.assert(fc.asyncProperty(
            // Distinct asset pair via chained arb; no post-hoc skip.
            arbDistinctBigInt(1n, 1n << 60n),
            arbField(1n << 200n), arbField(1n << 200n), arbField(1n << 200n),
            async ([assetA, assetB], pk, rho, rcm) => {
                const base = { value: 0n, pk, rho, rcm } as const;
                const cmA = commit(tx.P, { ...base, asset: assetA });
                const cmB = commit(tx.P, { ...base, asset: assetB });
                if (cmA === cmB) throw new Error("commitment collision across assets at value=0");
            },
        ), fcParams);
    });

    it("input value > 2^64 always fails (range check)", async () => {
        // Slow path — each run runs the SDK + circuit. Default to half via
        // FUZZ_RUNS_TRANSACT_OVERFLOW; capped lower if env unset.
        await fc.assert(fc.asyncProperty(
            fc.bigInt(1n, 1n << 200n),
            async (overflowSeed) => {
                const overflow = MAX_VALUE + 1n + (overflowSeed % (1n << 64n));
                // Either SDK validation or circuit range check must reject.
                let threw = false;
                try {
                    const nsk = 11n;
                    const tree = tx.newTree();
                    let inA = tx.insert(tree, tx.note(overflow, nsk, 1n), nsk);
                    let inB = tx.insert(tree, tx.note(0n, nsk, 2n), nsk);
                    const root = tree.root();
                    inA = tx.finalize(tree, inA);
                    inB = tx.finalize(tree, inB);
                    const outA = tx.note(overflow, nsk, 100n);
                    const outB = tx.note(0n, nsk, 200n);
                    const input = tx.build({
                        publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
                        inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
                    });
                    await circuit.calculateWitness(input, true);
                } catch { threw = true; }
                if (!threw) throw new Error("expected overflow value to fail (SDK or circuit)");
            },
        ), fcParamsFor("TRANSACT_OVERFLOW"));
    });

    it("wrong nsk (not the owner) always fails nullifier/key checks", async () => {
        await fc.assert(fc.asyncProperty(
            arbBalancedSplit(),
            // wrongNsk distinct from aliceNsk (hardcoded to 11n here).
            arbNsk().map(n => n === 11n ? n + 1n : n),
            async ({ v1, v2, o1, o2 }, wrongNsk) => {
                const aliceNsk = 11n, bobNsk = 22n;
                const tree = tx.newTree();
                let inA = tx.insert(tree, tx.note(v1, aliceNsk, 1n), aliceNsk);
                let inB = tx.insert(tree, tx.note(v2, aliceNsk, 2n), aliceNsk);
                const root = tree.root();
                inA = tx.finalize(tree, inA);
                inB = tx.finalize(tree, inB);
                const tamperedA: SpentNote = { ...inA, nsk: wrongNsk };
                const outA = tx.note(o1, bobNsk, 100n);
                const outB = tx.note(o2, aliceNsk, 200n);
                const input = tx.build({
                    publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
                    inputs: [tamperedA, inB], outputs: [outA, outB], merkleRoot: root,
                });
                await expectWitnessFails(circuit, input, "expected wrong-nsk tx to fail");
            },
        ), fcParams);
    });
});
