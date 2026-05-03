import * as fc from "fast-check";

import { MerkleTree, SpentNote, Note, Field, commit } from "../helpers";
import { loadCircuit, srcPath } from "../lib/circuit";
import { buildTxBuilder, TxBuilder, DEFAULT_ASSET as ASSET } from "../lib/transact";
import { expectWitnessFails } from "../lib/expect";
import { arbBalancedSplit, arbNsk, arbField, fcParams, MAX_VALUE } from "./arbitraries";

const DEPTH = 10;
const CIRCUIT = srcPath("2x2.circom");

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
            arbField(1n << 200n), arbField(1n << 200n), arbField(1n << 200n), arbField(1n << 200n),
            async ({ v1, v2, o1, o2 }, aliceNsk, bobNsk, rhoA, rhoBraw, rhoOA, rhoOB) => {
                const rhoB = rhoBraw === rhoA ? rhoBraw + 1n : rhoBraw;
                const { input } = await runValid(v1, v2, o1, o2, aliceNsk, bobNsk, rhoA, rhoB, rhoOA, rhoOB);
                const w = await circuit.calculateWitness(input, true);
                await circuit.checkConstraints(w);
            },
        ), fcParams);
    });

    it("unbalanced random tx (output mutated by +delta) always fails", async () => {
        await fc.assert(fc.asyncProperty(
            arbBalancedSplit(),
            arbNsk(), arbNsk(),
            fc.bigInt(1n, 1n << 32n),
            async ({ v1, v2, o1, o2 }, aliceNsk, bobNsk, delta) => {
                const total = v1 + v2;
                if (o2 + delta > MAX_VALUE) return;
                if (delta === 0n) return;
                const { input } = await runValid(
                    v1, v2, o1, o2 + delta, aliceNsk, bobNsk,
                    101n, 102n, 103n, 104n,
                );
                if (o1 + (o2 + delta) === total) return;
                await expectWitnessFails(circuit, input, "expected unbalanced tx to fail");
            },
        ), fcParams);
    });

    it("wrong asset_id on an output (ghost note) always fails", async () => {
        await fc.assert(fc.asyncProperty(
            arbBalancedSplit(),
            arbField(1n << 60n),
            async ({ v1, v2, o1, o2 }, badAssetSeed) => {
                if (o1 === 0n) return;
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
            arbField(1n << 60n), arbField(1n << 60n),
            arbField(1n << 200n), arbField(1n << 200n), arbField(1n << 200n),
            async (assetSeedA, assetSeedB, pk, rho, rcm) => {
                const assetA = 1n + assetSeedA;
                const assetB = 1n + assetSeedB;
                if (assetA === assetB) return;
                const base = { value: 0n, pk, rho, rcm } as const;
                const cmA = commit(tx.P, { ...base, asset: assetA });
                const cmB = commit(tx.P, { ...base, asset: assetB });
                if (cmA === cmB) throw new Error("commitment collision across assets at value=0");
            },
        ), fcParams);
    });

    it("input value > 2^64 always fails (range check)", async () => {
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
        ), { ...fcParams, numRuns: Math.min(fcParams.numRuns ?? 20, 10) });
    });

    it("wrong nsk (not the owner) always fails nullifier/key checks", async () => {
        await fc.assert(fc.asyncProperty(
            arbBalancedSplit(),
            arbNsk(),
            async ({ v1, v2, o1, o2 }, wrongNsk) => {
                const aliceNsk = 11n, bobNsk = 22n;
                const tree = tx.newTree();
                let inA = tx.insert(tree, tx.note(v1, aliceNsk, 1n), aliceNsk);
                let inB = tx.insert(tree, tx.note(v2, aliceNsk, 2n), aliceNsk);
                const root = tree.root();
                inA = tx.finalize(tree, inA);
                inB = tx.finalize(tree, inB);
                if (wrongNsk === aliceNsk) return;
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
