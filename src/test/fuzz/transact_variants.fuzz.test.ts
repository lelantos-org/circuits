// Heavy variant coverage for `2x2.circom`.
//
// Existing [src/test/fuzz/transact.fuzz.test.ts](./transact.fuzz.test.ts)
// covers balanced random witnesses, unbalanced mutations, ghost-note
// asset, wrong-nsk, and value-overflow. This file adds:
//   - role symmetry: swapping the two inputs (or the two outputs) must
//     still produce a verifying witness — the 2-in / 2-out circuit is
//     commutative in slot order, and any asymmetry would be a soundness
//     hole on the spender's side;
//   - public-value boundary: publicIn / publicOut at 2^64 - 1 (max) and
//     at exactly 2^64 (overflow);
//   - path-element perturbation: mutating a random level of one input's
//     Merkle authentication path must reject (Poseidon image disagrees
//     with `merkle_root`).
//
// SLOW: each property builds 1–2 depth-10 SNARK witnesses per fast-check
// trial. Run count halved vs the shared `fcParams` (mirrors
// `frontier_root_fuzz.test.ts` rationale).

import * as fc from "fast-check";

import { MerkleTree, Field, Note, SpentNote } from "../helpers";
import { loadCircuit, srcPath } from "../lib/circuit";
import { buildTxBuilder, TxBuilder, DEFAULT_ASSET as ASSET } from "../lib/transact";
import { expectWitnessFails } from "../lib/expect";
import { arbBalancedSplit, arbNsk, arbField, MAX_VALUE, fcParamsFor } from "./arbitraries";

const DEPTH = 10;
const CIRCUIT = srcPath("2x2.circom");
// `TRANSACT_VARIANTS` is slow (≥1 depth-10 witness per trial); SUITE_SCALE
// halves vs NUM_RUNS by default. Override: FUZZ_RUNS_TRANSACT_VARIANTS=N.
const fcParams = fcParamsFor("TRANSACT_VARIANTS");

// Construct an honest balanced 2-in-2-out witness (same asset, same
// owner-nsk for inputs). Returns the freshly-built circom input dict.
async function buildBalanced(
    tx: TxBuilder,
    v1: bigint, v2: bigint, o1: bigint, o2: bigint,
    aliceNsk: bigint, bobNsk: bigint,
    rhoA: bigint, rhoB: bigint, rhoOA: bigint, rhoOB: bigint,
): Promise<{ input: any; inputs: [SpentNote, SpentNote]; outputs: [Note, Note]; root: Field }> {
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
    return { input, inputs: [inA, inB], outputs: [outA, outB], root };
}

// Swap the two input slots inside a built circom-input dict. Touches every
// per-input array AND the public-input-bound `nullifier` / `in_cv` slots.
function swapInputs(input: any): any {
    const out = { ...input };
    const swap2 = <T>(arr: T[]): T[] => [arr[1], arr[0]];
    out.nullifier = swap2(input.nullifier);
    out.in_cv = swap2(input.in_cv);
    out.in_asset = swap2(input.in_asset);
    out.in_value = swap2(input.in_value);
    out.in_pk = swap2(input.in_pk);
    out.in_rho = swap2(input.in_rho);
    out.in_rcm = swap2(input.in_rcm);
    out.in_nsk = swap2(input.in_nsk);
    out.in_rcv = swap2(input.in_rcv);
    out.in_rcv_dep = swap2(input.in_rcv_dep);
    out.in_path_elements = swap2(input.in_path_elements);
    out.in_path_indices = swap2(input.in_path_indices);
    out.in_is_dummy = swap2(input.in_is_dummy);
    return out;
}

// Swap the two output slots — every per-output array.
function swapOutputs(input: any): any {
    const out = { ...input };
    const swap2 = <T>(arr: T[]): T[] => [arr[1], arr[0]];
    out.out_cm = swap2(input.out_cm);
    out.out_cv = swap2(input.out_cv);
    out.out_cv_dep = swap2(input.out_cv_dep);
    out.out_asset = swap2(input.out_asset);
    out.out_value = swap2(input.out_value);
    out.out_pk = swap2(input.out_pk);
    out.out_rho = swap2(input.out_rho);
    out.out_rcm = swap2(input.out_rcm);
    out.out_rcv = swap2(input.out_rcv);
    out.out_rcv_dep = swap2(input.out_rcv_dep);
    out.out_clue_bits = swap2(input.out_clue_bits);
    out.out_clue_Rx = swap2(input.out_clue_Rx);
    out.out_clue_Ry = swap2(input.out_clue_Ry);
    return out;
}

describe("transact_2x2 variants [fuzz]", function () {
    this.timeout(3_600_000);

    let circuit: any;
    let tx: TxBuilder;

    before(async () => {
        tx = await buildTxBuilder(DEPTH);
        circuit = await loadCircuit(CIRCUIT);
    });

    it("input-role swap preserves witness validity (slot commutativity)", async () => {
        await fc.assert(fc.asyncProperty(
            arbBalancedSplit(), arbNsk(), arbNsk(),
            async ({ v1, v2, o1, o2 }, aliceNsk, bobNsk) => {
                const { input } = await buildBalanced(
                    tx, v1, v2, o1, o2, aliceNsk, bobNsk,
                    101n, 102n, 103n, 104n,
                );
                // Original witness must pass.
                await circuit.calculateWitness(input, true);
                // Swapping the two input slots must also pass.
                const swapped = swapInputs(input);
                await circuit.calculateWitness(swapped, true);
            },
        ), fcParams);
    });

    it("output-role swap preserves witness validity", async () => {
        await fc.assert(fc.asyncProperty(
            arbBalancedSplit(), arbNsk(), arbNsk(),
            async ({ v1, v2, o1, o2 }, aliceNsk, bobNsk) => {
                const { input } = await buildBalanced(
                    tx, v1, v2, o1, o2, aliceNsk, bobNsk,
                    201n, 202n, 203n, 204n,
                );
                await circuit.calculateWitness(input, true);
                const swapped = swapOutputs(input);
                await circuit.calculateWitness(swapped, true);
            },
        ), fcParams);
    });

    it("public-value boundary: publicIn = 2^64 - 1 balanced witness passes", async () => {
        // One input full at MAX_VALUE; outputs sum to MAX_VALUE; publicIn=0,
        // publicOut=0 (transfer-only) ⇒ honest balanced witness. This pins
        // the Num2Bits(64) accepts at the upper boundary.
        const aliceNsk = 11n, bobNsk = 22n;
        const tree = tx.newTree();
        let inA = tx.insert(tree, tx.note(MAX_VALUE, aliceNsk, 1n), aliceNsk);
        let inB = tx.insert(tree, tx.note(0n, aliceNsk, 2n), aliceNsk);
        const root = tree.root();
        inA = tx.finalize(tree, inA);
        inB = tx.finalize(tree, inB);
        const outA = tx.note(MAX_VALUE, bobNsk, 100n);
        const outB = tx.note(0n, aliceNsk, 200n);
        const input = tx.build({
            publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
            inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
        });
        await circuit.calculateWitness(input, true);
    });

    it("public-value boundary: input value = 2^64 (overflow) rejects", async () => {
        // SDK or circuit must catch the range violation. Either layer's
        // rejection counts — both gates protect the same invariant.
        const aliceNsk = 11n, bobNsk = 22n;
        const overflow = 1n << 64n;
        let threw = false;
        try {
            const tree = tx.newTree();
            let inA = tx.insert(tree, tx.note(overflow, aliceNsk, 1n), aliceNsk);
            let inB = tx.insert(tree, tx.note(0n, aliceNsk, 2n), aliceNsk);
            const root = tree.root();
            inA = tx.finalize(tree, inA);
            inB = tx.finalize(tree, inB);
            const outA = tx.note(overflow, bobNsk, 100n);
            const outB = tx.note(0n, aliceNsk, 200n);
            const input = tx.build({
                publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
                inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
            });
            await circuit.calculateWitness(input, true);
        } catch { threw = true; }
        if (!threw) throw new Error("overflow input value must reject (SDK or circuit)");
    });

    it("path element perturbation at random level rejects", async () => {
        await fc.assert(fc.asyncProperty(
            arbBalancedSplit(), arbNsk(), arbNsk(),
            fc.integer({ min: 0, max: DEPTH - 1 }),
            fc.integer({ min: 0, max: 2 }),
            // bump ∈ [1, 2^200) — non-zero by construction.
            fc.bigInt(1n, (1n << 200n) - 1n),
            async ({ v1, v2, o1, o2 }, aliceNsk, bobNsk, lvl, slot, bump) => {
                const { input } = await buildBalanced(
                    tx, v1, v2, o1, o2, aliceNsk, bobNsk,
                    301n, 302n, 303n, 304n,
                );
                // Mutate inputs[0]'s authentication path at (lvl, slot).
                const paths = input.in_path_elements.map((arr: string[][]) =>
                    arr.map(level => [...level])
                );
                const orig = BigInt(paths[0][lvl][slot]);
                paths[0][lvl][slot] = (orig + bump).toString();
                const tampered = { ...input, in_path_elements: paths };
                await expectWitnessFails(circuit, tampered,
                    `path perturbation at lvl=${lvl} slot=${slot} must reject`);
            },
        ), fcParams);
    });

    it("cross-note attack: swapping in_nsk between two differently-owned inputs rejects", async () => {
        // Inputs owned by nsk0 and nsk1 respectively. Swapping in_nsk[0] ↔
        // in_nsk[1] breaks both the pk-derivation check (DerivePk(nsk1) ≠ pk0)
        // and the nullifier check (Poseidon(DeriveNk(nsk1), rho0) ≠ nf0).
        await fc.assert(fc.asyncProperty(
            arbBalancedSplit(), arbNsk(), arbNsk(),
            async ({ v1, v2, o1, o2 }, nsk0, nsk1) => {
                fc.pre(nsk0 !== nsk1);
                const tree = tx.newTree();
                let inA = tx.insert(tree, tx.note(v1, nsk0, 401n), nsk0);
                let inB = tx.insert(tree, tx.note(v2, nsk1, 402n), nsk1);
                const root = tree.root();
                inA = tx.finalize(tree, inA);
                inB = tx.finalize(tree, inB);
                const outA = tx.note(o1, nsk0, 403n);
                const outB = tx.note(o2, nsk1, 404n);
                const input = tx.build({
                    publicAssetId: ASSET, publicIn: 0n, publicOut: 0n,
                    inputs: [inA, inB], outputs: [outA, outB], merkleRoot: root,
                });
                await circuit.calculateWitness(input, true);
                const swapped = { ...input, in_nsk: [input.in_nsk[1], input.in_nsk[0]] };
                await expectWitnessFails(circuit, swapped, "swapped nsk must reject");
            },
        ), fcParams);
    });
});
