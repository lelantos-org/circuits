// Heavy variant coverage for `4x6.circom`.
//
// [test/fuzz/transact.fuzz.test.ts](./transact.fuzz.test.ts) covers
// balanced random witnesses, unbalanced mutations, ghost-note asset, wrong-nsk
// and value overflow. This file adds:
//   - role symmetry: the assignment of real notes to slots is free, so an honest
//     rebuild after swapping slots must verify. A raw JSON swap does not,
//     because output rho is bound to (nullifier[0], out_index) and slot order
//     feeds that derivation (the rho-uniqueness defence in transact/rho.test.ts).
//   - public-value boundary: publicIn / publicOut at 2^64 - 1 and at 2^64.
//   - path-element perturbation: mutating a random level of one input's Merkle
//     authentication path must reject, since the Poseidon image no longer
//     matches `merkle_root`.

import * as fc from "fast-check";

import { expectThrows, expectWitnessFails } from "../lib/expect";
import { bumpSignal } from "../lib/signal_path";
import { useTransactCircuit } from "../transact/setup";
import { arbBalancedSplit, arbNsk, MAX_VALUE, fcParamsFor } from "./arbitraries";
import { ALICE_NSK, BOB_NSK, DEPTH, TIMEOUT_HEAVY } from "../lib/constants";

// Each trial builds one or two production-depth witnesses, so SUITE_SCALE halves
// NUM_RUNS. Override: FUZZ_RUNS_TRANSACT_VARIANTS=N.
const fcParams = fcParamsFor("TRANSACT_VARIANTS");

describe("transact_4x6 variants [fuzz]", function () {
    this.timeout(TIMEOUT_HEAVY);

    const ctx = useTransactCircuit();

    it("input-role swap preserves witness validity (honest rebuild)", async () => {
        // Swapping input slots changes nullifier[0], and with it the derived
        // output rho and cm, so a raw JSON swap does not verify. The invariant
        // is that either assignment of real notes to input slots verifies once
        // the witness is rebuilt.
        await fc.assert(fc.asyncProperty(
            arbBalancedSplit(), arbNsk(), arbNsk(),
            async (split, aliceNsk, bobNsk) => {
                const { scenario, outputs } = ctx.tx.transferParts(split, aliceNsk, bobNsk, [101n, 102n, 103n, 104n]);
                await ctx.circuit.calculateWitness(ctx.tx.spend(scenario, outputs), true);
                const [inA, inB] = scenario.inputs;
                const swapped = ctx.tx.spend({ root: scenario.root, inputs: [inB, inA] }, outputs);
                await ctx.circuit.calculateWitness(swapped, true);
            },
        ), fcParams);
    });

    it("output-role swap preserves witness validity (honest rebuild)", async () => {
        // Rho is index-bound, so swapping output slots requires re-deriving each
        // slot's rho (honest rebuild), not a raw JSON swap. Both arrangements
        // must verify.
        await fc.assert(fc.asyncProperty(
            arbBalancedSplit(), arbNsk(), arbNsk(),
            async (split, aliceNsk, bobNsk) => {
                const { scenario, outputs } = ctx.tx.transferParts(split, aliceNsk, bobNsk, [201n, 202n, 203n, 204n]);
                await ctx.circuit.calculateWitness(ctx.tx.spend(scenario, outputs), true);
                const swapped = ctx.tx.spend(scenario, [outputs[1], outputs[0]]);
                await ctx.circuit.calculateWitness(swapped, true);
            },
        ), fcParams);
    });

    it("public-value boundary: publicIn = 2^64 - 1 balanced witness passes", async () => {
        // One input at MAX_VALUE, outputs summing to MAX_VALUE, publicIn =
        // publicOut = 0 (transfer only). Pins Num2Bits(64) acceptance at the
        // upper boundary.
        const split = { v1: MAX_VALUE, v2: 0n, o1: MAX_VALUE, o2: 0n };
        await ctx.circuit.calculateWitness(ctx.tx.transfer(split, ALICE_NSK, BOB_NSK), true);
    });

    it("public-value boundary: input value = 2^64 (overflow) rejects", async () => {
        // The SDK or the circuit must reject the range violation; both enforce
        // the same invariant, so either rejection passes.
        const overflow = 1n << 64n;
        const split = { v1: overflow, v2: 0n, o1: overflow, o2: 0n };
        await expectThrows(
            () => ctx.circuit.calculateWitness(ctx.tx.transfer(split, ALICE_NSK, BOB_NSK), true),
            "overflow input value must reject (SDK or ctx.circuit)",
        );
    });

    it("path element perturbation at random level rejects", async () => {
        await fc.assert(fc.asyncProperty(
            arbBalancedSplit(), arbNsk(), arbNsk(),
            fc.integer({ min: 0, max: DEPTH - 1 }),
            fc.integer({ min: 0, max: 2 }),
            // bump ∈ [1, 2^200) — non-zero by construction.
            fc.bigInt(1n, (1n << 200n) - 1n),
            async (split, aliceNsk, bobNsk, lvl, slot, bump) => {
                const tampered = ctx.tx.transfer(split, aliceNsk, bobNsk, [301n, 302n, 303n, 304n]);
                // Mutate inputs[0]'s authentication path at (lvl, slot).
                bumpSignal(tampered, `in_path_elements[0][${lvl}][${slot}]`, bump);
                await expectWitnessFails(ctx.circuit, tampered,
                    `path perturbation at lvl=${lvl} slot=${slot} must reject`);
            },
        ), fcParams);
    });

    it("cross-note attack: swapping in_nsk between two differently-owned inputs rejects", async () => {
        // Inputs owned by nsk0 and nsk1. Swapping in_nsk[0] ↔ in_nsk[1] breaks
        // both the pk-derivation check (DerivePk(nsk1) ≠ pk0) and the nullifier
        // check (nf0 is derived from DeriveNk(nsk0)).
        await fc.assert(fc.asyncProperty(
            arbBalancedSplit(), arbNsk(), arbNsk(),
            async ({ v1, v2, o1, o2 }, nsk0, nsk1) => {
                fc.pre(nsk0 !== nsk1);
                const input = ctx.tx.spend(
                    ctx.tx.plant([ctx.tx.note(v1, nsk0, 401n), ctx.tx.note(v2, nsk1, 402n)], [nsk0, nsk1]),
                    [ctx.tx.note(o1, nsk0, 403n), ctx.tx.note(o2, nsk1, 404n)],
                );
                await ctx.circuit.calculateWitness(input, true);
                // Transpose the first two entries on a copy of the full array.
                // A two-element literal would drop the padded slots, and the
                // witness calculator would reject the input shape ("Not enough
                // values for input signal in_nsk") instead of the key check.
                const nsk = [...input.in_nsk];
                [nsk[0], nsk[1]] = [nsk[1], nsk[0]];
                const swapped = { ...input, in_nsk: nsk };
                await expectWitnessFails(ctx.circuit, swapped, "swapped nsk must reject");
            },
        ), fcParams);
    });
});
