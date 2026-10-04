// A transact prover cannot attest to a transaction the contract did not
// validate: `z` is derived from calldata that differs from the honest witness,
// and the circuit's public outputs must not match the contract's.
//
// Covers the 13 coefficients and the digest word; challenge-only words are not
// signals of `4x6.circom`, so no witness copy exists to diverge. Each
// coefficient case runs twice: with the calldata digest word left at the honest
// witness's value, where the digest output matches and `y` must differ, and
// with it recomputed for the rewritten coefficients, where the digest output
// differs.

import { flatten, transactDigest, type TransactWitnessBundle } from "../helpers";
import { assertViewsDiverge, expectNotForgeable, expectWitnessPublic } from "../lib/expect";
import { incremented as bump } from "../lib/signal_path";
import { ALICE_NSK, TIMEOUT_CIRCUIT } from "../lib/constants";
import { bindFiatShamir, calldataPublic, calldataView } from "../lib/transact";
import { useTransactCircuit } from "./setup";

describe("transact_4x6 / divergent witness", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    // Built once; no case modifies it.
    let honest: TransactWitnessBundle;

    before(() => {
        honest = ctx.tx.balanced(ALICE_NSK);
    });

    interface Case {
        /** The coefficient, as it reads in the circom. */
        field: string;
        /** Rewrite the calldata view; the witness is left honest. */
        diverge: (c: TransactWitnessBundle) => void;
    }

    // One per coefficient block. A field that is a signal but not in `coeffs`
    // fails here.
    const CASES: Case[] = [
        { field: "merkle_root", diverge: c => { c.merkle_root = bump(c.merkle_root); } },
        { field: "nullifier", diverge: c => { c.nullifier[0] = bump(c.nullifier[0]); } },
        { field: "nullifier (last slot)", diverge: c => { c.nullifier[3] = bump(c.nullifier[3]); } },
        { field: "out_cm", diverge: c => { c.out_cm[0] = bump(c.out_cm[0]); } },
        { field: "out_cm (last slot)", diverge: c => { c.out_cm[5] = bump(c.out_cm[5]); } },
        { field: "public_asset_id", diverge: c => { c.public_asset_id = "42"; } },
        { field: "public_out", diverge: c => { c.public_out = "7"; } },
    ];

    const DIGESTS = [
        { label: "digest left at the witness's", fix: (_c: TransactWitnessBundle) => {} },
        {
            label: "digest recomputed for the calldata",
            fix: (c: TransactWitnessBundle) => { c.digest = transactDigest(c).toString(); },
        },
    ];

    for (const { field, diverge } of CASES) {
        for (const { label, fix } of DIGESTS) {
            it(`${field} declared differently in calldata cannot be forged (${label})`, async () => {
                const w = calldataView(honest);
                const calldata = calldataView(honest);
                diverge(calldata);
                fix(calldata);

                assertViewsDiverge(flatten(w), flatten(calldata), field);

                bindFiatShamir(w, calldata);

                await expectNotForgeable(ctx.circuit, w, calldataPublic(calldata, BigInt(w.z)), field);
            });
        }
    }

    it("a digest declared differently in calldata cannot be forged", async () => {
        // Every coefficient agrees, so `y` agrees: only the digest public signal
        // separates the proof from this calldata.
        const w = calldataView(honest);
        const calldata = calldataView(honest);
        calldata.digest = bump(calldata.digest);

        assertViewsDiverge(flatten(w), flatten(calldata), "digest");

        bindFiatShamir(w, calldata);

        await expectNotForgeable(ctx.circuit, w, calldataPublic(calldata, BigInt(w.z)), "digest");
    });

    it("a fully honest witness matches its own calldata", async () => {
        // Harness guard: every divergence above perturbs this case.
        const w = calldataView(honest);
        bindFiatShamir(w, calldataView(w));
        await expectWitnessPublic(ctx.circuit, w, calldataPublic(w));
    });
});
