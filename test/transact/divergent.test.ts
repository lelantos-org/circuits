// Checks that a transact prover cannot attest to a transaction the contract did
// not validate.
//
// `test/tree_update_batch.test.ts :: divergent witness` covers the batch
// circuit. The other transact suites derive `z` from the same bundle they pass
// to the circuit (`rebindFiatShamir`), so witness and calldata are the same
// transaction by construction and a word the circuit never pins still appears
// bound.
//
// The attack shape is the one `blinders.test.ts` describes: `z` comes from
// prover-authored calldata and is read before the witness is chosen, so any
// witness satisfying the R1CS at that `z` produces a verifying proof. Soundness
// requires the circuit's `y` to differ from the contract's whenever the two
// descriptions differ.
//
// Transact's challenge-only words are out of scope: they are not signals of
// `4x6.circom`, so no witness copy exists to diverge. `binding.test.ts :: the
// challenge-only fields are not circuit signals` checks that against the
// compiled circuit, which justifies excluding them from `y`. This file covers
// the other 46 words, each of which is a signal.

import { flatten, type TransactWitnessBundle } from "../helpers";
import { assertViewsDiverge, expectNotForgeable, expectWitnessY } from "../lib/expect";
import { ALICE_NSK, TIMEOUT_CIRCUIT } from "../lib/constants";
import { bindFiatShamir, calldataView, calldataY } from "../lib/transact";
import { useTransactCircuit } from "./setup";

describe("transact_4x6 / divergent witness", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    // `TxBuilder.balanced()` is the shared honest base of the tamper suites; its
    // docblock guarantees it is "honest in every respect but the field under
    // test".
    //
    // Built once (`tx.build` takes ~260ms). Every case diverges a
    // `structuredClone` of it and `bindFiatShamir` writes only `w.z`, so no case
    // modifies the base.
    let honest: TransactWitnessBundle;

    before(() => {
        honest = ctx.tx.balanced(ALICE_NSK);
    });

    interface Case {
        /** The coefficient, as it reads in the circom. */
        field: string;
        /** Rewrite the CALLDATA view; the witness is left honest. */
        diverge: (c: TransactWitnessBundle) => void;
    }

    // One per coefficient block. Each is a circuit signal, so a witness copy
    // exists and can disagree, and each is evaluated into `y`, which exposes the
    // disagreement. A field that is a signal but not in `coeffs` fails here.
    const CASES: Case[] = [
        { field: "merkle_root", diverge: c => { c.merkle_root = bump(c.merkle_root); } },
        { field: "nullifier", diverge: c => { c.nullifier[0] = bump(c.nullifier[0]); } },
        { field: "out_cm", diverge: c => { c.out_cm[0] = bump(c.out_cm[0]); } },
        { field: "public_asset_id", diverge: c => { c.public_asset_id = "42"; } },
        { field: "public_in", diverge: c => { c.public_in = "7"; } },
        { field: "public_out", diverge: c => { c.public_out = "7"; } },
        { field: "in_cv", diverge: c => { c.in_cv[0][0] = bump(c.in_cv[0][0]); } },
        { field: "out_cv", diverge: c => { c.out_cv[0][0] = bump(c.out_cv[0][0]); } },
        { field: "out_cv_dep", diverge: c => { c.out_cv_dep[0][0] = bump(c.out_cv_dep[0][0]); } },
    ];

    function bump(v: string): string {
        return (BigInt(v) + 1n).toString();
    }

    for (const { field, diverge } of CASES) {
        it(`${field} declared differently in calldata cannot be forged`, async () => {
            const w = calldataView(honest);
            const calldata = calldataView(honest);
            diverge(calldata);

            assertViewsDiverge(flatten(w), flatten(calldata), field);

            bindFiatShamir(w, calldata);

            await expectNotForgeable(ctx.circuit, w, calldataY(calldata, BigInt(w.z)), field);
        });
    }

    it("a fully honest witness matches its own calldata", async () => {
        // Harness guard: every divergence above perturbs this case, so a
        // disagreement between the circuit's `y` and the reference here would
        // make them pass for the wrong reason.
        const w = calldataView(honest);
        bindFiatShamir(w, calldataView(w));
        await expectWitnessY(ctx.circuit, w, calldataY(w));
    });
});
