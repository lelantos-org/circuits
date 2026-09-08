// Can a transact prover attest to a transaction the contract never validated?
//
// `test/tree_update_batch.test.ts :: divergent witness` asks this of the batch,
// where the answer was twice "yes". This is the transact half, and it did not
// exist: every transact suite derives `z` from the same bundle it feeds the
// circuit (`rebindFiatShamir`), so witness and calldata are the same
// transaction by construction and a word the circuit never pins still reads as
// bound.
//
// The shape being ruled out is the one `blinders.test.ts` argues is reachable:
// `z` comes from calldata the prover authored and is read BEFORE the witness is
// chosen, so any witness satisfying the R1CS at that `z` produces a verifying
// proof. Soundness rests entirely on the circuit's `y` disagreeing with the
// contract's whenever the two descriptions do.
//
// Transact's challenge-only words cannot be tested here and do not need to be:
// they are not signals of `4x6.circom` at all, so no witness copy exists to
// diverge — `binding.test.ts :: the challenge-only fields are not circuit
// signals` checks exactly that against the compiled circuit, and it is the
// argument that lets them be excluded from `y`. What this file covers is the
// other 46 words, every one of which IS a signal.

import { flatten, type TransactWitnessBundle } from "../helpers";
import { assertViewsDiverge, expectNotForgeable, expectWitnessY } from "../lib/expect";
import { ALICE_NSK, TIMEOUT_CIRCUIT } from "../lib/constants";
import { bindFiatShamir, calldataView, calldataY } from "../lib/transact";
import { useTransactCircuit } from "./setup";

describe("transact_4x6 / divergent witness", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    // `TxBuilder.balanced()` is the shared honest base the tamper suites use;
    // its docblock states the contract this file needs — "honest in every respect
    // but the field under test".
    //
    // Built once. Every case diverges a `structuredClone` of it and
    // `bindFiatShamir` writes only `w.z`, so no case can contaminate the base,
    // and `tx.build` is ~260ms a call.
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

    // One per coefficient block. Each is a signal of the circuit, so a witness
    // copy exists and can disagree; each is also evaluated into `y`, which is
    // what makes the disagreement visible. A field moved out of `coeffs` while
    // remaining a signal would fail here.
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
        // Guards the harness: this is the case every divergence above perturbs,
        // so if the circuit's `y` disagreed with the reference here, each of
        // them would pass for the wrong reason.
        const w = calldataView(honest);
        bindFiatShamir(w, calldataView(w));
        await expectWitnessY(ctx.circuit, w, calldataY(w));
    });
});
