// Divergent witness (soundness).
//
// The other batch suites derive `(z, y)` from the object passed to the circuit,
// via `rebindFiatShamir`. That checks whether a constraint fires, but witness
// and calldata are the same batch by construction, so a signal the circuit never
// pins still appears bound.
//
// In deployment they are separate: `MASP` hashes its calldata into `z` and
// compares its `y`, and the prover picks any witness satisfying the R1CS at that
// `z`. `z` is a circuit input read before the witness is chosen, so
// Schwartz-Zippel does not apply and hashing a word into the challenge binds it
// only if a constraint already pins it (src/README.md § 2a).
//
// These tests build the two views separately with `calldataView` +
// `bindFiatShamir` and assert the circuit cannot attest to a batch the contract
// did not validate. `transact/divergent.test.ts` is the transact counterpart.

import {
    bindFiatShamir,
    calldataView,
    DIVERGENCE_CASES,
    type BatchWitness,
} from "../lib/batch";
import { treeUpdateBatchChallenge, type TreeUpdateBatchPublicArgs } from "../lib/inputs";
import { assertViewsDiverge } from "../lib/expect";
import { TIMEOUT_HEAVY } from "../lib/constants";
import { expectBatchAccepts, expectBatchNotForgeable, useBatchCircuit } from "./setup";

describe("tree_update_batch / divergent witness", function () {
    this.timeout(TIMEOUT_HEAVY);

    const ctx = useBatchCircuit();

    /** The base each divergence is applied to: one honest single-leaf deposit. */
    function honestDeposit(val = 1000n, isDeposit: 0 | 1 = 1): BatchWitness {
        return ctx.batch.single({ val, isDeposit, asset: 7n });
    }

    /** The shared harness guard, over this circuit's challenge preimage. */
    function assertDiverged(w: BatchWitness, calldata: TreeUpdateBatchPublicArgs, field: string) {
        assertViewsDiverge(treeUpdateBatchChallenge(w), treeUpdateBatchChallenge(calldata), field);
    }

    for (const { field, diverge } of DIVERGENCE_CASES) {
        it(`divergent witness: ${field} declared differently in calldata cannot be forged`, async () => {
            const w = honestDeposit();
            const calldata = calldataView(w);
            diverge(calldata);
            assertDiverged(w, calldata, field);
            bindFiatShamir(w, calldata);
            await expectBatchNotForgeable(ctx.circuit, w, field);
        });
    }

    // The two cases below stage complete mint attempts rather than one-field
    // divergences. Both are reachable by a single party: `MASP.flushBatch` is
    // unpermissioned and `deposit` is external, so the depositor can also be the
    // flusher.

    it("divergent witness: is_deposit cleared in the witness cannot mint an unbound leaf", async () => {
        // The contract sees a 1-unit deposit of asset 7 and escrows accordingly.
        // The witness declares the same leaf a spend, so `active_dep` is 0, the
        // only constraint tying `cv_dep` to an asset and amount is gated off, and
        // the committed leaf holds 2^63 units instead of 1.
        //
        // `is_deposit` gates that constraint and is a private witness signal;
        // the circuit header lists it as a contract obligation (item 4).
        const w = honestDeposit(1n << 63n, 0);
        const calldata = calldataView(w);
        calldata.isDeposit[0] = 1;
        calldata.leafAsset[0] = 7n;
        calldata.leafPublicIn[0] = 1n;
        assertDiverged(w, calldata, "is_deposit");
        bindFiatShamir(w, calldata);
        await expectBatchNotForgeable(ctx.circuit, w, "is_deposit");
    });

    it("divergent witness: leaf_public_in inflated in the witness cannot mint value", async () => {
        // The gate is honestly 1 and the deposit binding holds against the
        // witness operands: `cv_dep` opens to 2^63 units of asset 7, while the
        // calldata the contract escrowed against declares 1. Pinning
        // `is_deposit` alone does not prevent this.
        const w = honestDeposit(1n << 63n);
        const calldata = calldataView(w);
        calldata.leafPublicIn[0] = 1n;
        assertDiverged(w, calldata, "leaf_public_in");
        bindFiatShamir(w, calldata);
        await expectBatchNotForgeable(ctx.circuit, w, "leaf_public_in");
    });

    it("divergent witness: a fully honest witness still matches its own calldata", async () => {
        // Harness guard. Every divergence above perturbs this unmodified
        // snapshot; if the circuit's `y` disagreed here, those cases would be
        // rejected for the wrong reason and pass vacuously.
        //
        // `rebindFiatShamir` is defined as this call, so this checks the circuit
        // against the reference, not one binder against the other.
        const w = honestDeposit();
        bindFiatShamir(w, calldataView(w));
        await expectBatchAccepts(ctx.circuit, w);
    });
});
