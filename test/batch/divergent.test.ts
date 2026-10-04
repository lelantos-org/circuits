// Divergent witness (soundness): witness and calldata are built as separate
// views with `calldataView` + `bindFiatShamir`, and the circuit must not attest
// to a batch the contract did not validate.
//
// `MASP` hashes its calldata into `z`, compares its `y`, and passes the calldata
// digest word to the verifier; the prover picks any witness satisfying the R1CS
// at that `z`, so hashing a signal into the challenge binds nothing on its own.
// What binds is the digest public signal: it commits the witness's
// coefficients, and it is in the preimage of `z` (src/README.md § 2a).
//
// Each one-field case runs twice: with the calldata digest word left at the
// witness's own digest, where `y` must differ, and recomputed for the rewritten
// coefficients, where the digest public signal differs.

import {
    bindFiatShamir,
    calldataView,
    redigest,
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

    const DIGESTS = [
        { label: "digest left at the witness's", fix: (_c: TreeUpdateBatchPublicArgs) => {} },
        { label: "digest recomputed for the calldata", fix: redigest },
    ];

    for (const { field, diverge } of DIVERGENCE_CASES) {
        for (const { label, fix } of DIGESTS) {
            it(`divergent witness: ${field} declared differently in calldata cannot be forged (${label})`, async () => {
                const w = honestDeposit();
                const calldata = calldataView(w);
                diverge(calldata);
                fix(calldata);
                assertDiverged(w, calldata, field);
                bindFiatShamir(w, calldata);
                await expectBatchNotForgeable(ctx.circuit, w, field);
            });
        }
    }

    it("divergent witness: a digest declared differently in calldata cannot be forged", async () => {
        // Every coefficient agrees, so `y` agrees. Only the digest public signal
        // separates the proof from this calldata.
        const w = honestDeposit();
        const calldata = calldataView(w);
        calldata.digest = calldata.digest + 1n;
        assertDiverged(w, calldata, "digest");
        bindFiatShamir(w, calldata);
        await expectBatchNotForgeable(ctx.circuit, w, "digest");
    });

    // The two cases below stage complete mint attempts. Both are reachable by a
    // single party: `MASP.flushBatch` is unpermissioned and `deposit` is
    // external, so the depositor can also be the flusher.

    it("divergent witness: is_deposit cleared in the witness cannot mint an unbound leaf", async () => {
        // The contract sees a 1-unit deposit of asset 7 and escrows accordingly.
        // The witness declares the same slot a spend, so the word is inserted as
        // it stands, and the word is a commitment to 2^63 units instead of an
        // `inner`.
        const w = honestDeposit(1n << 63n, 0);
        const calldata = calldataView(w);
        calldata.isDeposit[0] = 1;
        calldata.leafAsset[0] = 7n;
        calldata.leafPublicIn[0] = 1n;
        // What calldata describing that deposit would carry.
        redigest(calldata);
        assertDiverged(w, calldata, "is_deposit");
        bindFiatShamir(w, calldata);
        await expectBatchNotForgeable(ctx.circuit, w, "is_deposit");
    });

    it("divergent witness: leaf_public_in inflated in the witness cannot mint value", async () => {
        // The flag is honestly 1 and the leaf is the commitment over the
        // witness's operands, 2^63 units of asset 7, while the calldata the
        // contract escrowed against declares 1.
        const w = honestDeposit(1n << 63n);
        const calldata = calldataView(w);
        calldata.leafPublicIn[0] = 1n;
        redigest(calldata);
        assertDiverged(w, calldata, "leaf_public_in");
        bindFiatShamir(w, calldata);
        await expectBatchNotForgeable(ctx.circuit, w, "leaf_public_in");
    });

    it("divergent witness: a fully honest witness still matches its own calldata", async () => {
        // Harness guard. Every divergence above perturbs this unmodified
        // snapshot; if the circuit's `y` disagreed here, those cases would be
        // rejected for the wrong reason and pass vacuously.
        const w = honestDeposit();
        bindFiatShamir(w, calldataView(w));
        await expectBatchAccepts(ctx.circuit, w);
    });
});
