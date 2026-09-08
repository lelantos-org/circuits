// Shared wiring for the transact suites: the same builder and the same compiled
// circuit. `loadCircuit` memoizes, so all suites together cost one compile.
//
// This is `lib/harness.ts :: useCircuit` plus the two things only transact
// needs: the `TxBuilder`, and `projectingTester` applied at load — see that
// function's docblock in `lib/transact.ts` for why it belongs there and not at
// each call site.

import { srcPath } from "../lib/circuit";
import { pendingCtx, useCircuit, type CircuitCtx } from "../lib/harness";
import { buildTxBuilder, projectingTester, TxBuilder } from "../lib/transact";
import { DEPTH } from "../lib/constants";

export const CIRCUIT = srcPath("4x6.circom");

/** A second asset, for the per-asset conservation tests. */
export const ASSET_B = 99n;

export interface TransactCtx extends CircuitCtx {
    /** Populated by `before`; reading it earlier is a programming error. */
    tx: TxBuilder;
}

/**
 * Register the `before` hook and return the context object it populates.
 *
 * Returns a stable object rather than the values themselves, so callers
 * destructure at test time (`const { circuit, tx } = ctx`).
 */
export function useTransactCircuit(): TransactCtx {
    const ctx = useCircuit(CIRCUIT, projectingTester) as TransactCtx;
    // `tx` is added here rather than by `useCircuit`, so it needs the same
    // read-before-hook guard the inherited fields get.
    Object.defineProperties(ctx, Object.getOwnPropertyDescriptors(
        pendingCtx<Pick<TransactCtx, "tx">>(["tx"], "useTransactCircuit"),
    ));
    before(async () => {
        ctx.tx = await buildTxBuilder(DEPTH);
    });
    return ctx;
}
