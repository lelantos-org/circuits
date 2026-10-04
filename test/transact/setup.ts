// Shared wiring for the transact suites: `lib/harness.ts :: useCircuit` plus a
// `TxBuilder`, with `projectingTester` (`lib/transact.ts`) applied at load.

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
 * Callers destructure at test time (`const { circuit, tx } = ctx`).
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
