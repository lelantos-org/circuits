// Shared wiring for the transact suites.
//
// Each suite needs the same builder and the same compiled circuit.
// `loadCircuit` memoizes, so all of them together cost one compile.

import { loadCircuit, srcPath, type CircuitTester } from "../lib/circuit";
import { buildTxBuilder, TxBuilder } from "../lib/transact";
import { DEPTH } from "../lib/constants";

export const CIRCUIT = srcPath("2x2.circom");

/** A second asset, for the per-asset conservation tests. */
export const ASSET_B = 99n;

export interface TransactCtx {
    /** Populated by `before`; reading it earlier is a programming error. */
    circuit: CircuitTester;
    tx: TxBuilder;
}

/**
 * Register the `before` hook and return the context object it populates.
 *
 * Returns a stable object rather than the values themselves, so callers
 * destructure at test time (`const { circuit, tx } = ctx`).
 */
export function useTransactCircuit(): TransactCtx {
    const ctx = {} as TransactCtx;
    before(async () => {
        ctx.tx = await buildTxBuilder(DEPTH);
        ctx.circuit = await loadCircuit(CIRCUIT);
    });
    return ctx;
}
