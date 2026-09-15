// Explanations for malleable findings.
//
// A `malleable` finding from `underconstrained.ts` is a second witness for the
// same public statement: a hidden entry moves while `y` and `z` do not. That is
// not a value break but is not necessarily harmless, so each one must be
// explained before a suite passes.
//
// An explainer names a precondition and checks it against the witness in hand.
// Allow-listing signal families by name (e.g. `main.vbal.in_eq[*][*].isz.inv`)
// is not accepted: an underconstrained signal inside such a family would pass
// unexamined.
//
// To add an explainer: state the gadget's constraints, derive when the signal is
// free, find a witness entry that decides it, and check that entry.

import type { Finding } from "./underconstrained";
import type { SymbolTable } from "./r1cs";

/**
 * Accounts for a finding, or returns null to leave it unexplained.
 *
 * Returning a string asserts that the finding is harmless and that the reason
 * was verified against `witness`, not inferred from the signal's name.
 */
export type Explainer = (
    f: Finding,
    witness: bigint[],
    symbols: SymbolTable,
) => string | null;

/**
 * `X.inv` of a circomlib `IsZero` whose input is zero in this witness.
 *
 * `IsZero` computes `out = 1 - in·inv` from the hint
 * `inv <-- in != 0 ? 1/in : 0`, under two constraints:
 *
 *     in · inv === 1 - out          in · out === 0
 *
 * At `in != 0` the first pins `inv` to `1/in`. At `in = 0` it reads
 * `0 === 1 - out`, which pins `out` to 1 and leaves `inv` unconstrained. So
 * `inv` is free exactly when `in = 0`, equivalently `out = 1`. A free `inv`
 * reaches nothing else, since `out` is pinned either way, so the public
 * statement cannot change with it.
 *
 * Either sibling decides the precondition, and which one remains depends on the
 * instance: `--O2` removes whichever is a linear alias. `main.vbal.*.isz` keeps
 * `in` while its `out` is folded into the sum it feeds; `main.spent[*].asset_nz`
 * keeps `out` and drops `in` (varIdx -1). The explainer reads whichever is
 * present and returns null when neither is.
 */
export const isZeroHint: Explainer = (f, witness, symbols) => {
    // The argument covers total freedom (any field element). A single
    // alternative value is a different case and is not covered.
    if (f.kind !== "unconstrained") return null;
    if (f.support.length !== 1) return null;

    const { name } = f.support[0];
    if (!name.endsWith(".inv")) return null;
    const base = name.slice(0, -".inv".length);

    const inIndex = symbols.indexOf(`${base}.in`);
    if (inIndex !== undefined) {
        return witness[inIndex] === 0n
            ? `IsZero hint: ${base}.in = 0, so inv is unconstrained by design`
            : null;
    }

    const outIndex = symbols.indexOf(`${base}.out`);
    if (outIndex !== undefined) {
        return witness[outIndex] === 1n
            ? `IsZero hint: ${base}.out = 1, so its input is 0 and inv is unconstrained`
            : null;
    }

    return null;
};

// No explainer for a free `frontier_in[d][k]`: `BatchAppend` pins every unread
// slot to zero, so a free frontier slot indicates a missing constraint.

/** Every explanation the suites accept. */
export const EXPLAINERS: readonly Explainer[] = [isZeroHint];

/** The first explanation that accounts for `f`, or null if none does. */
export function explain(
    f: Finding,
    witness: bigint[],
    symbols: SymbolTable,
    explainers: readonly Explainer[] = EXPLAINERS,
): string | null {
    for (const e of explainers) {
        const why = e(f, witness, symbols);
        if (why !== null) return why;
    }
    return null;
}

/** Split findings into the ones something accounts for and the ones nothing does. */
export function partitionExplained(
    findings: Finding[],
    witness: bigint[],
    symbols: SymbolTable,
): { explained: Finding[]; unexplained: Finding[] } {
    const explained: Finding[] = [];
    const unexplained: Finding[] = [];
    for (const f of findings) {
        (explain(f, witness, symbols) === null ? unexplained : explained).push(f);
    }
    return { explained, unexplained };
}
