// Explanations for malleable findings.
//
// A `malleable` finding from `underconstrained.ts` is a second witness for the
// same public statement: a hidden entry moves while `y` and `z` do not. Each one
// must be explained before a suite passes.
//
// An explainer names a precondition and checks it against the witness in hand.
// Signal families are not allow-listed by name: an underconstrained signal
// inside such a family would pass unexamined.

import type { Finding } from "./underconstrained";
import type { SymbolTable } from "./r1cs";

/**
 * Accounts for a finding, or returns null to leave it unexplained. A returned
 * string asserts that the reason was verified against `witness`, not inferred
 * from the signal's name.
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
 * At `in != 0` the first pins `inv` to `1/in`. At `in = 0` it pins `out` to 1
 * and leaves `inv` unconstrained, so `inv` is free when `in = 0`, equivalently
 * `out = 1`. `out` is pinned either way, so a free `inv` reaches nothing else.
 *
 * `--O2` removes whichever of `in` and `out` is a linear alias (varIdx -1), so
 * the explainer reads whichever sibling is present and returns null when
 * neither is.
 */
export const isZeroHint: Explainer = (f, witness, symbols) => {
    // The argument covers total freedom (any field element), not a single
    // alternative value.
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
