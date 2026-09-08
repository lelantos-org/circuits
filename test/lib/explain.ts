// Why a malleable finding is allowed to exist.
//
// A `malleable` finding from `underconstrained.ts` is a second witness for the
// SAME public statement: some hidden entry moves and `y` and `z` do not. That is
// not a value break, but it is not automatically harmless either, so every one
// has to be EXPLAINED before a suite lets it pass.
//
// The bar an explainer has to clear is that it names a PRECONDITION and has it
// checked against the witness in hand. An earlier version of the suite instead
// allow-listed signal families like `main.vbal.in_eq[*][*].isz.inv` and accepted
// any number of findings inside them. That trusts a name: a genuinely
// underconstrained signal that happened to land in an allow-listed family would
// have passed unexamined, and the list would have grown every time someone
// wanted a green run.
//
// Adding one is deliberately more work than widening a list would be — that is
// the point. State the gadget's constraints, derive when the signal is free,
// find a witness entry that decides it, and check that entry.

import type { Finding } from "./underconstrained";
import type { SymbolTable } from "./r1cs";

/**
 * Accounts for a finding, or returns null to leave it unexplained.
 *
 * Returning a string is an assertion that the finding is harmless AND that the
 * reason was verified against `witness` — not that the signal's name looked
 * familiar.
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
 * `0 === 1 - out`, which pins `out` to 1 and says nothing whatever about `inv`.
 * So `inv` is free EXACTLY when `in = 0`, equivalently when `out = 1` — and a
 * free `inv` reaches nothing else, since `out` stays pinned either way, so the
 * public statement cannot move with it.
 *
 * Either sibling decides the precondition, and which one SURVIVES depends on the
 * instance: `--O2` deletes whichever was a linear alias, and it is not the same
 * one each time. `main.vbal.*.isz` keeps `in` while its `out` is folded into the
 * sum it feeds; `main.spent[*].asset_nz` is the mirror image, `in` gone (varIdx
 * -1) and `out` kept. So read whichever is still there, and refuse when neither
 * is rather than assuming a layout.
 */
export const isZeroHint: Explainer = (f, witness, symbols) => {
    // The freedom this argument describes is total: any field element does. A
    // single alternative value is a different phenomenon and is not covered.
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

/**
 * `frontier_in[d][k]` at the level's own digit, where the running rebuild sits.
 *
 * `FrontierRoot` (src/lib/frontier_root.circom) fills child slot `k` of level
 * `d` from one of three sources, chosen by the one-hot digit selector `s[d][*]`:
 *
 *     k <  digit : frontier_in[d][k]   (a filled left sibling)
 *     k == digit : cur[d]              (the running rebuild)
 *     k >  digit : zeros[d]            (an empty right subtree)
 *
 * The frontier contribution to each slot is a PRODUCT with the selectors for
 * the digits strictly above it — `c1_post[d] <== (s[d][2] + s[d][3]) *
 * frontier_in[d][1]`, and so on. At `digit == k` every one of those selectors is
 * zero, so the whole product vanishes and `frontier_in[d][k]` multiplies nothing
 * anywhere in the system. It is free because the tree has no value to put there:
 * that position is occupied by the node being rebuilt.
 *
 * Exactly one slot per level qualifies, and only while `digit_d < 3` — slot 3 is
 * never a frontier slot, so at `digit_d == 3` all three are read and none is
 * free. This is what makes the freedom self-limiting rather than a hole: it
 * cannot move `old_root`, because the slots that DO feed the Poseidon preimage
 * at that level are a different set.
 *
 * PRECONDITION, checked against the witness: `s[d][k] == 1`, i.e. this level's
 * digit really is `k`. A frontier slot free at any OTHER digit would mean a slot
 * the rebuild reads is going unconstrained, which is a forged-root primitive and
 * must stay unexplained.
 */
export const frontierRunningSlot: Explainer = (f, witness, symbols) => {
    // Total freedom only; a single alternative value is a different phenomenon.
    if (f.kind !== "unconstrained") return null;
    if (f.support.length !== 1) return null;

    const { name } = f.support[0];
    const m = /^(.*)frontier_in\[(\d+)\]\[(\d+)\]$/.exec(name);
    if (m === null) return null;
    const [, prefix, level, slot] = m;

    // The selector that decides it. Refuse rather than assume a layout if the
    // compiler folded it away — same rule as `isZeroHint`.
    const sIndex = symbols.indexOf(`${prefix}frontier_root.s[${level}][${slot}]`);
    if (sIndex === undefined) return null;

    return witness[sIndex] === 1n
        ? `FrontierRoot running slot: digit_${level} = ${slot}, so frontier_in[${level}][${slot}] ` +
              "multiplies a zero selector and the rebuild reads cur instead"
        : null;
};

/** Every explanation the suites accept. */
export const EXPLAINERS: readonly Explainer[] = [isZeroHint, frontierRunningSlot];

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
