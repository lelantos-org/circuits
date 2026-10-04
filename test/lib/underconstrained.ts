// Negative-test generator: search from an honest witness `w` for a second
// witness `w' = w + t·v` the same R1CS accepts. It tests the constraint system,
// which is what a Groth16 proof binds, not the witness generator. See
// `Severity` for what a second witness implies.
//
// ===== the primitive =====
//
// Given a direction `v` in witness space, which steps `t` keep `w + t·v`
// satisfying? With `Ak = A·w` and `Av = A·v`, each constraint is a quadratic in
// `t`:
//
//     f(t) = (Ak + t·Av)(Bk + t·Bv) - (Ck + t·Cv)
//          = (Av·Bv)·t^2 + (Ak·Bv + Bk·Av - Cv)·t + (Ak·Bk - Ck)
//
// The constant term is zero because `w` satisfies, so `f(t) = t·(q2·t + q1)`:
//
//   q2 = 0, q1 = 0   the constraint is blind to `v`: every step passes
//   q2 = 0, q1 != 0  `t = 0` only: the direction is pinned
//   q2 != 0          also `t = -q1/q2`, unless that is 0 (double root)
//
// `sweepDirection` intersects these sets over every constraint that touches
// `v`'s support.
//
// ===== the two searches =====
//
// `sweepSingleSignal` passes every unit vector: one witness entry moves and
// everything else is held fixed.
//
// `sweepGroups` covers signals that must move together: a bit vector
// re-decomposed, a quotient/remainder pair, both coordinates of a curve point,
// a hint and the value it feeds. For a group `S` of signals it takes the null
// space of the Jacobian restricted to `S`,
//
//     J[k][s] = A_k[s]·Bk + B_k[s]·Ak - C_k[s]
//
// whose vectors are the directions in which every constraint's linear response
// vanishes, and passes each to `sweepDirection`.
//
// ===== limits =====
//
// The group search holds everything outside the group fixed. Groups come from
// the `.sym` component tree and from individual constraints' signal sets, both
// capped by size, so freedom spanning unrelated components is out of reach;
// `just picus` decides the general case. A clean run means "these directions
// are pinned", not "the circuit is sound".

import {
    fadd,
    fmul,
    fsub,
    finv,
    mod,
    signalFamily,
    type LinearCombination,
    type R1csView,
    type Region,
    type SymbolTable,
} from "./r1cs";

/**
 * How a second witness differs from the honest one.
 *
 * `break`: an output or public input moves, so the witness proves a different
 * public statement. `malleable`: only hidden state moves; this indicates a
 * missing constraint, and each occurrence requires manual review.
 */
export type Severity = "break" | "malleable";

/** One witness entry that moves, and by how much per unit step. */
export interface SupportEntry {
    index: number;
    /** `.sym` name, or `(no symbol)` when the compiler folded the label away. */
    name: string;
    region: Region;
    /** `w'[index] = w[index] + t·delta`. */
    delta: bigint;
}

export interface Finding {
    /** Every entry that moves, ascending by index. Length 1 for a unit sweep. */
    support: SupportEntry[];
    /**
     * Stable key for the baseline: the support's `.sym` names with array indices
     * collapsed, deduplicated and joined. Which slot trips depends on the
     * witness; the family does not.
     */
    family: string;
    region: Region;
    severity: Severity;
    /**
     * `unconstrained`: every step along the direction is admissible.
     * `alternate`: exactly one non-zero step is.
     */
    kind: "unconstrained" | "alternate";
    /** The step to take. For `unconstrained` any non-zero step works; this is 1. */
    t: bigint;
    origin: "single" | "group";
    /** Constraints touching the support. */
    degree: number;
}

/** A direction in witness space: witness index -> component. Sparse, non-zero. */
export type Direction = Map<number, bigint>;

export type DirectionResult =
    | { kind: "pinned" }
    | { kind: "unconstrained" }
    | { kind: "alternate"; t: bigint };

/** `lc · v` over a sparse direction. */
function dotDirection(lc: LinearCombination, v: Direction): bigint {
    let acc = 0n;
    // Iterates the direction rather than the linear combination: `v` has a few
    // entries and an `lc` can have thousands.
    for (const [index, delta] of v) {
        const coef = lc[String(index)];
        if (coef !== undefined) acc += coef * delta;
    }
    return mod(acc);
}

/**
 * The set of steps `t` that keep `w + t·v` satisfying the whole system.
 *
 * `witness` must already satisfy it: the algebra assumes `t = 0` is a root.
 */
export function sweepDirection(
    view: R1csView,
    witness: bigint[],
    v: Direction,
): DirectionResult {
    let allowed: bigint | null = null; // null = no non-zero step found yet
    let sawRestriction = false;

    for (const k of constraintsTouching(view, v.keys())) {
        const [A, B, C] = view.constraints[k];

        const Av = dotDirection(A, v);
        const Bv = dotDirection(B, v);
        const Cv = dotDirection(C, v);
        if (Av === 0n && Bv === 0n && Cv === 0n) continue; // blind to `v`

        const Ak = view.evalLc(A, witness);
        const Bk = view.evalLc(B, witness);

        const q2 = fmul(Av, Bv);
        const q1 = fsub(fadd(fmul(Ak, Bv), fmul(Bk, Av)), Cv);

        if (q2 === 0n && q1 === 0n) continue; // vacuous along `v`

        sawRestriction = true;
        // Linear in `t`, so `t = 0` is the only root; or a double root at 0.
        if (q2 === 0n) return { kind: "pinned" };
        const t = fmul(mod(-q1), finv(q2));
        if (t === 0n) return { kind: "pinned" };

        if (allowed === null) allowed = t;
        else if (allowed !== t) return { kind: "pinned" };
    }

    if (!sawRestriction) return { kind: "unconstrained" };
    return allowed === null ? { kind: "pinned" } : { kind: "alternate", t: allowed };
}

/** Union of the constraint lists of every signal in `support`, ascending. */
function constraintsTouching(view: R1csView, support: Iterable<number>): number[] {
    const seen = new Set<number>();
    for (const s of support) {
        const list = view.occurrences.get(s);
        if (list === undefined) continue;
        for (const k of list) seen.add(k);
    }
    return [...seen].sort((a, b) => a - b);
}

// ===== search 1: unit vectors =====

export interface SweepOptions {
    /**
     * Only sweep these witness indices. Defaults to every index but the
     * constant, which is not a variable.
     */
    indices?: Iterable<number>;
}

/**
 * Every single-signal second witness. A signal no constraint mentions is
 * reported as `unconstrained` without algebra.
 */
export function sweepSingleSignal(
    view: R1csView,
    witness: bigint[],
    symbols: SymbolTable,
    opts: SweepOptions = {},
): Finding[] {
    const findings: Finding[] = [];
    const indices = opts.indices ?? range(1, view.nVars);
    // Reused across signals rather than reallocated per witness entry.
    const v: Direction = new Map();

    for (const s of indices) {
        const touching = view.occurrences.get(s);
        if (touching === undefined) {
            findings.push(build(view, symbols, [[s, 1n]], "unconstrained", 1n, 0, "single"));
            continue;
        }

        v.clear();
        v.set(s, 1n);

        const result = sweepDirection(view, witness, v);
        if (result.kind === "pinned") continue;
        findings.push(build(
            view, symbols, [[s, 1n]],
            result.kind,
            result.kind === "alternate" ? result.t : 1n,
            touching.length,
            "single",
        ));
    }

    return findings;
}

// ===== search 2: null-space directions over a group =====

/** A set of witness indices to search jointly, with a label for the report. */
export interface Group {
    label: string;
    signals: number[];
}

export interface GroupSweepOptions {
    /**
     * Skip groups larger than this. The null-space elimination is cubic in the
     * group size, and the large components are Poseidon permutations whose
     * internals are pinned by construction.
     */
    maxSignals?: number;
    /** Skip groups touching more constraints than this. */
    maxConstraints?: number;
}

export const DEFAULT_MAX_GROUP_SIGNALS = 128;
export const DEFAULT_MAX_GROUP_CONSTRAINTS = 4096;

/**
 * Multi-signal second witnesses over the supplied groups: for each group, the
 * null space of its Jacobian, each vector decided by `sweepDirection`.
 *
 * Findings whose support is a single signal are dropped: `sweepSingleSignal`
 * reports those.
 */
export function sweepGroups(
    view: R1csView,
    witness: bigint[],
    symbols: SymbolTable,
    groups: Iterable<Group>,
    opts: GroupSweepOptions = {},
): Finding[] {
    const maxSignals = opts.maxSignals ?? DEFAULT_MAX_GROUP_SIGNALS;
    const maxConstraints = opts.maxConstraints ?? DEFAULT_MAX_GROUP_CONSTRAINTS;

    const findings: Finding[] = [];
    const seen = new Set<string>();
    const sides = evalConstraintSides(view, witness);

    // The two group sources overlap, and a column set already searched yields
    // the same null space.
    const searched = new Set<string>();

    for (const group of groups) {
        const signals = group.signals;
        if (signals.length < 2 || signals.length > maxSignals) continue;

        const columns = signals.join(",");
        if (searched.has(columns)) continue;
        searched.add(columns);

        const rows = constraintsTouching(view, signals);
        if (rows.length > maxConstraints) continue;

        for (const vec of nullSpace(jacobian(view, sides, rows, signals), signals.length)) {
            const entries: [number, bigint][] = [];
            for (let i = 0; i < signals.length; i++) {
                if (vec[i] !== 0n) entries.push([signals[i], vec[i]]);
            }
            // A one-signal direction is a unit vector.
            if (entries.length < 2) continue;

            const key = entries.map(([i, d]) => `${i}:${d}`).join(",");
            if (seen.has(key)) continue;
            seen.add(key);

            const result = sweepDirection(view, witness, new Map(entries));
            if (result.kind === "pinned") continue;

            findings.push(build(
                view, symbols, entries,
                result.kind,
                result.kind === "alternate" ? result.t : 1n,
                rows.length,
                "group",
            ));
        }
    }

    return findings;
}

/**
 * `A_k·w` and `B_k·w` for every constraint, evaluated once per witness: they
 * do not depend on the group being searched.
 */
interface ConstraintSides {
    a: bigint[];
    b: bigint[];
}

function evalConstraintSides(view: R1csView, witness: bigint[]): ConstraintSides {
    const n = view.constraints.length;
    const a = new Array<bigint>(n);
    const b = new Array<bigint>(n);
    for (let k = 0; k < n; k++) {
        const [A, B] = view.constraints[k];
        a[k] = view.evalLc(A, witness);
        b[k] = view.evalLc(B, witness);
    }
    return { a, b };
}

/**
 * Jacobian of the constraint system at `witness`, restricted to `signals`.
 * Row `k` is the derivative of `(A·w)(B·w) - C·w` with respect to each signal:
 *
 *     d/ds = A_k[s]·(B_k·w) + B_k[s]·(A_k·w) - C_k[s]
 */
function jacobian(
    view: R1csView,
    sides: ConstraintSides,
    rows: number[],
    signals: number[],
): bigint[][] {
    // Signal indices key the sparse linear combinations as strings; convert once
    // per column rather than once per cell.
    const keys = signals.map(String);
    return rows.map(k => {
        const [A, B, C] = view.constraints[k];
        const Ak = sides.a[k];
        const Bk = sides.b[k];
        return keys.map(key => {
            const a = A[key] ?? 0n;
            const b = B[key] ?? 0n;
            const c = C[key] ?? 0n;
            return fsub(fadd(fmul(a, Bk), fmul(b, Ak)), c);
        });
    });
}

/**
 * Basis of the null space of `m` (which is modified in place), by
 * Gauss-Jordan elimination over the field.
 *
 * Returns one vector per free column: the free column set to 1 and each pivot
 * column set to the negated entry the reduced matrix records for it.
 */
function nullSpace(m: bigint[][], cols: number): bigint[][] {
    const pivotOfRow: number[] = [];
    const pivotCols = new Set<number>();
    let row = 0;

    for (let col = 0; col < cols && row < m.length; col++) {
        let sel = -1;
        for (let r = row; r < m.length; r++) {
            if (m[r][col] !== 0n) { sel = r; break; }
        }
        if (sel === -1) continue;

        [m[row], m[sel]] = [m[sel], m[row]];

        const scale = finv(m[row][col]);
        for (let c = col; c < cols; c++) m[row][c] = fmul(m[row][c], scale);

        for (let r = 0; r < m.length; r++) {
            if (r === row || m[r][col] === 0n) continue;
            const factor = m[r][col];
            for (let c = col; c < cols; c++) {
                m[r][c] = fsub(m[r][c], fmul(factor, m[row][c]));
            }
        }

        pivotOfRow[row] = col;
        pivotCols.add(col);
        row++;
    }

    const basis: bigint[][] = [];
    for (let free = 0; free < cols; free++) {
        if (pivotCols.has(free)) continue;
        const vec = new Array<bigint>(cols).fill(0n);
        vec[free] = 1n;
        for (let r = 0; r < row; r++) vec[pivotOfRow[r]] = mod(-m[r][free]);
        basis.push(vec);
    }
    return basis;
}

// ===== group sources =====

/**
 * One group per `.sym` component (one `IsZero`, one `Num2Bits`, one curve
 * addition): the signals whose names share a parent path.
 */
export function componentGroups(symbols: SymbolTable): Group[] {
    const byComponent = new Map<string, number[]>();
    for (const [index, name] of symbols.entries()) {
        const parent = name.slice(0, name.lastIndexOf("."));
        if (parent === "") continue;
        let list = byComponent.get(parent);
        if (list === undefined) byComponent.set(parent, (list = []));
        list.push(index);
    }
    return [...byComponent].map(([label, signals]) => ({ label, signals }));
}

/**
 * One group per constraint: the signals it mentions. Covers couplings that
 * cross a component boundary, such as an equality wiring one gadget's output
 * to another's input.
 */
export function constraintGroups(view: R1csView): Group[] {
    const groups: Group[] = [];
    for (let k = 0; k < view.constraints.length; k++) {
        const signals = new Set<number>();
        for (const lc of view.constraints[k]) {
            for (const key in lc) {
                const s = Number(key);
                if (s !== 0) signals.add(s);
            }
        }
        if (signals.size >= 2) {
            groups.push({ label: `constraint ${k}`, signals: [...signals].sort((a, b) => a - b) });
        }
    }
    return groups;
}

// ===== the whole search =====

/**
 * Every group proposed by the two sources. Neither needs to be precise: a
 * group whose Jacobian has full column rank yields nothing.
 */
export function allGroups(view: R1csView, symbols: SymbolTable): Group[] {
    return [...componentGroups(symbols), ...constraintGroups(view)];
}

/**
 * Both searches over one honest witness. `witness` must satisfy the system;
 * callers assert `view.firstViolation(witness) === -1` first.
 */
export function searchWitness(
    view: R1csView,
    symbols: SymbolTable,
    witness: bigint[],
    groups: Group[],
): Finding[] {
    return [
        ...sweepSingleSignal(view, witness, symbols),
        ...sweepGroups(view, witness, symbols, groups),
    ];
}

// ===== findings =====

function build(
    view: R1csView,
    symbols: SymbolTable,
    entries: [number, bigint][],
    kind: Finding["kind"],
    t: bigint,
    degree: number,
    origin: Finding["origin"],
): Finding {
    const support: SupportEntry[] = entries
        .slice()
        .sort((a, b) => a[0] - b[0])
        .map(([index, delta]) => ({
            index,
            name: symbols.nameOf(index),
            region: view.region(index),
            delta: mod(delta),
        }));

    const families = [...new Set(support.map(e => signalFamily(e.name)))].sort();
    const broken = support.find(e => e.region === "output" || e.region === "publicInput");

    return {
        support,
        family: families.join(" + "),
        // The region that decides severity, so a break names the public entry.
        region: (broken ?? support[0]).region,
        severity: broken === undefined ? "malleable" : "break",
        kind,
        t: mod(t),
        origin,
        degree,
    };
}

function* range(from: number, to: number): Generator<number> {
    for (let i = from; i < to; i++) yield i;
}

/** `w + t·v` for a finding's direction. */
export function applyFinding(witness: bigint[], f: Finding): bigint[] {
    const mutated = witness.slice();
    for (const e of f.support) {
        mutated[e.index] = mod(witness[e.index] + f.t * e.delta);
    }
    return mutated;
}

/**
 * Substitute a finding's step and re-check the whole system, as an independent
 * check on the quadratic algebra.
 *
 * Returns the index of the constraint that rejected, or -1 when the mutated
 * witness satisfies (the finding is real).
 */
export function confirm(view: R1csView, witness: bigint[], f: Finding): number {
    if (!f.support.some(e => fmul(f.t, e.delta) !== 0n)) {
        throw new Error(`confirm: finding ${f.family} does not change the witness`);
    }
    return view.firstViolation(applyFinding(witness, f));
}

export function byFamily(findings: Finding[]): Map<string, Finding[]> {
    const out = new Map<string, Finding[]>();
    for (const f of findings) {
        let list = out.get(f.family);
        if (list === undefined) out.set(f.family, (list = []));
        list.push(f);
    }
    return out;
}

/** One line per family, widest first. */
export function formatReport(findings: Finding[]): string {
    if (findings.length === 0) return "  (none)";
    return [...byFamily(findings)]
        .sort((a, b) => b[1].length - a[1].length)
        .map(([family, list]) => {
            const f = list[0];
            const width = f.support.length === 1 ? "" : ` [${f.support.length} signals]`;
            return `  ${String(list.length).padStart(4)}x  ${f.severity.padEnd(9)} ` +
                `${f.kind.padEnd(14)} ${f.origin.padEnd(6)} ${family}${width}`;
        })
        .join("\n");
}
