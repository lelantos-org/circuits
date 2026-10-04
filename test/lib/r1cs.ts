// R1CS-level access to a compiled circuit.
//
// `circom_tester` runs only the witness generator (`<--`, the assignment order,
// `assert`), but a proof binds the verifier only to the constraint system
// (`===`, `<==`). A signal the generator computes but the R1CS does not pin can
// be chosen freely by a malicious prover, and mutating the input object cannot
// reveal it. Detecting one means changing an honest witness vector directly and
// checking it against the R1CS. This module provides the R1CS side;
// `underconstrained.ts` is the search.
//
// Field elements are plain `bigint` in normal (non-Montgomery) form, as
// `readR1cs` yields for coefficients and the wasm calculator yields for witness
// entries.

import * as fs from "fs";
import * as readline from "readline";

// r1csfile ships without TS types
// @ts-ignore
import { readR1cs } from "r1csfile";
// @ts-ignore
import { F1Field } from "ffjavascript";

// ===== field =====

/** BN254 scalar field order — the prime circom compiles against by default. */
export const P = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

export const mod = (x: bigint): bigint => ((x % P) + P) % P;
export const fadd = (a: bigint, b: bigint): bigint => mod(a + b);
export const fsub = (a: bigint, b: bigint): bigint => mod(a - b);
export const fmul = (a: bigint, b: bigint): bigint => mod(a * b);

/** Multiplicative inverse by the extended Euclidean algorithm. Throws on zero. */
export function finv(a: bigint): bigint {
    const x = mod(a);
    if (x === 0n) throw new Error("finv: no inverse for 0");
    let [oldR, r] = [x, P];
    let [oldS, s] = [1n, 0n];
    while (r !== 0n) {
        const q = oldR / r;
        [oldR, r] = [r, oldR - q * r];
        [oldS, s] = [s, oldS - q * s];
    }
    return mod(oldS);
}

// ===== constraint system =====

/**
 * One R1CS linear combination: witness index (as a decimal string key, the form
 * `readR1cs` produces) -> coefficient.
 */
export type LinearCombination = Record<string, bigint>;

/** `(A · w) * (B · w) - (C · w) = 0`. */
export type Constraint = [LinearCombination, LinearCombination, LinearCombination];

/**
 * The witness vector's regions, in the order circom lays them out:
 * `[1, ...outputs, ...public inputs, ...private inputs, ...intermediates]`.
 *
 * A second witness that differs only in an intermediate proves the same public
 * statement (malleability). One that differs in an output or a public input
 * proves a different statement under the same proof (a soundness break).
 */
export type Region = "constant" | "output" | "publicInput" | "privateInput" | "intermediate";

export interface R1csView {
    nVars: number;
    nOutputs: number;
    nPubInputs: number;
    nPrvInputs: number;
    constraints: Constraint[];
    /** Witness index -> indices of every constraint whose A, B or C mentions it. */
    occurrences: Map<number, number[]>;
    region(index: number): Region;
    /** `lc · w`. */
    evalLc(lc: LinearCombination, witness: bigint[]): bigint;
    /** Index of the first unsatisfied constraint, or -1 if the witness satisfies. */
    firstViolation(witness: bigint[]): number;
}

/**
 * Read a `.r1cs` and index it.
 *
 * Changing one witness entry can only affect constraints that mention it, so
 * with the occurrence index re-checking a single-signal mutation costs
 * `deg(signal)` constraint evaluations.
 */
export async function loadR1cs(r1csPath: string): Promise<R1csView> {
    const r1cs = await readR1cs(r1csPath, {
        loadConstraints: true,
        loadMap: false,
        getFieldFromPrime: (p: bigint) => new F1Field(p),
    });

    if (BigInt(r1cs.prime) !== P) {
        throw new Error(`loadR1cs: unexpected prime ${r1cs.prime}; this module assumes BN254`);
    }

    const constraints = r1cs.constraints as Constraint[];

    const occurrences = new Map<number, number[]>();
    for (let k = 0; k < constraints.length; k++) {
        for (const lc of constraints[k]) {
            for (const key in lc) {
                const s = Number(key);
                let list = occurrences.get(s);
                if (list === undefined) occurrences.set(s, (list = []));
                // A signal may appear in A, B and C of the same constraint; the
                // list holds each constraint once, and k is increasing.
                if (list[list.length - 1] !== k) list.push(k);
            }
        }
    }

    const nOutputs = r1cs.nOutputs as number;
    const nPubInputs = r1cs.nPubInputs as number;
    const nPrvInputs = r1cs.nPrvInputs as number;

    const view: R1csView = {
        nVars: r1cs.nVars,
        nOutputs,
        nPubInputs,
        nPrvInputs,
        constraints,
        occurrences,

        region(index: number): Region {
            if (index === 0) return "constant";
            if (index <= nOutputs) return "output";
            if (index <= nOutputs + nPubInputs) return "publicInput";
            if (index <= nOutputs + nPubInputs + nPrvInputs) return "privateInput";
            return "intermediate";
        },

        evalLc(lc: LinearCombination, witness: bigint[]): bigint {
            let acc = 0n;
            for (const key in lc) acc += lc[key] * witness[Number(key)];
            return mod(acc);
        },

        firstViolation(witness: bigint[]): number {
            for (let k = 0; k < constraints.length; k++) {
                const [A, B, C] = constraints[k];
                const a = view.evalLc(A, witness);
                const b = view.evalLc(B, witness);
                const c = view.evalLc(C, witness);
                if (mod(a * b - c) !== 0n) return k;
            }
            return -1;
        },
    };

    return view;
}

// ===== symbols =====

/** The `.sym` file, indexed both ways. */
export interface SymbolTable {
    /** Signal name for a witness index; `(no symbol)` when the label was folded away. */
    nameOf(index: number): string;
    /** Witness index for a signal name, or undefined when it has none. */
    indexOf(name: string): number | undefined;
    /** Every (index, name) pair the circuit kept. */
    entries(): Iterable<[number, string]>;
    /** How many witness indices carry a name. */
    readonly size: number;
}

/** What `nameOf` returns for an index the `.sym` does not cover. */
export const NO_SYMBOL = "(no symbol)";

/**
 * Read the `.sym` circom emits: one `labelIdx,varIdx,componentIdx,name` line per
 * label.
 *
 * `varIdx` is -1 for a label the optimizer removed; such labels own no witness
 * entry and are dropped. If an index has several names, the first wins.
 */
export async function loadSymbols(symPath: string): Promise<SymbolTable> {
    const byIndex = new Map<number, string>();
    const byName = new Map<string, number>();

    const rl = readline.createInterface({
        input: fs.createReadStream(symPath),
        crlfDelay: Infinity,
    });
    for await (const line of rl) {
        const parts = line.split(",");
        if (parts.length !== 4) continue;
        const varIdx = Number(parts[1]);
        if (varIdx < 0) continue;
        const name = parts[3];
        if (!byIndex.has(varIdx)) byIndex.set(varIdx, name);
        if (!byName.has(name)) byName.set(name, varIdx);
    }

    return {
        nameOf: index => byIndex.get(index) ?? NO_SYMBOL,
        indexOf: name => byName.get(name),
        entries: () => byIndex.entries(),
        get size() { return byIndex.size; },
    };
}

/**
 * Collapse array indices in a signal name: `main.vbal.in_eq[0][2].isz.inv` ->
 * `main.vbal.in_eq[*][*].isz.inv`.
 *
 * Which slots of a family trip depends on the witness values; the family does
 * not, so a report keyed on it is stable across witnesses.
 */
export function signalFamily(name: string): string {
    return name.replace(/\[\d+\]/g, "[*]");
}
