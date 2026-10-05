// What earlier campaigns learned, kept in `build/.mutation/history.json`.
//
// It is used three ways, none of which can change a verdict:
//
//   * ordering: the spec that rejected a mutant last time runs first, then the
//     specs that reject its neighbours, then the cheapest;
//   * sampling: a run prefers mutants that were weak, then ones never tested;
//   * resuming: `--resume` reuses an outcome recorded for the same tree.
//
// An outcome is reused only under the same `fingerprint`: the digest of every
// file a gate reads.

import { execFileSync } from "child_process";
import * as crypto from "crypto";
import * as fs from "fs";
import * as path from "path";

import { ROOT } from "../lib/files";
import { keyOf, shuffled, type Mutant } from "./mutants";
import { calculatorPreserving } from "./operators";

export type Status = "stillborn" | "equivalent" | "killed" | "static" | "survived";

/** Statuses of a mutant the gates ran against. */
export const TESTED: readonly Status[] = ["killed", "static", "survived"];

/** The last outcome recorded for one mutant. `outcome` is the runner's record, opaque here. */
export interface Past {
    fingerprint: string;
    file: string;
    op: string;
    status: Status;
    /** The first dynamic gate that rejected it, and the spec file that failed. */
    stage?: string;
    spec?: string;
    /** The gates the run was asked for, and whether every one of them ran. */
    stages: string[];
    matrix: boolean;
    outcome: unknown;
}

export interface History {
    /** Per spec file, the time its tests took against the unmutated tree. */
    specMs: Record<string, number>;
    /** The tree and gates the unmutated circuits last passed under. */
    green?: { fingerprint: string; stages: string[] };
    mutants: Record<string, Past>;
}

export function readHistory(file: string): History {
    if (!fs.existsSync(file)) return { specMs: {}, mutants: {} };
    try {
        const parsed = JSON.parse(fs.readFileSync(file, "utf8")) as Partial<History>;
        return { specMs: parsed.specMs ?? {}, green: parsed.green, mutants: parsed.mutants ?? {} };
    } catch {
        // Written by a run that was killed mid-write, or by an older format.
        return { specMs: {}, mutants: {} };
    }
}

/** Write through a rename, so a killed run leaves the previous file intact. */
export function writeHistory(file: string, history: History): void {
    const tmp = `${file}.tmp`;
    fs.writeFileSync(tmp, JSON.stringify(history));
    fs.renameSync(tmp, file);
}

// ===== fingerprint =====

/** Everything a gate reads, relative to the package root. Directories are walked. */
const INPUTS = ["src", "test", "lean/scripts", "lean/expected", "lean/Lelantos", "justfile", "package-lock.json", "scripts/mutate.ts"];

/** Not an input: accepting a survivor does not change what any gate does. */
const NOT_INPUTS = new Set(["test/mutation/survivors.json"]);

function walk(rel: string, out: string[]): void {
    const abs = path.join(ROOT, rel);
    if (!fs.existsSync(abs)) return;
    if (!fs.statSync(abs).isDirectory()) {
        if (!NOT_INPUTS.has(rel)) out.push(rel);
        return;
    }
    for (const name of fs.readdirSync(abs).sort()) walk(`${rel}/${name}`, out);
}

/** Digest of the tree and compiler the gates run against. */
export function fingerprint(): string {
    const files: string[] = [];
    for (const input of INPUTS) walk(input, files);
    for (const name of fs.readdirSync(path.join(ROOT, "lean"))) {
        if (name.endsWith(".md")) files.push(`lean/${name}`);
    }
    const hash = crypto.createHash("sha256");
    for (const rel of files.sort()) {
        hash.update(rel).update("\0").update(fs.readFileSync(path.join(ROOT, rel))).update("\0");
    }
    hash.update(execFileSync("circom", ["--version"]));
    return hash.digest("hex").slice(0, 16);
}

// ===== ordering =====

/**
 * `specs` in the order most likely to fail first on `mutant`: the spec that
 * rejected it before, then by how many mutants of the same source file each
 * spec has rejected, then cheapest first.
 */
export function orderSpecs(specs: readonly string[], mutant: Mutant, history: History): string[] {
    const own = history.mutants[keyOf(mutant)]?.spec;
    const neighbours = new Map<string, number>();
    for (const past of Object.values(history.mutants)) {
        if (past.file === mutant.file && past.spec !== undefined) {
            neighbours.set(past.spec, (neighbours.get(past.spec) ?? 0) + 1);
        }
    }
    const rank = (spec: string): [number, number, number] => [
        spec === own ? 0 : 1,
        -(neighbours.get(spec) ?? 0),
        history.specMs[spec] ?? 0,
    ];
    return [...specs].sort((a, b) => {
        const [ra, rb] = [rank(a), rank(b)];
        return ra[0] - rb[0] || ra[1] - rb[1] || ra[2] - rb[2] || a.localeCompare(b);
    });
}

/** `stages` with the one that rejected `mutant` before moved to the front. */
export function orderStages<S extends string>(stages: readonly S[], mutant: Mutant, history: History): S[] {
    const own = history.mutants[keyOf(mutant)]?.stage;
    return [...stages].sort((a, b) => Number(b === own) - Number(a === own));
}

// ===== sampling =====

/**
 * Whether a past outcome marks a spot the tests do not reach. A
 * calculator-preserving mutant that only lint rejects is expected, not a
 * finding.
 */
function weak(past: Past): boolean {
    return past.status === "survived" || (past.status === "static" && !calculatorPreserving(past.op));
}

/** Where a mutant stands relative to the current tree; lower is sampled first. */
export enum Tier {
    /** Not rejected by a test last time, and the tree has changed since. */
    Weak = 0,
    /** Never run. */
    New = 1,
    /** Killed under an older tree. */
    Old = 2,
    /** Already run against the current tree. */
    Current = 3,
}

export function tierOf(mutant: Mutant, history: History, current: string): Tier {
    const past = history.mutants[keyOf(mutant)];
    if (past === undefined) return Tier.New;
    if (past.fingerprint === current) return Tier.Current;
    return weak(past) ? Tier.Weak : Tier.Old;
}

/**
 * The share of one source file's mutants under one operator that no test
 * rejected, smoothed so a pair never tested sits at one half: unexplored code
 * ranks between code known to be weak and code known to be covered.
 */
function heat(history: History): (m: Mutant) => number {
    const seen = new Map<string, { tested: number; weak: number }>();
    for (const past of Object.values(history.mutants)) {
        if (!TESTED.includes(past.status)) continue;
        const key = `${past.file}\0${past.op}`;
        const entry = seen.get(key) ?? { tested: 0, weak: 0 };
        entry.tested++;
        if (weak(past)) entry.weak++;
        seen.set(key, entry);
    }
    return m => {
        const entry = seen.get(`${m.file}\0${m.op}`) ?? { tested: 0, weak: 0 };
        return (entry.weak + 1) / (entry.tested + 2);
    };
}

/**
 * The order a sampled run draws mutants in: by tier, then towards the
 * file-and-operator pairs that have let the most mutants through, then by the
 * seeded shuffle.
 */
export function prioritized(mutants: readonly Mutant[], history: History, current: string, seed: number): Mutant[] {
    const heatOf = heat(history);
    const drawn = new Map(shuffled(mutants, seed).map((m, i) => [m.id, i]));
    // Tenths, so the shuffle still decides among pairs of similar heat.
    const bucket = (m: Mutant) => Math.round(heatOf(m) * 10);
    return [...mutants].sort((a, b) =>
        tierOf(a, history, current) - tierOf(b, history, current) ||
        bucket(b) - bucket(a) ||
        drawn.get(a.id)! - drawn.get(b.id)!,
    );
}
