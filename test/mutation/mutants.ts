// Enumerates the mutants of `src/`: every operator applied at every statement
// of every file the two shipped circuits include.

import * as fs from "fs";
import * as path from "path";

import { lcg } from "../lib/rand";
import { OPERATORS, splitComments, type Edit } from "./operators";

/** The shipped circuits. A mutant is tested against the ones that include its file. */
export const ROOTS = ["4x6", "tree_update_batch"] as const;
export type Root = (typeof ROOTS)[number];

export interface Mutant {
    /** `<file>:<line>:<operator>:<variant>`, for display and `--only`. */
    id: string;
    /** Relative to `src/`. */
    file: string;
    line: number;
    op: string;
    bugClass: string;
    /** Index among the operator's mutants of this statement. */
    variant: number;
    /** The statement as written, trimmed. */
    source: string;
    /** What replaces it, trimmed; `(deleted)` for an emptied line. */
    mutated: string;
    /**
     * Occurrence index among statements of this file with the same `source`,
     * so the baseline key survives a line shift.
     */
    nth: number;
    edits: Edit[];
    roots: Root[];
}

const INCLUDE = /^\s*include\s+"([^"]+)"/;

/** Files under `srcDir` that `root` includes, transitively. circomlib is outside it. */
function closure(srcDir: string, root: string): Set<string> {
    const seen = new Set<string>();
    const visit = (rel: string) => {
        if (seen.has(rel)) return;
        const abs = path.join(srcDir, rel);
        if (!fs.existsSync(abs)) return;
        seen.add(rel);
        for (const line of fs.readFileSync(abs, "utf8").split("\n")) {
            const m = INCLUDE.exec(line);
            if (m === null) continue;
            const target = path.normalize(path.join(path.dirname(rel), m[1]));
            if (!target.startsWith("..")) visit(target);
        }
    };
    visit(`${root}.circom`);
    return seen;
}

/** `file -> roots including it`, over both shipped circuits. */
export function sourceFiles(srcDir: string): Map<string, Root[]> {
    const files = new Map<string, Root[]>();
    for (const root of ROOTS) {
        for (const file of closure(srcDir, root)) {
            files.set(file, [...(files.get(file) ?? []), root]);
        }
    }
    return new Map([...files].sort(([a], [b]) => a.localeCompare(b)));
}

/** Every mutant of `srcDir`, in file, line, operator order. */
export function enumerate(srcDir: string): Mutant[] {
    const mutants: Mutant[] = [];
    for (const [file, roots] of sourceFiles(srcDir)) {
        const original = fs.readFileSync(path.join(srcDir, file), "utf8");
        const { code } = splitComments(original);
        const occurrences = new Map<string, number>();
        // Two operators can produce the same text; the first one keeps it.
        const produced = new Set<string>();

        for (let i = 0; i < code.length; i++) {
            const source = code[i].trim();
            if (source === "") continue;
            const nth = occurrences.get(source) ?? 0;
            occurrences.set(source, nth + 1);

            for (const op of OPERATORS) {
                op.mutate(code, i).forEach((edits, variant) => {
                    const fingerprint = edits.map(e => `${e.line}\u0000${e.text.trim()}`).join("\u0001");
                    if (edits.every(e => e.text.trim() === code[e.line - 1].trim())) return;
                    if (produced.has(fingerprint)) return;
                    produced.add(fingerprint);
                    mutants.push({
                        id: `${file}:${i + 1}:${op.name}:${variant}`,
                        file,
                        line: i + 1,
                        op: op.name,
                        bugClass: op.bugClass,
                        variant,
                        source,
                        mutated: edits.map(e => e.text.trim() || "(deleted)").join("  "),
                        nth,
                        edits,
                        roots,
                    });
                });
            }
        }
    }
    return mutants;
}

/** `original` with `mutant` applied. Line count is preserved. */
export function apply(original: string, mutant: Mutant): string {
    const lines = original.split("\n");
    const { comment } = splitComments(original);
    for (const edit of mutant.edits) {
        const tail = comment[edit.line - 1];
        const text = edit.text.trimEnd();
        lines[edit.line - 1] = tail === "" ? text : text === "" ? tail : `${text} ${tail}`;
    }
    return lines.join("\n");
}

/**
 * A seeded order that interleaves operators, so a truncated run still samples
 * every defect class. The same seed gives the same order.
 */
export function shuffled(mutants: readonly Mutant[], seed: number): Mutant[] {
    const next = lcg(BigInt(Math.trunc(seed)) & ((1n << 64n) - 1n), 64n);
    const buckets = new Map<string, Mutant[]>();
    for (const m of mutants) {
        const bucket = buckets.get(m.op) ?? [];
        bucket.push(m);
        buckets.set(m.op, bucket);
    }
    for (const bucket of buckets.values()) {
        // Fisher-Yates. The high bits are used: an LCG's low bits have short periods.
        for (let i = bucket.length - 1; i > 0; i--) {
            const j = Number((next() >> 32n) % BigInt(i + 1));
            [bucket[i], bucket[j]] = [bucket[j], bucket[i]];
        }
    }
    const out: Mutant[] = [];
    const queues = [...buckets.values()];
    for (let round = 0; out.length < mutants.length; round++) {
        for (const q of queues) {
            if (round < q.length) out.push(q[round]);
        }
    }
    return out;
}

// ===== accepted survivors =====

/** One accepted survivor. Keyed on the statement text, not its line number. */
export interface Accepted {
    file: string;
    op: string;
    variant: number;
    source: string;
    nth: number;
    /** Why no suite can reject it. Required. */
    reason: string;
}

export function keyOf(m: Pick<Mutant, "file" | "op" | "variant" | "source" | "nth">): string {
    return [m.file, m.op, m.variant, m.nth, m.source].join("\u0000");
}

export function readAccepted(file: string): Accepted[] {
    if (!fs.existsSync(file)) return [];
    const parsed = JSON.parse(fs.readFileSync(file, "utf8")) as { survivors?: Accepted[] };
    return parsed.survivors ?? [];
}

export function writeAccepted(file: string, survivors: readonly Accepted[]): void {
    const sorted = [...survivors].sort((a, b) => keyOf(a).localeCompare(keyOf(b)));
    fs.writeFileSync(file, JSON.stringify({ survivors: sorted }, null, 2) + "\n");
}
