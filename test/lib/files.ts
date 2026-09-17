// Repository paths and the committed files the suites read: vectors, Lean
// layout dumps, circom sources.
//
// Every suite resolves against the package root rather than its own directory,
// so moving a spec file does not change what it reads.

import * as fs from "fs";
import * as path from "path";
import { fileURLToPath } from "url";

/** The `circuits/` package root. */
export const ROOT = path.join(path.dirname(fileURLToPath(import.meta.url)), "..", "..");

/** An absolute path under the package root. */
export function repoPath(...parts: string[]): string {
    return path.join(ROOT, ...parts);
}

export function readText(rel: string): string {
    return fs.readFileSync(repoPath(rel), "utf8");
}

// The files parsed here are hand-maintained or generated JSON whose schema the
// caller asserts, so the result is typed by the caller rather than validated.
export function readJson<T = any>(rel: string): T {
    return JSON.parse(readText(rel)) as T;
}

/** Non-empty, trimmed lines: the format of `lean/expected/layout-*.txt`. */
export function readLines(rel: string): string[] {
    return readText(rel)
        .split("\n")
        .map(l => l.trim())
        .filter(l => l.length > 0);
}
