// Repository paths and the committed files the suites read. Paths resolve
// against the package root, not the spec file's directory.

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

// Not validated: the caller asserts the schema.
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
