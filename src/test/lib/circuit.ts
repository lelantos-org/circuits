// Wrap circom_tester so each test file picks the wasm + include path the same way.

import * as path from "path";
import { fileURLToPath } from "url";
// circom_tester ships without TS types
// @ts-ignore
import { wasm as wasmTester } from "circom_tester";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const SRC_DIR = path.join(__dirname, "..", "..");
const NODE_MODULES = path.join(SRC_DIR, "..", "node_modules");

export const SRC = SRC_DIR;
export const FIXTURES = path.join(SRC_DIR, "test", "fixtures");

export function srcPath(...parts: string[]): string {
    return path.join(SRC_DIR, ...parts);
}

export function fixturePath(name: string): string {
    return path.join(FIXTURES, name);
}

// Load a circuit by absolute path; resolves circom_tester's `include` to node_modules.
export async function loadCircuit(absPath: string): Promise<any> {
    return wasmTester(absPath, { include: [NODE_MODULES] });
}
