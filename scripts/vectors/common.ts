// Shared plumbing for the vector generator.
//
// `just vectors-check` regenerates into a temp dir and diffs, so nothing here
// may read the clock, the absolute filesystem layout, or a random source.

import { keccak_256 } from "@noble/hashes/sha3";
import { createHash } from "node:crypto";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import {
    BABYJUB_SUBGROUP_ORDER,
    BN254_FR,
    H_BASE,
    Jubjub,
    MerkleTree,
    Poseidon,
    TAGS,
    type Field,
    type Point,
} from "../../test/ref/index.js";
import { DEPTH } from "../../test/lib/constants.js";

export const ROOT = path.join(path.dirname(fileURLToPath(import.meta.url)), "..", "..");
const LEAN_EXPECTED = path.join(ROOT, "lean", "expected");

/** Version tag carried by every published file; bump only on a shape change. */
export const SCHEMA = "lelantos.circuits.vectors/1";

export const s = (x: Field | number | bigint): string => x.toString();
export const pt = (p: Point) => ({ x: s(p[0]), y: s(p[1]) });
export const hex = (b: Uint8Array) => "0x" + Buffer.from(b).toString("hex");

/** keccak256 over the newline-joined slot names — one line that moves when the layout does. */
export function layoutDigest(layout: string[]): string {
    return hex(keccak_256(new TextEncoder().encode(layout.join("\n"))));
}

/**
 * The Lean model's layout dump.
 *
 * Read rather than regenerated: the vector file carries Lean's ordering to the
 * SDK, so deriving it here would break that chain.
 */
export function readLeanLayout(shape: string): string[] {
    const p = path.join(LEAN_EXPECTED, `layout-${shape}.txt`);
    if (!fs.existsSync(p)) {
        throw new Error(
            `missing ${p} — run 'just lean-update' so the Lean model publishes its layout first`,
        );
    }
    return fs.readFileSync(p, "utf8").trim().split("\n");
}

/** Stable stringify: 2-space indent. Returns the SHA-256 the index records. */
export function writeJson(file: string, value: unknown): string {
    const text = JSON.stringify(value, null, 2) + "\n";
    fs.writeFileSync(file, text);
    return createHash("sha256").update(text).digest("hex");
}

/**
 * Curve, field and tag values repeated in every vector file.
 *
 * Published so the SDK can check agreement on them before comparing derived
 * values; a mismatch here accounts for every downstream mismatch.
 */
export function sharedConstants(P: Poseidon, J: Jubjub) {
    const tree = new MerkleTree(P, DEPTH);
    return {
        bn254Fr: s(BN254_FR),
        babyjubSubgroupOrder: s(BABYJUB_SUBGROUP_ORDER),
        babyjubBase8: pt(J.base8),
        hBase: pt(H_BASE),
        tags: Object.fromEntries(Object.entries(TAGS).map(([k, v]) => [k, s(v)])),
        // depth+1 entries; also hardcoded as EMPTY_SUBTREE in src/lib/common.circom
        // and as CommitmentTree.EMPTY_ROOT (last entry) in the contracts repo.
        emptySubtree: tree.emptySubtree().map(s),
    };
}

/** The Fiat-Shamir pair plus the coefficients it was derived from. */
export interface Compression {
    coeffs: string[];
    abiEncodedCoeffs: string;
    zDerivation: "fiat-shamir";
    z: string;
    y: string;
}
