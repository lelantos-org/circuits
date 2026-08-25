import { expect } from "chai";
import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import { keccak_256 } from "@noble/hashes/sha3";

import { flatten } from "../helpers";

// Public-input layout parity between the Lean model and `ref/compress.ts`.
//
// The 31-slot ordering exists in four places: `TransactCompressN`
// (src/lib/poly_eval.circom), `PubInputs.sol :: compress(Transact, aux)`,
// `src/test/ref/compress.ts :: flatten`, and `Lelantos.piSlot`
// (lean/Lelantos/Circuit/Witness.lean). A transposition between any two breaks
// proof verification silently, and PolyEval binding is stated about this
// layout, so a wrong layout in Lean would empty `transact_sound`'s compression
// clause.
//
// `lean/expected/layout-2x2.txt` is generated from the Lean definition by
// `lean/scripts/dump-layout.sh`, which also guards it against drift on the Lean side.
// This test closes the other side: it checks that file against `ref/compress.ts`.
//
// `ref/compress.ts :: flatten` is also what `scripts/gen-vectors.ts` uses to
// produce `vectors/`, which the SDK consumes. The final case below pins the
// published vector's layout to the same Lean file, giving the chain:
//
//   Lelantos.piSlot -> layout-2x2.txt -> ref/flatten -> vectors/*.json -> SDK
//
// A Lean layout change therefore fails here, before a vector can be published.
//
// The circuit-to-ref link is covered by the PolyEval binding cases in
// transact.test.ts, and by gen-vectors.ts refusing to write when the compiled
// circuit's `y` disagrees with the reference Horner evaluation.

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(HERE, "../../..");
const LAYOUT_FILE = resolve(ROOT, "lean/expected/layout-2x2.txt");

// Every shape that ships both a Lean layout dump and a published vector. The
// sentinel table below is 2x2-only (it is hand-written, one entry per slot), but
// the vector-carries-Lean check is shape-agnostic and covers all of them.
const SHIPPED_SHAPES = ["2x2", "3x3", "4x4"] as const;

// Distinct sentinel per logical field, so any transposition shows up as a mismatch
// rather than coincidentally agreeing.
const SENTINEL: Record<string, bigint> = {
    merkleRoot: 1000n,
    "nullifier 0": 1010n,
    "nullifier 1": 1011n,
    "outCm 0": 1020n,
    "outCm 1": 1021n,
    publicAssetId: 1030n,
    publicIn: 1031n,
    publicOut: 1032n,
    "inCvX 0": 1040n,
    "inCvY 0": 1041n,
    "inCvX 1": 1042n,
    "inCvY 1": 1043n,
    "outCvX 0": 1050n,
    "outCvY 0": 1051n,
    "outCvX 1": 1052n,
    "outCvY 1": 1053n,
    recipient: 1060n,
    chainId: 1061n,
    payer: 1062n,
    relayer: 1063n,
    "outCvDepX 0": 1070n,
    "outCvDepY 0": 1071n,
    "outCvDepX 1": 1072n,
    "outCvDepY 1": 1073n,
    "clueRx 0": 1080n,
    "clueRy 0": 1081n,
    "clueBits 0": 1082n,
    "clueRx 1": 1090n,
    "clueRy 1": 1091n,
    "clueBits 1": 1092n,
    auxDigest: 1100n,
};

const S = SENTINEL;

const SENTINEL_INPUT = {
    merkle_root: S["merkleRoot"],
    nullifier: [S["nullifier 0"], S["nullifier 1"]],
    out_cm: [S["outCm 0"], S["outCm 1"]],
    public_asset_id: S["publicAssetId"],
    public_in: S["publicIn"],
    public_out: S["publicOut"],
    in_cv: [
        [S["inCvX 0"], S["inCvY 0"]],
        [S["inCvX 1"], S["inCvY 1"]],
    ],
    out_cv: [
        [S["outCvX 0"], S["outCvY 0"]],
        [S["outCvX 1"], S["outCvY 1"]],
    ],
    recipient_address: S["recipient"],
    chain_id: S["chainId"],
    payer_address: S["payer"],
    relayer_address: S["relayer"],
    out_cv_dep: [
        [S["outCvDepX 0"], S["outCvDepY 0"]],
        [S["outCvDepX 1"], S["outCvDepY 1"]],
    ],
    out_clue_Rx: [S["clueRx 0"], S["clueRx 1"]],
    out_clue_Ry: [S["clueRy 0"], S["clueRy 1"]],
    out_clue_bits: [S["clueBits 0"], S["clueBits 1"]],
    out_aux_digest: S["auxDigest"],
};

function readLayout(file: string): string[] {
    return readFileSync(file, "utf8")
        .split("\n")
        .map((l) => l.trim())
        .filter((l) => l.length > 0);
}

function leanLayout(): string[] {
    return readLayout(LAYOUT_FILE);
}

describe("formal model / public-input layout parity", () => {
    it("the Lean layout file has exactly the 31 slots the circuit compresses", () => {
        const layout = leanLayout();
        expect(layout.length).to.equal(31);
        expect(new Set(layout).size).to.equal(31, "layout slot names must be distinct");
    });

    it("every Lean slot name has a sentinel (the test covers the whole layout)", () => {
        for (const name of leanLayout()) {
            expect(SENTINEL, `no sentinel for Lean slot "${name}"`).to.have.property(name);
        }
    });

    it("ref/compress.ts flattens into exactly the order the Lean model claims", () => {
        const layout = leanLayout();
        const coeffs = flatten(SENTINEL_INPUT);

        expect(coeffs.length).to.equal(
            layout.length,
            "ref coefficient count differs from the Lean layout length",
        );

        layout.forEach((name, k) => {
            expect(coeffs[k]).to.equal(
                SENTINEL[name],
                `slot ${k}: Lean says "${name}" (${SENTINEL[name]}) but ref/flatten put ${coeffs[k]}`,
            );
        });
    });

    // Carries the ordering across the package boundary: without it a published
    // vector could drift from the Lean model and the SDK would match the drift.
    for (const shape of SHIPPED_SHAPES) {
        it(`the published ${shape} vector carries the Lean layout verbatim`, () => {
            const layout = readLayout(resolve(ROOT, `lean/expected/layout-${shape}.txt`));
            const vector = JSON.parse(
                readFileSync(resolve(ROOT, `vectors/transact-${shape}.json`), "utf8"),
            );

            expect(vector.circuit.layout).to.deep.equal(
                layout,
                `vectors/transact-${shape}.json layout differs from ` +
                    `lean/expected/layout-${shape}.txt — run \`just lean-update\` then \`just vectors\``,
            );
            expect(vector.circuit.coeffCount).to.equal(layout.length);
            expect(vector.circuit.coeffCount).to.equal(
                9 + 3 * vector.circuit.shape.nIn + 8 * vector.circuit.shape.nOut,
                "coefficient count must equal 9 + 3·N_IN + 8·N_OUT",
            );

            const digest =
                "0x" +
                Buffer.from(keccak_256(new TextEncoder().encode(layout.join("\n")))).toString(
                    "hex",
                );
            expect(vector.circuit.layoutDigest).to.equal(
                digest,
                "layoutDigest does not match the Lean slot names it claims to digest",
            );
        });
    }
});
