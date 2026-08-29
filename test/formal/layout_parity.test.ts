import { expect } from "chai";
import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import { keccak_256 } from "@noble/hashes/sha3";

import { flatten } from "../helpers";
import { N_IN, N_OUT } from "../lib/constants";

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
const ROOT = resolve(HERE, "../..");
const LAYOUT_FILE = resolve(ROOT, "lean/expected/layout-4x6.txt");

// Every shape that ships both a Lean layout dump and a published vector.
const SHIPPED_SHAPES = ["4x6"] as const;

const COEFF_COUNT = 9 + 3 * N_IN + 8 * N_OUT;

// Distinct sentinel per logical field, so any transposition shows up as a
// mismatch rather than coincidentally agreeing.
//
// Generated from the Lean layout's slot NAMES rather than hand-written, which is
// what lets this scale past the 31 slots of the old 2x2 shape to 4x6's 69. The
// independence the test needs is not in where the numbers come from — it is in
// `SENTINEL_INPUT` below, which assigns each sentinel to a field by name. That
// assignment is the transcription under test; `flatten` has to reproduce Lean's
// order from it.
const SENTINEL: Record<string, bigint> = Object.fromEntries(
    readLayout(LAYOUT_FILE).map((name, i) => [name, BigInt(1000 + i)]),
);

const S = SENTINEL;

/** `S[name]`, failing loudly rather than yielding `undefined` on a typo. */
function sentinel(name: string): bigint {
    const v = S[name];
    if (v === undefined) throw new Error(`layout_parity: no sentinel for slot "${name}"`);
    return v;
}

/** `[S["<field>X i"], S["<field>Y i"]]` for each of `n` slots. */
function points(field: string, n: number): bigint[][] {
    return Array.from({ length: n }, (_, i) => [
        sentinel(`${field}X ${i}`),
        sentinel(`${field}Y ${i}`),
    ]);
}

/** `[S["<field> 0"], …, S["<field> n-1"]]`. */
function scalars(field: string, n: number): bigint[] {
    return Array.from({ length: n }, (_, i) => sentinel(`${field} ${i}`));
}

const SENTINEL_INPUT = {
    merkle_root: sentinel("merkleRoot"),
    nullifier: scalars("nullifier", N_IN),
    out_cm: scalars("outCm", N_OUT),
    public_asset_id: sentinel("publicAssetId"),
    public_in: sentinel("publicIn"),
    public_out: sentinel("publicOut"),
    in_cv: points("inCv", N_IN),
    out_cv: points("outCv", N_OUT),
    recipient_address: sentinel("recipient"),
    chain_id: sentinel("chainId"),
    payer_address: sentinel("payer"),
    relayer_address: sentinel("relayer"),
    out_cv_dep: points("outCvDep", N_OUT),
    out_clue_Rx: scalars("clueRx", N_OUT),
    out_clue_Ry: scalars("clueRy", N_OUT),
    out_clue_bits: scalars("clueBits", N_OUT),
    out_aux_digest: sentinel("auxDigest"),
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
    it("the Lean layout file has exactly the slots the circuit compresses", () => {
        const layout = leanLayout();
        expect(layout.length).to.equal(COEFF_COUNT);
        expect(new Set(layout).size).to.equal(COEFF_COUNT, "layout slot names must be distinct");
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
