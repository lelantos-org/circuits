import { expect } from "chai";
import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import { coeffs as refCoeffs, flatten } from "../helpers";
import { N_IN, N_OUT } from "../lib/constants";
import { sentinels } from "../lib/sentinels";
import { layoutDigest } from "../../scripts/vectors/common";

// Public-input layout parity between the Lean model and `ref/compress.ts`.
//
// The slot ordering exists in four places: `TransactCompressN`
// (src/lib/poly_eval.circom), `PubInputs.sol :: compress(Transact, aux)`,
// `test/ref/compress.ts :: flatten`, and `Lelantos.piSlot`
// (lean/Lelantos/Circuit/Witness.lean). A transposition between any two breaks
// proof verification silently, and PolyEval binding is stated about this
// layout, so a wrong layout in Lean would empty `transact_sound`'s compression
// clause.
//
// `lean/expected/layout-4x6.txt` is generated from the Lean definition by
// `lean/scripts/dump-layout.sh`, which also guards it against drift on the Lean side.
// This test closes the other side: it checks that file against `ref/compress.ts`.
//
// `ref/compress.ts :: flatten` is also what `scripts/gen-vectors.ts` uses to
// produce `vectors/`, which the SDK consumes. The final case below pins the
// published vector's layout to the same Lean file, giving the chain:
//
//   Lelantos.piSlot -> layout-4x6.txt -> ref/flatten -> vectors/*.json -> SDK
//
// A Lean layout change therefore fails here, before a vector can be published.
//
// The circuit-to-ref link is covered by the PolyEval binding cases in
// test/transact/binding.test.ts, and by gen-vectors.ts refusing to write when
// the compiled circuit's `y` disagrees with the reference Horner evaluation.

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(HERE, "../..");
const LAYOUT_FILE = resolve(ROOT, "lean/expected/layout-4x6.txt");

// Every shape that ships both a Lean layout dump and a published vector.
const SHIPPED_SHAPES = ["4x6"] as const;

// The polynomial's slots, which is what the Lean model lays out.
const COEFF_COUNT = 4 + 3 * N_IN + 5 * N_OUT;

// The challenge preimage: a superset, adding the four address words, the clue
// triples and the aux digest. Those are logical public inputs bound through `z`
// rather than through `y`, so they are outside the Lean layout by construction —
// see `TRANSACT_COEFFS` in PubInputs.sol and `coeffs` in ref/compress.ts.
const CHALLENGE_WORDS = 9 + 3 * N_IN + 8 * N_OUT;

// Distinct sentinel per logical field, so any transposition shows up as a
// mismatch rather than coincidentally agreeing.
//
// Generated from the Lean layout's slot NAMES rather than hand-written. The
// independence the test needs is in `SENTINEL_INPUT` below, which assigns each
// sentinel to a field by name: that assignment is the transcription under test,
// and `flatten` has to reproduce Lean's order from it.
const S = sentinels(readLayout(LAYOUT_FILE), 1000, "layout_parity");

/**
 * Sentinels for the fields that are hashed but never evaluated.
 *
 * Separate from `S.map` because that one is derived from the Lean layout,
 * and these are exactly the names the Lean layout must NOT contain. Written out
 * rather than generated, so adding one back to the coefficient vector by mistake
 * fails the superset case below instead of silently regenerating.
 */
const CHALLENGE_ONLY = sentinels(
    [
        "recipient",
        "chainId",
        "payer",
        "relayer",
        "auxDigest",
        ...["clueRx", "clueRy", "clueBits"].flatMap((f) =>
            Array.from({ length: N_OUT }, (_, i) => `${f} ${i}`),
        ),
    ],
    // A second family in one test, which is what `base` is for: these must not
    // collide with the coefficient sentinels, or a word moving between the two
    // vectors would go unnoticed.
    9000,
    "layout_parity challenge-only",
);

const SENTINEL_INPUT = {
    merkle_root: S.at("merkleRoot"),
    nullifier: S.scalars("nullifier", N_IN),
    out_cm: S.scalars("outCm", N_OUT),
    public_asset_id: S.at("publicAssetId"),
    public_in: S.at("publicIn"),
    public_out: S.at("publicOut"),
    in_cv: S.points("inCv", N_IN),
    out_cv: S.points("outCv", N_OUT),
    out_cv_dep: S.points("outCvDep", N_OUT),
    // Hashed, never evaluated — hence sentinels from the other map.
    recipient_address: CHALLENGE_ONLY.at("recipient"),
    chain_id: CHALLENGE_ONLY.at("chainId"),
    payer_address: CHALLENGE_ONLY.at("payer"),
    relayer_address: CHALLENGE_ONLY.at("relayer"),
    out_clue_Rx: CHALLENGE_ONLY.scalars("clueRx", N_OUT),
    out_clue_Ry: CHALLENGE_ONLY.scalars("clueRy", N_OUT),
    out_clue_bits: CHALLENGE_ONLY.scalars("clueBits", N_OUT),
    out_aux_digest: CHALLENGE_ONLY.at("auxDigest"),
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

    it("the challenge preimage is a strict superset of the coefficients", () => {
        // The unconstrained fields must be hashed and not evaluated. Both halves
        // matter: dropping them from the preimage would leave a relayer free to
        // rewrite the recipient, and adding them back to the coefficients would
        // restore the free variables that made `y` forgeable.
        const c = refCoeffs(SENTINEL_INPUT);
        const pre = flatten(SENTINEL_INPUT);
        expect(c.length).to.equal(COEFF_COUNT);
        expect(pre.length).to.equal(CHALLENGE_WORDS);

        const inCoeffs = new Set(c);
        for (const [name, v] of Object.entries(CHALLENGE_ONLY.map)) {
            expect(inCoeffs.has(v), `${name} must not be a coefficient`).to.equal(false);
            expect(pre, `${name} must be a challenge word`).to.include(v);
        }
        for (const name of Object.keys(CHALLENGE_ONLY.map)) {
            expect(S.map, `"${name}" must not appear in the Lean layout`).to.not.have.property(
                name,
            );
        }
        for (const v of c) {
            expect(pre, "every coefficient must also be hashed into the challenge").to.include(v);
        }
    });

    it("every Lean slot name has a sentinel (the test covers the whole layout)", () => {
        for (const name of leanLayout()) {
            expect(S.map, `no sentinel for Lean slot "${name}"`).to.have.property(name);
        }
    });

    it("ref/compress.ts orders coefficients exactly as the Lean model claims", () => {
        const layout = leanLayout();
        const coeffs = refCoeffs(SENTINEL_INPUT);

        expect(coeffs.length).to.equal(
            layout.length,
            "ref coefficient count differs from the Lean layout length",
        );

        layout.forEach((name, k) => {
            expect(coeffs[k]).to.equal(
                S.map[name],
                `slot ${k}: Lean says "${name}" (${S.map[name]}) but ref/coeffs put ${coeffs[k]}`,
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
                4 + 3 * vector.circuit.shape.nIn + 5 * vector.circuit.shape.nOut,
                "coefficient count must equal 4 + 3·N_IN + 5·N_OUT",
            );
            expect(vector.circuit.challengeWords).to.equal(
                9 + 3 * vector.circuit.shape.nIn + 8 * vector.circuit.shape.nOut,
                "challenge preimage must equal 9 + 3·N_IN + 8·N_OUT",
            );

            // Computed with the generator's own function: what this pins is the
            // layout LIST, not the digest algorithm.
            expect(vector.circuit.layoutDigest).to.equal(
                layoutDigest(layout),
                "layoutDigest does not match the Lean slot names it claims to digest",
            );
        });
    }
});
