import { expect } from "chai";
import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import { layoutDigest } from "../../scripts/vectors/common";
import { sentinels } from "../lib/sentinels";

import { batchCoeffs, flattenBatch } from "../helpers";
import { MAX_L } from "../lib/constants";

// Public-input layout parity for `tree_update_batch`.
//
// The batch counterpart of `layout_parity.test.ts`, anchored on
// `lean/expected/layout-batch-8.txt`, which `lean/scripts/dump-layout.sh` dumps
// from `Lelantos.batchPiSlot`, the definition the Lean batch proofs read their
// coefficients through. The published vector is checked against Lean rather
// than against its own `circuit.layout`: the SDK and the contracts fixture read
// that layout too, so a drift in it would be consistent across consumers and
// otherwise undetected.
//
// Unlike transact, the batch's challenge preimage and coefficient vector are the
// same 52 words. Transact evaluates 46 of its 70 because the other 24 are not
// signals of `4x6.circom`. Every batch word is a signal, so evaluating all 52 is
// the only sound option: hashing a signal into `z` binds nothing when the prover
// knows `z` before choosing the witness. The equality is therefore asserted word
// by word rather than by length.

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(HERE, "../..");
const VECTOR_FILE = resolve(ROOT, "vectors/tree-update-batch-8.json");
const LEAN_LAYOUT_FILE = resolve(ROOT, `lean/expected/layout-batch-${MAX_L}.txt`);

// Coefficients and preimage are the same 52 words. The published vector's two
// count fields are each asserted against this constant below.
const WORDS = 4 + 6 * MAX_L;

const vector = JSON.parse(readFileSync(VECTOR_FILE, "utf8"));
const layout: string[] = vector.circuit.layout;

/** The layout as Lean defines it, dumped by `lean/scripts/dump-layout.sh`. */
const leanLayout: string[] = readFileSync(LEAN_LAYOUT_FILE, "utf8")
    .split("\n")
    .map(l => l.trim())
    .filter(l => l.length > 0);

// Distinct sentinel per logical field, so a transposition shows up as a
// mismatch. Derived from the published slot names; the transcription under test
// is `SENTINEL_INPUT` below, which assigns each sentinel to a field by hand, and
// `flattenBatch` must reproduce the published order from it.
const S = sentinels(layout, 1000, "batch_layout_parity");

const SENTINEL_INPUT = {
    old_root: S.at("oldRoot"),
    new_root: S.at("newRoot"),
    start_index: S.at("startIndex"),
    actual_count: S.at("actualCount"),
    cms: S.scalars("cms", MAX_L),
    cv_dep: S.points("cvDep", MAX_L),
    // Evaluated like every other word. Sentinels come from the same map
    // because, unlike transact's challenge-only words, these are slots of the
    // published layout, whose coefficients cover the whole preimage.
    leaf_asset: S.scalars("leafAsset", MAX_L),
    leaf_public_in: S.scalars("leafPublicIn", MAX_L),
    is_deposit: S.scalars("isDeposit", MAX_L),
};

/**
 * The trailing block: the deposit-binding fields, in layout order.
 *
 * Named so their placement stays checked. The assertions below state that these
 * words are evaluated, so making any of them challenge-only requires changing
 * this file.
 */
const DEPOSIT_BINDING_SLOTS = ["leafAsset", "leafPublicIn", "isDeposit"].flatMap(field =>
    Array.from({ length: MAX_L }, (_, i) => `${field} ${i}`),
);

describe("formal model / batch public-input layout parity", () => {
    it("the published layout is the one Lean defines", () => {
        // The anchor. The other cases check the vector against `ref/compress` and
        // against itself; this ties the chain to a definition outside TypeScript,
        // so a drift shared by the generator, the SDK and the fixture still fails.
        expect(layout).to.deep.equal(
            leanLayout,
            `vectors/tree-update-batch-8.json disagrees with ` +
                `lean/expected/layout-batch-${MAX_L}.txt — one of BatchCompress, ` +
                `Lelantos.batchPiSlot and ref/compress.ts has moved`,
        );
    });

    it("the published layout has exactly the words the circuit hashes", () => {
        expect(layout.length).to.equal(WORDS);
        expect(new Set(layout).size).to.equal(
            WORDS,
            "layout slot names must be distinct",
        );
        expect(vector.circuit.challengeWords).to.equal(WORDS);
        expect(vector.circuit.coeffCount).to.equal(WORDS);
    });

    it("ref/compress.ts orders the challenge preimage exactly as the vector claims", () => {
        const pre = flattenBatch(SENTINEL_INPUT);
        expect(pre.length).to.equal(layout.length);
        layout.forEach((name, k) => {
            expect(pre[k]).to.equal(
                S.map[name],
                `word ${k}: the vector says "${name}" (${S.map[name]}) but flattenBatch put ${pre[k]}`,
            );
        });
    });

    it("the coefficients are the whole preimage, word for word", () => {
        // The contract requires contiguity: `PubInputs.compress` evaluates one
        // span of the copied calldata (`_finalizeRaw(head, n, nCoeffs)`) rather
        // than gathering slots. Here that span is the entire block.
        const c = batchCoeffs(SENTINEL_INPUT);
        const pre = flattenBatch(SENTINEL_INPUT);
        expect(c.length).to.equal(WORDS);
        expect(c).to.deep.equal(
            pre,
            "batchCoeffs and flattenBatch must produce the same words in the same order",
        );
    });

    it("the deposit-binding fields are the trailing block, and are evaluated", () => {
        // `leaf_asset`, `leaf_public_in` and `is_deposit` are circuit signals, so
        // a prover can supply a witness whose copies disagree with the calldata
        // `z` was hashed from. Evaluating them into `y`, together with the step 6a
        // constraint that pins them where the binding degenerates, prevents that.
        //
        // Their position is checked too: the contract re-masks the two uint64
        // blocks and the uint8 block by offset, so a reordering would mask the
        // wrong words.
        expect(layout.slice(4 + 3 * MAX_L)).to.deep.equal(
            DEPOSIT_BINDING_SLOTS,
            "the words after the cv_dep block must be exactly leafAsset, " +
                "leafPublicIn and isDeposit, in that order",
        );
    });

    it("nothing is challenge-only, and the vector says so", () => {
        // `reference.test.ts` drives its discharge check from `challengeOnly`,
        // which lists the unpinned words. The generator writes it independently
        // of `layout`, so the two can disagree. An empty list states that every
        // word is pinned.
        expect(vector.circuit.challengeOnly).to.deep.equal(
            [],
            "a batch word that is hashed but not evaluated must be declared here, and " +
                "then needs a divergent-witness case in test/lib/batch.ts",
        );
        expect(vector.circuit.coeffCount).to.equal(
            vector.circuit.challengeWords,
            "the batch evaluates every word it hashes",
        );
    });

    it("layoutDigest matches the slot names it claims to digest", () => {
        // Computed with the generator's own function: this pins the layout list,
        // not the digest algorithm.
        expect(vector.circuit.layoutDigest).to.equal(
            layoutDigest(layout),
            "layoutDigest does not match circuit.layout — run `just vectors`",
        );
    });
});
