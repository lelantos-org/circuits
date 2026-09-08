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
// `layout_parity.test.ts` does this for the transact shapes, anchored on
// `lean/expected/layout-4x6.txt`. This file is the same for the batch, anchored
// on `lean/expected/layout-batch-8.txt` — dumped from `Lelantos.batchPiSlot` by
// `lean/scripts/dump-layout.sh`, the same definition the Lean batch proofs read
// their coefficients through.
//
// It did not always have that anchor. `lean/` modelled the batch's tree logic
// but not `BatchCompress`, so the only anchor available was the published
// vector's own `circuit.layout` — which the SDK and the contracts fixture also
// read, making a drift consistent everywhere and invisible. The vector is still
// checked, but now against Lean rather than against itself.
//
// The batch's layout has a property the transact one does not, and it is the
// whole reason this file exists: its challenge preimage and its coefficient
// vector are the SAME 52 words. Transact evaluates only 46 of its 69, and can,
// because the other 23 are not signals of `4x6.circom` at all. The batch has no
// such words — every one of its 52 is a signal — so evaluating all 52 is not a
// convenience but the only sound option, since hashing a signal into `z` binds
// nothing when the prover reads `z` before choosing the witness.
//
// Demoting three of them was tried and was exploitable, so the equality is
// asserted here word by word rather than left to a length check.

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(HERE, "../..");
const VECTOR_FILE = resolve(ROOT, "vectors/tree-update-batch-8.json");
const LEAN_LAYOUT_FILE = resolve(ROOT, `lean/expected/layout-batch-${MAX_L}.txt`);

// Coefficients and preimage are the same 52 words; that they are equal in the
// published vector is asserted below rather than assumed by using one constant
// for both of its fields.
const WORDS = 4 + 6 * MAX_L;

const vector = JSON.parse(readFileSync(VECTOR_FILE, "utf8"));
const layout: string[] = vector.circuit.layout;

/** The layout as Lean defines it, dumped by `lean/scripts/dump-layout.sh`. */
const leanLayout: string[] = readFileSync(LEAN_LAYOUT_FILE, "utf8")
    .split("\n")
    .map(l => l.trim())
    .filter(l => l.length > 0);

// Distinct sentinel per logical field, so a transposition shows up as a
// mismatch rather than coincidentally agreeing. Derived from the published slot
// NAMES; the transcription under test is `SENTINEL_INPUT` below, which assigns
// each sentinel to a field by hand — `flattenBatch` has to reproduce the
// published order from it.
const S = sentinels(layout, 1000, "batch_layout_parity");

const SENTINEL_INPUT = {
    old_root: S.at("oldRoot"),
    new_root: S.at("newRoot"),
    start_index: S.at("startIndex"),
    actual_count: S.at("actualCount"),
    cms: S.scalars("cms", MAX_L),
    cv_dep: S.points("cvDep", MAX_L),
    // Evaluated like everything else. Sentinels come from the same map because
    // unlike transact's challenge-only words these ARE slots of the published
    // layout — the preimage is what the layout describes, and here the
    // coefficients are the whole of it.
    leaf_asset: S.scalars("leafAsset", MAX_L),
    leaf_public_in: S.scalars("leafPublicIn", MAX_L),
    is_deposit: S.scalars("isDeposit", MAX_L),
};

/**
 * The trailing block: the deposit-binding fields, in layout order.
 *
 * Named because their placement is what has to stay checked. They are the words
 * that were once demoted to challenge-only, and the assertions below say they
 * are evaluated — the opposite claim, in the same terms, so a re-demotion reads
 * as a change to this file rather than a silent one.
 */
const DEPOSIT_BINDING_SLOTS = ["leafAsset", "leafPublicIn", "isDeposit"].flatMap(field =>
    Array.from({ length: MAX_L }, (_, i) => `${field} ${i}`),
);

describe("formal model / batch public-input layout parity", () => {
    it("the published layout is the one Lean defines", () => {
        // The anchor. Everything below checks the vector against `ref/compress`
        // and against itself; this is what ties the whole chain to a definition
        // outside the TypeScript, so a drift agreed on by the generator, the SDK
        // and the fixture still fails.
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
        // Contiguity is load-bearing on the contract side: `PubInputs.compress`
        // evaluates ONE span of the copied calldata (`_finalizeRaw(head, n,
        // nCoeffs)`) rather than gathering slots. Here that span is the entire
        // block.
        const c = batchCoeffs(SENTINEL_INPUT);
        const pre = flattenBatch(SENTINEL_INPUT);
        expect(c.length).to.equal(WORDS);
        expect(c).to.deep.equal(
            pre,
            "batchCoeffs and flattenBatch must produce the same words in the same order",
        );
    });

    it("the deposit-binding fields are the trailing block, and are evaluated", () => {
        // The assertion that would have caught the demotion. `leaf_asset`,
        // `leaf_public_in` and `is_deposit` are signals of the circuit, so a
        // prover can hand the verifier a witness whose copies disagree with the
        // calldata `z` was hashed from. Only evaluating them into `y` — plus the
        // constraint in step 7a that pins them where the binding degenerates —
        // closes that.
        //
        // Their POSITION is checked too: the contract re-masks the two uint64
        // blocks and the uint8 block by offset, so a reordering would clean the
        // wrong words.
        expect(layout.slice(4 + 3 * MAX_L)).to.deep.equal(
            DEPOSIT_BINDING_SLOTS,
            "the words after the cv_dep block must be exactly leafAsset, " +
                "leafPublicIn and isDeposit, in that order",
        );
    });

    it("nothing is challenge-only, and the vector says so", () => {
        // `challengeOnly` is what `reference.test.ts` drives its discharge check
        // from, and what a reader consults to know which words are unpinned. It
        // is written by the generator independently of `layout`, so the two can
        // disagree. An empty list is the claim that every word is pinned.
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
        // Computed with the generator's own function: what this pins is the
        // layout LIST, not the digest algorithm.
        expect(vector.circuit.layoutDigest).to.equal(
            layoutDigest(layout),
            "layoutDigest does not match circuit.layout — run `just vectors`",
        );
    });
});
