import { expect } from "chai";

import { layoutDigest } from "../../scripts/vectors/common";
import { readJson, readLines } from "../lib/files";
import { sentinels } from "../lib/sentinels";

import { batchCoeffs, flattenBatch } from "../helpers";
import { MAX_L } from "../lib/constants";

// Public-input layout parity for `tree_update_batch`: the published vector
// against `lean/expected/layout-batch-8.txt`, which
// `lean/scripts/dump-layout.sh` dumps from `Lelantos.batchPiSlot`. The SDK and
// the contracts fixture read the vector's `circuit.layout`, so a drift in it
// would be consistent across consumers and otherwise undetected.
//
// Every input word of the batch is a circuit signal, so every one of the 36 is
// evaluated. The challenge preimage is those 36 words followed by the digest
// word, which is hashed so that it is fixed before `z` and is compared by the
// verifier as a public signal rather than evaluated.


// The coefficients. The preimage is these plus the digest word.
const WORDS = 4 + 4 * MAX_L;
const CHALLENGE_WORDS = WORDS + 1;

/** A sentinel no layout slot uses, for the digest word. */
const DIGEST_SENTINEL = 9000n;

const vector = readJson("vectors/tree-update-batch-8.json");
const layout: string[] = vector.circuit.layout;

/** The layout as Lean defines it, dumped by `lean/scripts/dump-layout.sh`. */
const leanLayout: string[] = readLines(`lean/expected/layout-batch-${MAX_L}.txt`);

// Distinct sentinel per logical field, so a transposition shows up as a
// mismatch. `SENTINEL_INPUT` assigns each sentinel to a field by hand, and
// `flattenBatch` must reproduce the published order from it.
const S = sentinels(layout, 1000, "batch_layout_parity");

const SENTINEL_INPUT = {
    old_root: S.at("oldRoot"),
    new_root: S.at("newRoot"),
    start_index: S.at("startIndex"),
    actual_count: S.at("actualCount"),
    cms: S.scalars("cms", MAX_L),
    // Evaluated like every other word, so sentinels come from the same map.
    leaf_asset: S.scalars("leafAsset", MAX_L),
    leaf_public_in: S.scalars("leafPublicIn", MAX_L),
    is_deposit: S.scalars("isDeposit", MAX_L),
    digest: DIGEST_SENTINEL,
};

/** The trailing block: the deposit fields, in layout order. */
const DEPOSIT_BINDING_SLOTS = ["leafAsset", "leafPublicIn", "isDeposit"].flatMap(field =>
    Array.from({ length: MAX_L }, (_, i) => `${field} ${i}`),
);

describe("formal model / batch public-input layout parity", () => {
    it("the published layout is the one Lean defines", () => {
        // The anchor: the other cases check the vector against `ref/compress`
        // and against itself.
        expect(layout).to.deep.equal(
            leanLayout,
            `vectors/tree-update-batch-8.json disagrees with ` +
                `lean/expected/layout-batch-${MAX_L}.txt — one of BatchCompress, ` +
                `Lelantos.batchPiSlot and ref/compress.ts has moved`,
        );
    });

    it("the published layout has exactly the words the circuit evaluates", () => {
        expect(layout.length).to.equal(WORDS);
        expect(new Set(layout).size).to.equal(
            WORDS,
            "layout slot names must be distinct",
        );
        expect(vector.circuit.coeffCount).to.equal(WORDS);
        expect(vector.circuit.challengeWords).to.equal(CHALLENGE_WORDS);
    });

    it("ref/compress.ts orders the coefficients exactly as the vector claims", () => {
        const c = batchCoeffs(SENTINEL_INPUT);
        expect(c.length).to.equal(layout.length);
        layout.forEach((name, k) => {
            expect(c[k]).to.equal(
                S.map[name],
                `word ${k}: the vector says "${name}" (${S.map[name]}) but batchCoeffs put ${c[k]}`,
            );
        });
    });

    it("the preimage is the coefficients, word for word, then the digest word", () => {
        // The contract requires contiguity: `PubInputs.compress` evaluates one
        // span of the copied calldata (`_finalizeRaw(head, n, nCoeffs)`) rather
        // than gathering slots. Here that span is everything but the last word.
        const c = batchCoeffs(SENTINEL_INPUT);
        const pre = flattenBatch(SENTINEL_INPUT);
        expect(c.length).to.equal(WORDS);
        expect(pre.length).to.equal(CHALLENGE_WORDS);
        expect(pre.slice(0, WORDS)).to.deep.equal(
            c,
            "the coefficients must be the preimage's leading words, in order",
        );
        expect(pre[WORDS], "the digest word closes the preimage").to.equal(DIGEST_SENTINEL);
        expect(c, "the digest is not a coefficient").to.not.include(DIGEST_SENTINEL);
    });

    it("the deposit fields are the trailing block, and are evaluated", () => {
        // `leaf_asset`, `leaf_public_in` and `is_deposit` are circuit signals, so
        // a prover can supply a witness whose copies disagree with the calldata
        // `z` was hashed from; evaluating them into `y` prevents that. The
        // contract re-masks the two uint64 blocks and the uint8 block by offset,
        // so a reordering would mask the wrong words.
        expect(layout.slice(4 + MAX_L)).to.deep.equal(
            DEPOSIT_BINDING_SLOTS,
            "the words after the cms block must be exactly leafAsset, " +
                "leafPublicIn and isDeposit, in that order",
        );
    });

    it("the layout carries no value-commitment word", () => {
        expect(layout.filter(name => /cv/i.test(name))).to.deep.equal([]);
    });

    it("nothing is challenge-only, and the vector says so", () => {
        // `challengeOnly` lists the words bound through `z` alone. The generator
        // writes it independently of `layout`, so the two can disagree. The
        // digest word is not challenge-only: the verifier compares it as a
        // public signal.
        expect(vector.circuit.challengeOnly).to.deep.equal(
            [],
            "a batch word that is hashed but not evaluated must be declared here, and " +
                "then needs a divergent-witness case in test/lib/batch.ts",
        );
        expect(vector.circuit.challengeWords).to.equal(
            vector.circuit.coeffCount + 1,
            "the batch hashes every coefficient and the digest word, and nothing else",
        );
        expect(vector.circuit.publicSignals).to.deep.equal(["y", "digest", "z"]);
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
