import { expect } from "chai";
import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import { flatten } from "@lelantos-org/sdk";

// Fidelity bridge: the Lean model's public-input layout vs. the SDK's.
//
// The 30-slot ordering exists in four places -- `TransactCompressN`
// (src/lib/poly_eval.circom:32), `PubInputs.sol :: compress(Transact, aux)`,
// `sdk/src/bundle/snark-compression.ts :: flatten`, and `Lelantos.piSlot`
// (lean/Lelantos/Circuit/Witness.lean). A transposition between any two of them silently
// breaks proof verification, and `PolyEval` binding is stated *about* this layout, so a
// wrong layout in Lean would make `transact_sound`'s compression clause meaningless.
//
// `lean/expected/layout-2x2.txt` is generated from the Lean definition by
// `lean/scripts/dump-layout.sh`, which also guards it against drift on the Lean side.
// This test closes the other side: it checks that file against the SDK's `flatten`.
//
// The circuit <-> SDK link is already covered by the PolyEval binding cases in
// transact.test.ts:645-729, so together the three checks pin all four implementations.

const HERE = dirname(fileURLToPath(import.meta.url));
const LAYOUT_FILE = resolve(HERE, "../../../lean/expected/layout-2x2.txt");

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
};

function leanLayout(): string[] {
    return readFileSync(LAYOUT_FILE, "utf8")
        .split("\n")
        .map((l) => l.trim())
        .filter((l) => l.length > 0);
}

describe("formal model / public-input layout parity", () => {
    it("the Lean layout file has exactly the 30 slots the circuit compresses", () => {
        const layout = leanLayout();
        expect(layout.length).to.equal(30);
        expect(new Set(layout).size).to.equal(30, "layout slot names must be distinct");
    });

    it("every Lean slot name has a sentinel (the test covers the whole layout)", () => {
        for (const name of leanLayout()) {
            expect(SENTINEL, `no sentinel for Lean slot "${name}"`).to.have.property(name);
        }
    });

    it("the SDK flattens into exactly the order the Lean model claims", () => {
        const layout = leanLayout();
        const coeffs = flatten(SENTINEL_INPUT);

        expect(coeffs.length).to.equal(
            layout.length,
            "SDK coefficient count differs from the Lean layout length",
        );

        layout.forEach((name, k) => {
            expect(coeffs[k]).to.equal(
                SENTINEL[name],
                `slot ${k}: Lean says "${name}" (${SENTINEL[name]}) but the SDK put ${coeffs[k]}`,
            );
        });
    });
});
