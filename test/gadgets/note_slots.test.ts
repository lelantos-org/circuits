// Unit tests for the per-slot bundles: `OutputNote` (lib/output.circom) and
// `SpentNote` (lib/spent.circom), the latter at DEPTH = 2.
//
// A dummy `SpentNote` drops the pk, membership and asset checks and does not
// force its value to zero. `Transact` discharges those obligations with
// `DummyZeroValue` and `all_dummy`; without the former a dummy could carry
// value into the conservation sum while bypassing membership.

import { expect } from "chai";

import {
    MerkleTree,
    POW_2_64,
    TAG_CM,
    buildInner,
    buildNoteCommitment,
    buildNullifierFromNsk,
    derivePk,
    type Field,
    type Poseidon,
} from "../helpers";
import { generatedFixture } from "../lib/circuit";
import { expectAccepts, expectWitnessFails } from "../lib/expect";
import {
    ALICE_NSK,
    ARITY,
    MALLORY_NSK,
    TIMEOUT_CIRCUIT,
    TWO_64,
} from "../lib/constants";
import { useCircuit } from "../lib/harness";

const DEPTH = 2;

/** A note's fields, as both slot templates take them. */
interface NoteFields {
    asset: Field;
    value: Field;
    rho: Field;
    rcm: Field;
}

const NOTE: NoteFields = { asset: 7n, value: 1000n, rho: 5n, rcm: 6n };

/**
 * `cm` over a packed word the reference refuses to build. The hash equality
 * holds over the out-of-range field, so only the range check can reject.
 */
function cmOverPacked(P: Poseidon, packed: Field, n: NoteFields, pk: Field): Field {
    return P.hash([TAG_CM, packed, buildInner(P, { pk, rho: n.rho, rcm: n.rcm })]);
}

/**
 * The signals both templates name identically, as circom reads them. `pk` is
 * taken rather than derived, so a case can declare one that no `nsk` produces.
 */
function noteFieldsJson(n: NoteFields, pk: Field) {
    return {
        asset_id: n.asset.toString(),
        value: n.value.toString(),
        pk: pk.toString(),
        rho: n.rho.toString(),
        rcm: n.rcm.toString(),
    };
}

describe("OutputNote (one output slot)", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useCircuit(generatedFixture("lib/output.circom", "OutputNote", []));

    /** The honest witness for `n`, owned by ALICE. */
    function honest(n: NoteFields = NOTE) {
        const { P } = ctx;
        const pk = derivePk(P, ALICE_NSK);
        return {
            ...noteFieldsJson(n, pk),
            cm: buildNoteCommitment(P, { ...n, pk }).toString(),
        };
    }

    it("accepts an honest note", async () => {
        await expectAccepts(ctx.circuit, honest());
    });

    it("accepts a zero-value padding note", async () => {
        await expectAccepts(ctx.circuit, honest({ ...NOTE, value: 0n }));
    });

    it("FAILS when cm is not the commitment to these fields", async () => {
        const input = honest();
        input.cm = (BigInt(input.cm) + 1n).toString();
        await expectWitnessFails(ctx.circuit, input, "cm_h.cm === cm must reject");
    });

    it("FAILS when cm was committed under a different owner", async () => {
        const { P } = ctx;
        const input = honest();
        input.cm = buildNoteCommitment(P, {
            ...NOTE,
            pk: derivePk(P, MALLORY_NSK),
        }).toString();
        await expectWitnessFails(ctx.circuit, input, "the declared pk must be the committed one");
    });

    for (const [field, other] of [
        ["asset", { ...NOTE, asset: NOTE.asset + 1n }],
        ["value", { ...NOTE, value: NOTE.value + 1n }],
        ["rho", { ...NOTE, rho: NOTE.rho + 1n }],
        ["rcm", { ...NOTE, rcm: NOTE.rcm + 1n }],
    ] as const) {
        it(`FAILS when cm was committed under a different ${field}`, async () => {
            const input = honest();
            input.cm = honest(other).cm;
            await expectWitnessFails(ctx.circuit, input, `cm must bind ${field}`);
        });
    }

    it("FAILS on asset_id 0", async () => {
        // Id 0 means "no asset": the transparent bucket of a transfer names it.
        // cm is recomputed for asset 0, so only the non-zero check rejects.
        const input = honest({ ...NOTE, asset: 0n });
        await expectWitnessFails(ctx.circuit, input, "asset_nz.out === 0 must reject asset 0");
    });

    it("FAILS when value reaches 2^64", async () => {
        const { P } = ctx;
        const pk = derivePk(P, ALICE_NSK);
        const input = honest();
        input.value = TWO_64.toString();
        input.cm = cmOverPacked(P, NOTE.asset * POW_2_64 + TWO_64, NOTE, pk).toString();
        await expectWitnessFails(ctx.circuit, input, "RangeCheck64 must reject", {
            template: "Num2Bits",
        });
    });

    it("FAILS when asset_id reaches 2^64", async () => {
        // The asset bound keeps (asset, value) -> packed injective from above.
        const { P } = ctx;
        const pk = derivePk(P, ALICE_NSK);
        const input = honest();
        input.asset_id = TWO_64.toString();
        input.cm = cmOverPacked(P, TWO_64 * POW_2_64 + NOTE.value, NOTE, pk).toString();
        await expectWitnessFails(ctx.circuit, input, "RangeCheck64 must reject the asset id", {
            template: "Num2Bits",
        });
    });

    it("the two readings of one packed word cannot both be proved", async () => {
        // (asset 7, value 2^64) and (asset 8, value 0) pack to the same word and
        // so share a cm. Only the in-range reading is accepted.
        const { P } = ctx;
        const pk = derivePk(P, ALICE_NSK);
        const inRange = honest({ ...NOTE, asset: 8n, value: 0n });
        expect(inRange.cm).to.equal(cmOverPacked(P, 7n * POW_2_64 + TWO_64, NOTE, pk).toString());
        await expectAccepts(ctx.circuit, inRange);
        await expectWitnessFails(
            ctx.circuit,
            { ...inRange, asset_id: "7", value: TWO_64.toString() },
            "the out-of-range reading of the same cm must be rejected",
        );
    });
});

describe("SpentNote (one input slot, DEPTH = 2)", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useCircuit(generatedFixture("lib/spent.circom", "SpentNote", [DEPTH]));

    interface Planted {
        root: Field;
        pathElements: Field[][];
        pathIndices: number[];
    }

    /** Insert `n`'s commitment into a fresh tree and take its authentication path. */
    function plant(n: NoteFields, nsk: Field): Planted {
        const { P } = ctx;
        const pk = derivePk(P, nsk);
        const cm = buildNoteCommitment(P, { ...n, pk });
        const tree = new MerkleTree(P, DEPTH);
        // Two decoys first, so the note sits at a non-zero index and its path
        // carries real siblings rather than empty-subtree constants.
        tree.insert(0xdec0n);
        tree.insert(0xdec1n);
        const index = tree.insert(cm);
        const { pathElements, pathIndices } = tree.proof(index);
        return { root: tree.root(), pathElements, pathIndices };
    }

    function honest(n: NoteFields = NOTE, nsk: Field = ALICE_NSK) {
        const { P } = ctx;
        const pk = derivePk(P, nsk);
        const cm = buildNoteCommitment(P, { ...n, pk });
        const planted = plant(n, nsk);
        return {
            ...noteFieldsJson(n, pk),
            nsk: nsk.toString(),
            path_elements: planted.pathElements.map(lvl => lvl.map(String)),
            path_indices: planted.pathIndices.map(String),
            is_dummy: "0",
            root: planted.root.toString(),
            nullifier: buildNullifierFromNsk(P, nsk, n.rho, cm).toString(),
        };
    }

    it("accepts an honest spend", async () => {
        await expectAccepts(ctx.circuit, honest());
    });

    it("FAILS when nsk does not derive the committed pk", async () => {
        const input = honest();
        input.nsk = MALLORY_NSK.toString();
        await expectWitnessFails(
            ctx.circuit,
            input,
            "(1 - is_dummy) * (pk_check.pk - pk) === 0 must reject a non-owner",
        );
    });

    it("FAILS on a perturbed sibling", async () => {
        const input = honest();
        input.path_elements = input.path_elements.map(lvl => lvl.slice());
        input.path_elements[0][0] = (BigInt(input.path_elements[0][0]) + 1n).toString();
        await expectWitnessFails(ctx.circuit, input, "the leaf must authenticate against root");
    });

    it("FAILS on a declared root the path does not reach", async () => {
        const input = honest();
        input.root = (BigInt(input.root) + 1n).toString();
        await expectWitnessFails(ctx.circuit, input, "the recomputed root must equal root");
    });

    it("FAILS on a forged nullifier", async () => {
        const input = honest();
        input.nullifier = (BigInt(input.nullifier) + 1n).toString();
        await expectWitnessFails(ctx.circuit, input, "nf_h.nf === nullifier must reject");
    });

    // The leaf is cm, so a spend that restates the note's asset or value opens a
    // commitment that is not in the tree. The nullifier is recomputed over the
    // restated cm, so membership is the only constraint left to reject.
    for (const [field, restated] of [
        ["value", { ...NOTE, value: NOTE.value + 1n }],
        ["asset", { ...NOTE, asset: NOTE.asset + 1n }],
    ] as const) {
        it(`FAILS when the spend restates the note's ${field}, nullifier consistent`, async () => {
            const { P } = ctx;
            const pk = derivePk(P, ALICE_NSK);
            const input = honest();
            input.asset_id = restated.asset.toString();
            input.value = restated.value.toString();
            const cm = buildNoteCommitment(P, { ...restated, pk });
            input.nullifier = buildNullifierFromNsk(P, ALICE_NSK, restated.rho, cm).toString();
            await expectWitnessFails(ctx.circuit, input, `the restated ${field} must not open the inserted leaf`);
        });
    }

    it("FAILS on asset_id 0 for a real note", async () => {
        const zeroAsset = { ...NOTE, asset: 0n };
        const input = honest(zeroAsset);
        await expectWitnessFails(
            ctx.circuit,
            input,
            "(1 - is_dummy) * asset_nz.out === 0 must reject asset 0",
        );
    });

    it("FAILS when value reaches 2^64", async () => {
        const input = honest();
        input.value = TWO_64.toString();
        await expectWitnessFails(ctx.circuit, input, "RangeCheck64 must reject", {
            template: "Num2Bits",
        });
    });

    it("FAILS when asset_id reaches 2^64", async () => {
        const input = honest();
        input.asset_id = TWO_64.toString();
        await expectWitnessFails(ctx.circuit, input, "RangeCheck64 must reject the asset id", {
            template: "Num2Bits",
        });
    });

    // ===== the dummy branch =====

    it("bypasses pk, membership and asset checks at is_dummy = 1", async () => {
        const { P } = ctx;
        const n: NoteFields = { ...NOTE, asset: 0n, value: 0n };
        const pk = 0xdead_beefn; // not derived from any nsk
        const cm = buildNoteCommitment(P, { ...n, pk });
        await expectAccepts(ctx.circuit, {
            ...noteFieldsJson(n, pk),
            nsk: ALICE_NSK.toString(),
            path_elements: Array.from({ length: DEPTH }, (_, d) =>
                Array.from({ length: ARITY - 1 }, (_, k) => (0xbad0000 + d * 16 + k).toString())),
            path_indices: ["1", "2"],
            is_dummy: "1",
            root: "12345",
            nullifier: buildNullifierFromNsk(P, ALICE_NSK, n.rho, cm).toString(),
        });
    });

    // A dummy emits a real nullifier, which makes padding indistinguishable on
    // chain; the contract inserts each one into the spent set
    // (src/README.md § 10.10).
    it("still binds the nullifier for a dummy slot", async () => {
        const input = honest();
        input.is_dummy = "1";
        input.nullifier = (BigInt(input.nullifier) + 1n).toString();
        await expectWitnessFails(
            ctx.circuit,
            input,
            "the nullifier is bound in both branches",
        );
    });

    it("still range-checks a dummy's value", async () => {
        const input = honest();
        input.is_dummy = "1";
        input.value = TWO_64.toString();
        await expectWitnessFails(ctx.circuit, input, "RangeCheck64 applies to dummies too", {
            template: "Num2Bits",
        });
    });

    it("still range-checks a dummy's asset id, with cm and nullifier consistent", async () => {
        // Nothing but the range check reads a dummy's asset id, so the rejection
        // is isolated by rebuilding cm and the nullifier around the oversized
        // id. The accepted control is the largest id in range.
        const { P } = ctx;
        const dummyAt = (asset: Field) => {
            const n: NoteFields = { ...NOTE, asset, value: 0n };
            const cm = cmOverPacked(P, asset * POW_2_64, n, 0n);
            return {
                ...noteFieldsJson(n, 0n),
                nsk: ALICE_NSK.toString(),
                path_elements: Array.from({ length: DEPTH }, () => ["0", "0", "0"]),
                path_indices: ["0", "0"],
                is_dummy: "1",
                root: "0",
                nullifier: buildNullifierFromNsk(P, ALICE_NSK, n.rho, cm).toString(),
            };
        };
        await expectAccepts(ctx.circuit, dummyAt(TWO_64 - 1n));
        await expectWitnessFails(ctx.circuit, dummyAt(TWO_64), "RangeCheck64 on asset_id applies to dummies too", {
            template: "Num2Bits",
        });
    });

    it("does not itself force a dummy's value to zero", async () => {
        const input = honest();
        input.is_dummy = "1";
        await expectAccepts(ctx.circuit, input);
    });
});
