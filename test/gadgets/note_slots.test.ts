// Unit tests for the per-slot bundles: `OutputNote` (lib/output.circom) and
// `SpentNote` (lib/spent.circom), the latter at DEPTH = 2.
//
// A dummy `SpentNote` drops the membership and asset checks and does not force
// its value to zero. `Transact` discharges those obligations with
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

// The diversifier the honest owner's pk is derived under: 128-bit, the width a
// wallet samples.
const D: Field = (1n << 127n) + 0xd1n;

/**
 * `cm` over a packed word the reference refuses to build. The hash equality
 * holds over the out-of-range field, so only the range check can reject.
 */
function cmOverPacked(P: Poseidon, packed: Field, n: NoteFields, pk: Field): Field {
    return P.hash([TAG_CM, packed, buildInner(P, { pk, rho: n.rho, rcm: n.rcm })]);
}

/** The signals both templates name identically, as circom reads them. */
function noteFieldsJson(n: NoteFields) {
    return {
        asset_id: n.asset.toString(),
        value: n.value.toString(),
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
        const pk = derivePk(P, ALICE_NSK, D);
        return {
            ...noteFieldsJson(n),
            // An output takes its owner key as an input; `SpentNote` derives it.
            pk: pk.toString(),
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
            pk: derivePk(P, MALLORY_NSK, D),
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
        const pk = derivePk(P, ALICE_NSK, D);
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
        const pk = derivePk(P, ALICE_NSK, D);
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
        const pk = derivePk(P, ALICE_NSK, D);
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
    function plant(n: NoteFields, nsk: Field, d: Field): Planted {
        const { P } = ctx;
        const pk = derivePk(P, nsk, d);
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

    /** The honest spend of `n`, held by `nsk` under the diversifier `d`. */
    function honest(n: NoteFields = NOTE, nsk: Field = ALICE_NSK, d: Field = D) {
        const { P } = ctx;
        const pk = derivePk(P, nsk, d);
        const cm = buildNoteCommitment(P, { ...n, pk });
        const planted = plant(n, nsk, d);
        return {
            ...noteFieldsJson(n),
            nsk: nsk.toString(),
            d: d.toString(),
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
            "a non-owner's nsk derives another pk, so the opened cm is not the leaf",
        );
    });

    // ===== the diversifier =====

    // d is not range-checked: zero, the 128-bit width a wallet samples, and
    // wider field elements all open the pk derived under them.
    for (const [label, d] of [
        ["0", 0n],
        ["1", 1n],
        ["2^128 - 1", (1n << 128n) - 1n],
        ["2^200", 1n << 200n],
    ] as const) {
        it(`accepts the spend of a note whose pk is derived under d = ${label}`, async () => {
            await expectAccepts(ctx.circuit, honest(NOTE, ALICE_NSK, d));
        });
    }

    it("gives one nsk a different pk, cm and nullifier under each diversifier", async () => {
        const { P } = ctx;
        const [a, b] = [honest(NOTE, ALICE_NSK, D), honest(NOTE, ALICE_NSK, D + 1n)];
        expect(derivePk(P, ALICE_NSK, D), "pk must depend on d").to.not.equal(
            derivePk(P, ALICE_NSK, D + 1n),
        );
        expect(a.root, "cm binds pk, so the leaf moves with d").to.not.equal(b.root);
        expect(a.nullifier, "the nullifier binds cm").to.not.equal(b.nullifier);
        await expectAccepts(ctx.circuit, a);
        await expectAccepts(ctx.circuit, b);
    });

    // The owner's nsk with the wrong diversifier derives another pk, and so
    // another cm. The nullifier is rebuilt over that cm, so membership is the
    // only constraint left to reject.
    for (const [label, wrong] of [
        ["d + 1", D + 1n],
        ["0", 0n],
        ["the pk itself", null],
    ] as const) {
        it(`FAILS when the witness d is ${label}, not the diversifier pk is derived under`, async () => {
            const { P } = ctx;
            const d = wrong ?? derivePk(P, ALICE_NSK, D);
            const input = honest();
            input.d = d.toString();
            const cm = buildNoteCommitment(P, { ...NOTE, pk: derivePk(P, ALICE_NSK, d) });
            input.nullifier = buildNullifierFromNsk(P, ALICE_NSK, NOTE.rho, cm).toString();
            await expectWitnessFails(
                ctx.circuit,
                input,
                "the cm opened under a wrong diversifier is not the inserted leaf",
            );
        });
    }

    it("FAILS when another nsk presents the owner's diversifier", async () => {
        const { P } = ctx;
        const input = honest();
        input.nsk = MALLORY_NSK.toString();
        // Nullifier rebuilt under the attacker's key and the cm it opens, so only
        // membership rejects.
        const cm = buildNoteCommitment(P, { ...NOTE, pk: derivePk(P, MALLORY_NSK, D) });
        input.nullifier = buildNullifierFromNsk(P, MALLORY_NSK, NOTE.rho, cm).toString();
        await expectWitnessFails(ctx.circuit, input, "knowing d does not open the pk without nsk");
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
            const pk = derivePk(P, ALICE_NSK, D);
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

    /** A dummy slot: asset 0, value 0, a path and root that authenticate nothing. */
    function dummy(d: Field, pk: Field = derivePk(ctx.P, ALICE_NSK, d)) {
        const { P } = ctx;
        const n: NoteFields = { ...NOTE, asset: 0n, value: 0n };
        const cm = buildNoteCommitment(P, { ...n, pk });
        return {
            ...noteFieldsJson(n),
            nsk: ALICE_NSK.toString(),
            d: d.toString(),
            path_elements: Array.from({ length: DEPTH }, (_, lvl) =>
                Array.from({ length: ARITY - 1 }, (_, k) => (0xbad0000 + lvl * 16 + k).toString())),
            path_indices: ["1", "2"],
            is_dummy: "1",
            root: "12345",
            nullifier: buildNullifierFromNsk(P, ALICE_NSK, n.rho, cm).toString(),
        };
    }

    it("bypasses membership and asset checks at is_dummy = 1", async () => {
        await expectAccepts(ctx.circuit, dummy(0n));
    });

    // d is not range-checked on any slot, so a dummy takes any field element.
    for (const [label, d] of [
        ["0", 0n],
        ["a 128-bit value", D],
        ["2^253", 1n << 253n],
    ] as const) {
        it(`accepts ${label} as d at is_dummy = 1`, async () => {
            await expectAccepts(ctx.circuit, dummy(d));
        });
    }

    // pk is derived on every slot, so a dummy's nullifier is over a cm its nsk
    // owns too.
    it("FAILS when a dummy's nullifier is built over a pk its nsk does not derive", async () => {
        await expectWitnessFails(
            ctx.circuit,
            dummy(0n, 0xdead_beefn),
            "the nullifier binds the cm of the derived pk on a dummy slot",
        );
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
            const cm = cmOverPacked(P, asset * POW_2_64, n, derivePk(P, ALICE_NSK, 0n));
            return {
                ...noteFieldsJson(n),
                nsk: ALICE_NSK.toString(),
                d: "0",
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
