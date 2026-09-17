// Unit tests for the per-slot bundles: `OutputNote` (lib/output.circom) and
// `SpentNote` (lib/spent.circom).
//
// `transact_4x6` instantiates these N_OUT and N_IN times and adds conservation
// on top, so a rejection there is attributable to a slot only by elimination,
// and every case pays for a production-depth tree and a 100k-constraint
// witness. Driven directly at DEPTH = 2 a case is a four-leaf tree and a ~10k
// witness, which is what makes the dummy-bypass branches — the `(1 - is_dummy)`
// factors that the full-circuit suites can only reach through a padded
// bundle — worth enumerating.
//
// Several cases below assert that a slot ACCEPTS something: the dummy branch
// drops the pk, membership and asset checks, and nothing in `SpentNote` forces
// a dummy's value to zero. Those are the obligations `Transact` discharges with
// `DummyZeroValue` and `all_dummy`, recorded here so a reader of the gadget
// does not assume the slot is self-contained.

import { expect } from "chai";

import {
    MerkleTree,
    POW_2_64,
    buildLeaf,
    buildNoteCommitment,
    buildNullifierFromNsk,
    derivePk,
    pointJson,
    type Field,
    type Point,
} from "../helpers";
import { generatedFixture, readPoint } from "../lib/circuit";
import { expectAccepts, expectWitnessFails } from "../lib/expect";
import {
    ALICE_NSK,
    ARITY,
    MALLORY_NSK,
    TIMEOUT_CIRCUIT,
    TWO_252,
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
    rcv: Field;
    rcvDep: Field;
}

const NOTE: NoteFields = { asset: 7n, value: 1000n, rho: 5n, rcm: 6n, rcv: 77n, rcvDep: 88n };

/**
 * The signals both templates name identically, as circom reads them.
 *
 * `pk` is taken rather than derived: a spend proves ownership of the committed
 * pk, so several cases below declare one that no `nsk` produces.
 */
function noteFieldsJson(n: NoteFields, pk: Field) {
    return {
        asset_id: n.asset.toString(),
        value: n.value.toString(),
        pk: pk.toString(),
        rho: n.rho.toString(),
        rcm: n.rcm.toString(),
        rcv: n.rcv.toString(),
        rcv_dep: n.rcvDep.toString(),
    };
}

describe("OutputNote (one output slot)", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useCircuit(generatedFixture("lib/output.circom", "OutputNote", []));

    /** The honest witness for `n`, owned by ALICE. */
    function honest(n: NoteFields = NOTE) {
        const { P, J } = ctx;
        const pk = derivePk(P, ALICE_NSK);
        return {
            ...noteFieldsJson(n, pk),
            cm: buildNoteCommitment(P, { ...n, pk }).toString(),
            cv: pointJson(J.commit(n.asset, n.value, n.rcv)),
        };
    }

    it("accepts an honest note and exposes cv_dep for the leaf", async () => {
        const { J } = ctx;
        const w = await ctx.circuit.calculateWitness(honest(), true);
        await ctx.circuit.checkConstraints(w);
        const ref = J.commitPair(NOTE);
        // Outputs are rH[2] then cv_dep[2].
        expect(readPoint(w, 0), "rH").to.deep.equal(ref.rH);
        expect(readPoint(w, 2), "cv_dep").to.deep.equal(ref.cvDep);
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

    for (const half of [0, 1]) {
        it(`FAILS when cv[${half}] does not match the recomputed commitment`, async () => {
            const input = honest();
            input.cv = [...input.cv];
            input.cv[half] = (BigInt(input.cv[half]) + 1n).toString();
            await expectWitnessFails(ctx.circuit, input, "cv === vc.cv must reject");
        });
    }

    it("FAILS when cv was committed under a different blinder", async () => {
        const { J } = ctx;
        const input = honest();
        input.cv = pointJson(J.commit(NOTE.asset, NOTE.value, NOTE.rcv + 1n));
        await expectWitnessFails(ctx.circuit, input, "cv must be bound to rcv");
    });

    it("FAILS on asset_id 0, the ghost-note defence", async () => {
        // packed_av = asset_id·2^64 + value, so asset 0 would let a note's
        // commitment preimage start below 2^64 and collide with a tagged one.
        const input = honest();
        input.asset_id = "0";
        input.cm = buildNoteCommitment(ctx.P, {
            ...NOTE,
            asset: 0n,
            pk: derivePk(ctx.P, ALICE_NSK),
        }).toString();
        input.cv = pointJson(ctx.J.commit(0n, NOTE.value, NOTE.rcv));
        await expectWitnessFails(ctx.circuit, input, "asset_nz.out === 0 must reject asset 0");
    });

    it("FAILS when value reaches 2^64", async () => {
        // cm is recomputed over the out-of-range value, so the commitment
        // equality still holds and RangeCheck64 is the only thing left to
        // reject: `buildNoteCommitment` refuses the value, being bounded like
        // the circuit, so the packing is done here.
        const { P } = ctx;
        const pk = derivePk(P, ALICE_NSK);
        const input = honest();
        input.value = TWO_64.toString();
        input.cm = P.hash([NOTE.asset * POW_2_64 + TWO_64, pk, NOTE.rho, NOTE.rcm]).toString();
        await expectWitnessFails(ctx.circuit, input, "RangeCheck64 must reject", {
            template: "Num2Bits",
        });
    });

    it("FAILS when a blinder reaches 2^252", async () => {
        const wide = honest();
        wide.rcv = TWO_252.toString();
        await expectWitnessFails(ctx.circuit, wide, "MulH's Num2Bits must reject rcv", {
            template: "Num2Bits",
        });
        const wideDep = honest();
        wideDep.rcv_dep = TWO_252.toString();
        await expectWitnessFails(ctx.circuit, wideDep, "and rcv_dep", { template: "Num2Bits" });
    });

    // rcv_dep is not bound by any equality in this template: it is the caller's
    // leaf that pins it, through cv_dep. Changing it therefore moves cv_dep
    // rather than being rejected — which is what makes the deposit anchor a
    // binding commitment in `tree_update_batch`.
    it("moves cv_dep when rcv_dep changes, rather than rejecting", async () => {
        const input = honest();
        input.rcv_dep = (NOTE.rcvDep + 1n).toString();
        const w = await expectAccepts(ctx.circuit, input);
        expect(readPoint(w, 2)).to.deep.equal(
            ctx.J.commit(NOTE.asset, NOTE.value, NOTE.rcvDep + 1n),
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
        cvDep: Point;
    }

    /** Insert `n`'s leaf into a fresh tree and take its authentication path. */
    function plant(n: NoteFields, nsk: Field): Planted {
        const { P, J } = ctx;
        const pk = derivePk(P, nsk);
        const cm = buildNoteCommitment(P, { ...n, pk });
        const cvDep = J.commit(n.asset, n.value, n.rcvDep);
        const tree = new MerkleTree(P, DEPTH);
        // Two decoys first, so the note sits at a non-zero index and its path
        // carries real siblings rather than empty-subtree constants.
        tree.insert(0xdec0n);
        tree.insert(0xdec1n);
        const index = tree.insert(buildLeaf(P, cm, cvDep));
        const { pathElements, pathIndices } = tree.proof(index);
        return { root: tree.root(), pathElements, pathIndices, cvDep };
    }

    function honest(n: NoteFields = NOTE, nsk: Field = ALICE_NSK) {
        const { P, J } = ctx;
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
            cv: pointJson(J.commit(n.asset, n.value, n.rcv)),
        };
    }

    it("accepts an honest spend and exposes rH", async () => {
        const w = await expectAccepts(ctx.circuit, honest());
        expect(readPoint(w, 0)).to.deep.equal(ctx.J.commitPair(NOTE).rH);
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

    it("FAILS when the note's rcv_dep does not reproduce the inserted leaf", async () => {
        // cv_dep feeds the leaf hash, so a different deposit blinder recomputes
        // a leaf that is not in the tree: this is the binding that stops a
        // spend from restating a deposit's (asset, value).
        const input = honest();
        input.rcv_dep = (NOTE.rcvDep + 1n).toString();
        await expectWitnessFails(ctx.circuit, input, "the leaf must match the inserted one");
    });

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

    // ===== the dummy branch =====

    it("bypasses pk, membership and asset checks at is_dummy = 1", async () => {
        const { P, J } = ctx;
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
            cv: pointJson(J.commit(n.asset, n.value, n.rcv)),
        });
    });

    // A dummy still emits a real nullifier — that is what makes padding
    // indistinguishable on chain, and the contract inserts every one of them
    // into the spent set (src/README.md § 10.10).
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

    // The slot does not force a dummy's value to zero: `DummyZeroValue` in
    // `Transact` does (`transact/balance.test.ts` covers the rejection there).
    // Without that caller-side constraint a dummy could carry value into the
    // conservation sum while bypassing membership.
    it("does not itself force a dummy's value to zero", async () => {
        const input = honest();
        input.is_dummy = "1";
        await expectAccepts(ctx.circuit, input);
    });
});
