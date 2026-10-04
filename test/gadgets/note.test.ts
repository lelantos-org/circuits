// Unit tests for `lib/note.circom`: the key hierarchy, the note commitment,
// output-rho derivation and the nullifier.
//
// Two things are pinned here that the full-circuit suites cannot reach.
//
// First, the domain-separation tags. `lib/tags.circom` carries the TAG_* table
// and a comment requiring it to stay in sync with the SDK; the only automated
// check was that vectors built from `ref/tags.ts` verify. Each case below
// compares a compiled derivation against `ref/`, so a tag edited on one side
// alone fails here rather than at a consumer.
//
// Second, the range obligations. `NoteCommitment` packs asset_id and value into
// one field element and range-checks neither; the packing is only injective
// because `SpentNote`, `OutputNote` and `TreeUpdateBatch` apply RangeCheck64 to
// both first. The aliasing case below shows what the packing does without them.

import { expect } from "chai";

import {
    POW_2_64,
    buildInner,
    buildNoteCommitment,
    buildNullifier,
    commitWithInner,
    buildRho,
    deriveIvk,
    deriveNk,
    derivePkFromIvk,
    type Field,
} from "../helpers";
import { generatedFixture, readOutput } from "../lib/circuit";
import { expectAccepts } from "../lib/expect";
import { ALICE_NSK, BOB_NSK, TIMEOUT_CIRCUIT, TWO_64 } from "../lib/constants";
import { useCircuits } from "../lib/harness";

const NSKS: Field[] = [ALICE_NSK, BOB_NSK, 1n, 0xdead_beefn];

describe("note derivations (keys, commitment, rho, nullifier)", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useCircuits({
        ivk: generatedFixture("lib/note.circom", "DeriveIvk", []),
        nk: generatedFixture("lib/note.circom", "DeriveNk", []),
        pk: generatedFixture("lib/note.circom", "DerivePk", []),
        inner: generatedFixture("lib/note.circom", "NoteInner", []),
        cm: generatedFixture("lib/note.circom", "NoteCommitment", []),
        rho: generatedFixture("lib/note.circom", "DeriveRho", []),
        nf: generatedFixture("lib/note.circom", "Nullifier", []),
    });

    /** Single-output helper: witness the gadget and read its output. */
    async function out(
        which: "ivk" | "nk" | "pk" | "inner" | "cm" | "rho" | "nf",
        input: Record<string, string>,
    ): Promise<Field> {
        const circuit = ctx.circuits[which];
        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
        return readOutput(w);
    }

    const ivkOf = (nsk: Field) => out("ivk", { nsk: nsk.toString() });
    const nkOf = (nsk: Field) => out("nk", { nsk: nsk.toString() });
    const pkOf = (ivk: Field) => out("pk", { ivk: ivk.toString() });

    // ===== key hierarchy: nsk -> ivk -> pk, and nsk -> nk =====

    it("derives ivk, nk and pk exactly as the reference does", async () => {
        const { P } = ctx;
        for (const nsk of NSKS) {
            const ivk = await ivkOf(nsk);
            expect(ivk, `ivk(${nsk})`).to.equal(deriveIvk(P, nsk));
            expect(await nkOf(nsk), `nk(${nsk})`).to.equal(deriveNk(P, nsk));
            expect(await pkOf(ivk), `pk(${nsk})`).to.equal(derivePkFromIvk(P, ivk));
        }
    });

    // TAG_IVK, TAG_NK and TAG_PK are 4, 9 and 3. If two were equal, or a call
    // site read the wrong one, the derivations above would still agree with a
    // reference that shared the mistake — but two of these three values would
    // coincide, which is what this checks.
    it("separates the three derivations by tag, not by arity", async () => {
        for (const nsk of NSKS) {
            const [ivk, nk] = [await ivkOf(nsk), await nkOf(nsk)];
            expect(ivk, `ivk and nk collide at nsk ${nsk}`).to.not.equal(nk);
            // pk takes ivk, so compare it against the same argument, not nsk.
            expect(await pkOf(ivk), "pk(ivk) must not equal ivk").to.not.equal(ivk);
            expect(await pkOf(nk), "the tags must separate pk(nk) from pk(ivk)")
                .to.not.equal(await pkOf(ivk));
        }
    });

    it("gives different owners different pks", async () => {
        const alice = await pkOf(await ivkOf(ALICE_NSK));
        const bob = await pkOf(await ivkOf(BOB_NSK));
        expect(alice).to.not.equal(bob);
    });

    // ===== note commitment: inner, then cm =====

    const innerInput = (pk: Field, rho: Field, rcm: Field) => ({
        owner_pk: pk.toString(),
        rho: rho.toString(),
        rcm: rcm.toString(),
    });

    const cmInput = (asset: Field, value: Field, inner: Field) => ({
        asset_id: asset.toString(),
        value: value.toString(),
        inner: inner.toString(),
    });

    /** The two gadgets chained, as SpentNote and OutputNote chain them. */
    async function cmOf(asset: Field, value: Field, pk: Field, rho: Field, rcm: Field): Promise<Field> {
        return out("cm", cmInput(asset, value, await out("inner", innerInput(pk, rho, rcm))));
    }

    it("computes inner as the reference does", async () => {
        const { P } = ctx;
        const pk = await pkOf(await ivkOf(ALICE_NSK));
        expect(await out("inner", innerInput(pk, 5n, 6n))).to.equal(buildInner(P, { pk, rho: 5n, rcm: 6n }));
    });

    it("inner binds each of pk, rho and rcm", async () => {
        const pk = await pkOf(await ivkOf(ALICE_NSK));
        const base = await out("inner", innerInput(pk, 5n, 6n));
        for (const v of [innerInput(pk + 1n, 5n, 6n), innerInput(pk, 6n, 6n), innerInput(pk, 5n, 7n)]) {
            expect(await out("inner", v), `inner must change when ${JSON.stringify(v)} does`).to.not.equal(base);
        }
        // Not symmetric in rho and rcm: swapping them is a different note.
        expect(await out("inner", innerInput(pk, 6n, 5n))).to.not.equal(base);
    });

    it("commits the packed (asset, value) pair over inner as the reference does", async () => {
        const { P } = ctx;
        const cases: [Field, Field][] = [
            [1n, 0n],
            [7n, 1000n],
            [0xffff_ffff_ffff_ffffn, TWO_64 - 1n],
        ];
        for (const [asset, value] of cases) {
            expect(await out("cm", cmInput(asset, value, 0x1234n)), `cm(${asset}, ${value})`)
                .to.equal(commitWithInner(P, asset, value, 0x1234n));
        }
    });

    it("the chained gadgets give the reference note commitment", async () => {
        // The form SpentNote opens and the form tree_update_batch builds for a
        // deposit are this one value: cm over the note, and cm over the public
        // amount and the note's inner.
        const { P } = ctx;
        const pk = await pkOf(await ivkOf(ALICE_NSK));
        const note = { asset: 7n, value: 1000n, pk, rho: 5n, rcm: 6n };
        const cm = await cmOf(7n, 1000n, pk, 5n, 6n);
        expect(cm).to.equal(buildNoteCommitment(P, note));
        expect(cm).to.equal(commitWithInner(P, 7n, 1000n, buildInner(P, note)));
    });

    it("binds every field of the note", async () => {
        const pk = await pkOf(await ivkOf(ALICE_NSK));
        const base = await cmOf(7n, 1000n, pk, 5n, 6n);
        const variants: [Field, Field, Field, Field, Field][] = [
            [8n, 1000n, pk, 5n, 6n],
            [7n, 1001n, pk, 5n, 6n],
            [7n, 1000n, pk + 1n, 5n, 6n],
            [7n, 1000n, pk, 6n, 6n],
            [7n, 1000n, pk, 5n, 7n],
        ];
        for (const v of variants) {
            expect(await cmOf(...v), `cm must change when the note becomes ${v}`).to.not.equal(base);
        }
    });

    // TAG_CM and TAG_INNER lead their preimages. Arity alone separates most of
    // the sites, but cm shares arity 3 with DeriveRho and inner shares arity 4
    // with the nullifier, so those two pairs rest on the tag. With the same
    // trailing inputs each pair must still differ.
    it("separates cm from rho, and inner from the nullifier, by tag", async () => {
        const [a, b, c] = [0x111n, 0x222n, 0x333n];
        expect(await out("cm", { asset_id: "0", value: a.toString(), inner: b.toString() }))
            .to.not.equal(await out("rho", { nf0: a.toString(), index: b.toString() }));
        expect(await out("inner", innerInput(a, b, c)))
            .to.not.equal(await out("nf", { nk: a.toString(), rho: b.toString(), cm: c.toString() }));
    });

    // packed_av = asset_id·2^64 + value is injective only for value < 2^64.
    // The gadget range-checks neither field, so out of range the packing
    // aliases: (asset, 2^64) and (asset + 1, 0) hash identically. `SpentNote`,
    // `OutputNote` and `TreeUpdateBatch` apply RangeCheck64 to both fields
    // beside this template; `gadgets/note_slots.test.ts` and
    // `batch/deposit_binding.test.ts` show the out-of-range reading rejected
    // there. Recorded here so the obligation is visible at the gadget, and so a
    // future caller cannot assume the packing self-checks.
    it("aliases across the 2^64 boundary without the caller's RangeCheck64", async () => {
        const overflowed = await out("cm", cmInput(7n, POW_2_64, 0x1234n));
        const carried = await out("cm", cmInput(8n, 0n, 0x1234n));
        expect(overflowed, "packed_av collapses (7, 2^64) onto (8, 0)").to.equal(carried);
    });

    // ===== output rho =====

    it("derives rho from the first nullifier and the output index", async () => {
        const { P } = ctx;
        const nf0 = 0xc0ffeen;
        for (const index of [0n, 1n, 5n]) {
            expect(await out("rho", { nf0: nf0.toString(), index: index.toString() }))
                .to.equal(buildRho(P, nf0, index));
        }
    });

    it("gives each output slot a distinct rho", async () => {
        const nf0 = 0xc0ffeen;
        const seen = new Set<string>();
        for (let index = 0; index < 6; index++) {
            const rho = await out("rho", { nf0: nf0.toString(), index: index.toString() });
            expect(seen.has(rho.toString()), `rho repeats at index ${index}`).to.equal(false);
            seen.add(rho.toString());
        }
    });

    // ===== nullifier =====

    const nfInput = (nk: Field, rho: Field, cm: Field) => ({
        nk: nk.toString(),
        rho: rho.toString(),
        cm: cm.toString(),
    });

    it("computes nf as the reference does", async () => {
        const { P } = ctx;
        const nk = await nkOf(ALICE_NSK);
        expect(await out("nf", nfInput(nk, 5n, 0xabcn))).to.equal(buildNullifier(P, nk, 5n, 0xabcn));
    });

    // The faerie-gold defence: cm is in the preimage, so two notes that share
    // (nk, rho) still nullify separately and spending one cannot lock the other.
    it("separates two notes that share (nk, rho) but not cm", async () => {
        const nk = await nkOf(ALICE_NSK);
        const a = await out("nf", nfInput(nk, 5n, 0xaaan));
        const b = await out("nf", nfInput(nk, 5n, 0xbbbn));
        expect(a).to.not.equal(b);
    });

    it("separates two owners holding the same note contents", async () => {
        const alice = await nkOf(ALICE_NSK);
        const bob = await nkOf(BOB_NSK);
        expect(await out("nf", nfInput(alice, 5n, 0xabcn)))
            .to.not.equal(await out("nf", nfInput(bob, 5n, 0xabcn)));
    });

    // Nothing in this gadget is range-checked: it is a hash, and the ownership
    // and membership constraints that make the output meaningful live in
    // `SpentNote`. Pinned so a reader does not mistake the gadget for the check.
    it("hashes any field elements it is given", async () => {
        await expectAccepts(ctx.circuits.nf, nfInput(1n << 200n, 1n << 201n, 1n << 202n));
    });
});
