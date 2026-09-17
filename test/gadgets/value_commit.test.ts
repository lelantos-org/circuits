// Unit tests for `lib/value_commit.circom`: the commitment pair every note
// slot builds, the fixed-base blinding multiple, and the Edwards accumulator
// the balance check folds with.
//
// The production circuits reach these only through `SpentNote` / `OutputNote`,
// where a wrong point surfaces as a failed equality against a cv the witness
// also supplies — the same rejection a wrong blinder gives. Driving the gadget
// directly compares the point itself against the reference, so a window bug
// that happens to be self-consistent is visible.
//
// `ValueScalarMul` is the caller-constrained half: it takes raw bits, so the
// tests below record which booleanity obligations sit with the caller rather
// than with this file's templates.

import { expect } from "chai";

import {
    EDWARDS_IDENTITY,
    H_BASE,
    negatePoint,
    pointJson,
    pointsJson,
    type Field,
    type Point,
} from "../helpers";
import { generatedFixture, readPoint } from "../lib/circuit";
import { expectAccepts, expectWitnessFails } from "../lib/expect";
import { scalarBits } from "../lib/inputs";
import { RCV_BITS, TIMEOUT_CIRCUIT, TWO_252, TWO_64 } from "../lib/constants";
import { useCircuit } from "../lib/harness";

describe("ValueCommitPair (cv, cv_dep and their blinding multiples)", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useCircuit(generatedFixture("lib/value_commit.circom", "ValueCommitPair", []));

    function input(value: Field, gen: Point, rcv: Field, rcvDep: Field) {
        return {
            bits: scalarBits(value, 64),
            gen: pointJson(gen),
            rcv: rcv.toString(),
            rcv_dep: rcvDep.toString(),
        };
    }

    /**
     * Witness for one commitment pair, with all four outputs checked against
     * the reference.
     *
     * Outputs are read by name: `cv`, `rH`, `cv_dep`, `rH_dep`.
     */
    async function expectPair(value: Field, asset: Field, rcv: Field, rcvDep: Field): Promise<void> {
        const { J, circuit } = ctx;
        const gen = J.hashToAssetGen(asset);
        const w = await circuit.calculateWitness(input(value, gen, rcv, rcvDep), true);
        await circuit.checkConstraints(w);
        // `commitPair` is the reference mirror of this very template, so all
        // four outputs are compared against one derivation rather than four.
        const ref = J.commitPair({ asset, value, rcv, rcvDep });
        await circuit.assertOut(w, {
            cv: pointJson(ref.cv),
            rH: pointJson(ref.rH),
            cv_dep: pointJson(ref.cvDep),
            // Computed but consumed by nothing: `SpentNote` and `OutputNote`
            // forward `rH` only (grep `rH_dep` under src/). Pinned here so the
            // signal is either used or deleted deliberately.
            rH_dep: pointJson(ref.rHDep),
        });
    }

    it("matches the reference commitment on ordinary notes", async () => {
        await expectPair(1000n, 11n, 7n, 9n);
        await expectPair(1n, 1n, 123456789n, 987654321n);
        await expectPair(0xdead_beefn, 0xffff_ffff_ffff_ffffn, 1n << 200n, (1n << 251n) + 7n);
    });

    it("commits value 0 to the blinder alone, so cv == rH", async () => {
        const { J, circuit } = ctx;
        const gen = J.hashToAssetGen(11n);
        const w = await circuit.calculateWitness(input(0n, gen, 7n, 9n), true);
        const rH = J.mulPointEscalar(H_BASE, 7n);
        expect(readPoint(w, 0)).to.deep.equal(rH, "cv at value 0 must be rcv·H");
        expect(readPoint(w, 2)).to.deep.equal(rH);
    });

    it("commits blinder 0 to value·gen, with rH at the identity", async () => {
        const { J, circuit } = ctx;
        const gen = J.hashToAssetGen(11n);
        const w = await circuit.calculateWitness(input(1000n, gen, 0n, 0n), true);
        expect(readPoint(w, 0)).to.deep.equal(J.mulPointEscalar(gen, 1000n));
        expect(readPoint(w, 2)).to.deep.equal(EDWARDS_IDENTITY, "rH at rcv 0 must be the identity");
    });

    it("accepts the value and blinder ceilings", async () => {
        await expectPair(TWO_64 - 1n, 11n, TWO_252 - 1n, TWO_252 - 1n);
    });

    it("FAILS when a blinder reaches 2^252", async () => {
        const gen = ctx.J.hashToAssetGen(11n);
        await expectWitnessFails(
            ctx.circuit,
            input(1n, gen, TWO_252, 1n),
            `MulH's Num2Bits(${RCV_BITS}) must reject a wider blinder`,
            { template: "Num2Bits" },
        );
        await expectWitnessFails(
            ctx.circuit,
            input(1n, gen, 1n, TWO_252),
            "the deposit blinder is range-checked by its own MulH",
            { template: "Num2Bits" },
        );
    });

    // `ValueScalarMul` takes `bits` raw, so booleanity is the caller's job:
    // `SpentNote` and `OutputNote` feed it `RangeCheck64.bits`, which is a
    // Num2Bits output. Recorded here so the obligation is visible where the
    // gadget is read, not only where it is instantiated.
    it("does not itself constrain its bits to be boolean", async () => {
        const gen = ctx.J.hashToAssetGen(11n);
        const bits = scalarBits(1n, 64);
        bits[3] = "2";
        await expectAccepts(ctx.circuit, {
            bits,
            gen: pointJson(gen),
            rcv: "7",
            rcv_dep: "9",
        });
    });
});

describe("MulH (fixed-base blinding multiple)", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useCircuit(generatedFixture("lib/value_commit.circom", "MulH", []));

    async function expectH(scalar: Field): Promise<Point> {
        const w = await ctx.circuit.calculateWitness({ scalar: scalar.toString() }, true);
        await ctx.circuit.checkConstraints(w);
        const out = readPoint(w);
        expect(out).to.deep.equal(
            scalar === 0n ? EDWARDS_IDENTITY : ctx.J.mulPointEscalar(H_BASE, scalar),
            `rcv·H mismatch at ${scalar}`,
        );
        return out;
    }

    it("matches the reference across the blinder range", async () => {
        for (const s of [0n, 1n, 2n, 15n, 16n, 0xffff_ffffn, 1n << 128n, TWO_252 - 1n]) {
            await expectH(s);
        }
    });

    it("is additively homomorphic below the ceiling", async () => {
        const a = 0x1234_5678_9abc_def0n;
        const b = 0x0fed_cba9_8765_4321n;
        const [pa, pb, pab] = [await expectH(a), await expectH(b), await expectH(a + b)];
        expect(ctx.J.addPoint(pa, pb)).to.deep.equal(pab);
    });

    it("lands in the prime-order subgroup", async () => {
        for (const s of [1n, 0xc0ffeen, TWO_252 - 1n]) {
            expect(ctx.J.inSubgroup(await expectH(s))).to.equal(true);
        }
    });

    it("FAILS at 2^252", async () => {
        await expectWitnessFails(
            ctx.circuit,
            { scalar: TWO_252.toString() },
            `Num2Bits(${RCV_BITS}) must reject a 253-bit blinder`,
            { template: "Num2Bits" },
        );
    });
});

describe("PointSum (Edwards accumulator)", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    // 11 = N_IN + 1 + N_OUT, the width `PerAssetPointBalance(4, 6)` folds.
    const N = 11;
    const many = useCircuit(generatedFixture("lib/value_commit.circom", "PointSum", [N]));
    const one = useCircuit(generatedFixture("lib/value_commit.circom", "PointSum", [1]));

    const input = (pts: Point[]) => ({ pts: pointsJson(pts) });

    /** `k·H` for k = 1..N, a spread of distinct subgroup points. */
    function points(J: typeof many.J, count = N): Point[] {
        return Array.from({ length: count }, (_, i) => J.mulPointEscalar(H_BASE, BigInt(i + 1)));
    }

    async function sum(pts: Point[]): Promise<Point> {
        const w = await many.circuit.calculateWitness(input(pts), true);
        await many.circuit.checkConstraints(w);
        return readPoint(w);
    }

    it("folds 11 points in the same order as the reference", async () => {
        const { J } = many;
        const pts = points(J);
        const expected = pts.reduce((acc, p) => J.addPoint(acc, p), EDWARDS_IDENTITY);
        expect(await sum(pts)).to.deep.equal(expected);
        // (1 + 2 + ... + 11)·H, since every term is a multiple of one base.
        expect(expected).to.deep.equal(J.mulPointEscalar(H_BASE, 66n));
    });

    it("is order-independent, which is what lets the balance sides be listed separately", async () => {
        const pts = points(many.J);
        const rotated = [...pts.slice(4), ...pts.slice(0, 4)];
        expect(await sum(rotated)).to.deep.equal(await sum(pts));
    });

    it("absorbs identity terms, so padding slots are neutral", async () => {
        const { J } = many;
        const real = points(J, 3);
        const padded = [...real, ...Array<Point>(N - 3).fill(EDWARDS_IDENTITY)];
        expect(await sum(padded)).to.deep.equal(J.mulPointEscalar(H_BASE, 6n));
    });

    it("cancels a point against its negation", async () => {
        const { J } = many;
        const p = J.mulPointEscalar(H_BASE, 0xc0ffeen);
        const pts = [p, negatePoint(p), ...Array<Point>(N - 2).fill(EDWARDS_IDENTITY)];
        expect(await sum(pts)).to.deep.equal(EDWARDS_IDENTITY);
    });

    it("passes a single point through unchanged", async () => {
        const { J } = one;
        const p = J.mulPointEscalar(H_BASE, 5n);
        const w = await one.circuit.calculateWitness(input([p]), true);
        expect(readPoint(w)).to.deep.equal(p);
    });

    // BabyAdd is the complete Edwards addition law, so an off-curve input does
    // not fail here; `tree_update_batch` adds an explicit BabyCheck on the one
    // point it takes from the caller (`batch/deposit_binding.test.ts`).
    it("does not check its inputs are on the curve", async () => {
        const pts: Point[] = [[1n, 1n], ...Array<Point>(N - 1).fill(EDWARDS_IDENTITY)];
        await expectAccepts(many.circuit, input(pts));
    });
});
