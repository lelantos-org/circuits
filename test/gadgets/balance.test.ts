// Unit tests for `lib/balance.circom`: the conservation check, its
// point-balance counterpart, and the range and dummy bookkeeping around them.
//
// `PerAssetValueBalance` sweeps N_CAND = N_IN + N_OUT + 1 = 11 candidate assets
// against every slot, so its cost grows as (N_IN + N_OUT)^2 while the shapes
// that exercise it multiply. Driving it through `transact_4x6` costs a full
// TxBuilder run and a 100k-constraint witness per case, which is why the
// transact suites only ever reach two assets; here a case is a plain field
// array, so the combinatorics the production circuit cannot afford — every slot
// a distinct asset, duplicate candidates, an asset present on one side only —
// are covered exhaustively.
//
// The full-circuit counterpart is `transact/multi_asset.test.ts`, which pins the
// same conservation property end to end on a handful of shapes.

import { expect } from "chai";

import { BN254_FR, EDWARDS_IDENTITY, H_BASE, mod, pointJson, type Field, type Point } from "../helpers";
import { generatedFixture, readOutput, readPoint } from "../lib/circuit";
import { expectAccepts, expectWitnessFails } from "../lib/expect";
import {
    perAssetPointBalanceInput,
    perAssetValueBalanceInput,
    scalarBits,
    type PerAssetBalanceArgs,
} from "../lib/inputs";
import { N_IN, N_OUT, TIMEOUT_CIRCUIT, TWO_64 } from "../lib/constants";
import { useCircuit } from "../lib/harness";

describe("PerAssetValueBalance (per-asset conservation)", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useCircuit(
        generatedFixture("lib/balance.circom", "PerAssetValueBalance", [N_IN, N_OUT]),
    );

    // ===== the shape that fills every candidate row =====
    //
    // `cand` is [in_asset[0..3], out_asset[0..5], public_asset_id], 11 entries.
    // Below, no two slots share an asset except out[0]/out[1], which split
    // asset 11 — so a row that is silently skipped shows up as an accepted
    // imbalance in the sweep that follows.
    //
    //   asset 11: in 100        -> out 60 + 40
    //   asset 12: in  50        -> out 50
    //   asset 13: in  30        -> out 30
    //   asset 14: in  20        -> out 20
    //   asset 15: nothing in    -> out 0
    //   asset 16: the public bucket, both sides 0
    const MAX_DISTINCT: PerAssetBalanceArgs = {
        inAsset: [11n, 12n, 13n, 14n],
        inValue: [100n, 50n, 30n, 20n],
        outAsset: [11n, 11n, 12n, 13n, 14n, 15n],
        outValue: [60n, 40n, 50n, 30n, 20n, 0n],
        publicAssetId: 16n,
        publicIn: 0n,
        publicOut: 0n,
    };

    /** `MAX_DISTINCT` with `mutate` applied to a deep copy. */
    function shape(mutate: (a: PerAssetBalanceArgs) => void = () => {}): PerAssetBalanceArgs {
        const a: PerAssetBalanceArgs = {
            ...MAX_DISTINCT,
            inAsset: [...MAX_DISTINCT.inAsset],
            inValue: [...MAX_DISTINCT.inValue],
            outAsset: [...MAX_DISTINCT.outAsset],
            outValue: [...MAX_DISTINCT.outValue],
        };
        mutate(a);
        return a;
    }

    // Vacuity guard for every rejection below: the untouched shape must pass,
    // or a rejection proves nothing about the field it changed.
    it("accepts a shape carrying five distinct assets plus a sixth public one", async () => {
        await expectAccepts(ctx.circuit, perAssetValueBalanceInput(MAX_DISTINCT));
    });

    // Each of the 11 value slots feeds exactly one candidate row here, so a
    // +1 that is not rejected names a row the gadget never evaluates: a loop
    // bound one short, or a high slot wired to the wrong candidate. The
    // transact suites reach slots 2..3 and 2..5 only with padding values, where
    // a missed row is invisible.
    describe("every value slot is bound", () => {
        for (let i = 0; i < N_IN; i++) {
            it(`in_value[${i}] + 1 is rejected`, async () => {
                await expectWitnessFails(
                    ctx.circuit,
                    perAssetValueBalanceInput(shape(a => { a.inValue[i] += 1n; })),
                    `candidate row for in_asset[${i}] must not accept an inflated input`,
                );
            });
        }
        for (let j = 0; j < N_OUT; j++) {
            it(`out_value[${j}] + 1 is rejected`, async () => {
                await expectWitnessFails(
                    ctx.circuit,
                    perAssetValueBalanceInput(shape(a => { a.outValue[j] += 1n; })),
                    `candidate row for out_asset[${j}] must not accept an inflated output`,
                );
            });
        }
        it("public_in + 1 is rejected", async () => {
            await expectWitnessFails(
                ctx.circuit,
                perAssetValueBalanceInput(shape(a => { a.publicIn += 1n; })),
                "the public candidate row must not accept an inflated deposit",
            );
        });
        it("public_out + 1 is rejected", async () => {
            await expectWitnessFails(
                ctx.circuit,
                perAssetValueBalanceInput(shape(a => { a.publicOut += 1n; })),
                "the public candidate row must not accept an inflated withdrawal",
            );
        });
    });

    // ===== the public row, cand[N_IN + N_OUT] =====
    //
    // `public_asset_id` is always a candidate, even when no note carries it.
    // That row is the only thing tying the two transparent buckets together.

    it("FAILS on a deposit of an asset no note carries", async () => {
        await expectWitnessFails(
            ctx.circuit,
            perAssetValueBalanceInput(shape(a => { a.publicIn = 7n; })),
            "public_in on an orphan asset must not be absorbed by the shielded rows",
        );
    });

    it("accepts an orphan public asset whose buckets cancel", async () => {
        // Nothing is minted: the row reads public_in == public_out and every
        // shielded row is untouched, because no note declares asset 16.
        await expectAccepts(
            ctx.circuit,
            perAssetValueBalanceInput(shape(a => { a.publicIn = 7n; a.publicOut = 7n; })),
        );
    });

    it("accepts a deposit into an asset the notes do carry", async () => {
        await expectAccepts(ctx.circuit, perAssetValueBalanceInput(shape(a => {
            a.publicAssetId = 11n;
            a.publicIn = 5n;
            a.outValue[0] += 5n; // asset 11 now has 105 in, 65 + 40 out
        })));
    });

    it("FAILS when a withdrawal is not covered by the shielded side", async () => {
        await expectWitnessFails(
            ctx.circuit,
            perAssetValueBalanceInput(shape(a => { a.publicAssetId = 11n; a.publicOut = 5n; })),
            "public_out must be funded by the same asset's inputs",
        );
    });

    // ===== assets present on one side only =====

    it("FAILS on minting: an output asset with no input of that asset", async () => {
        await expectWitnessFails(
            ctx.circuit,
            perAssetValueBalanceInput(shape(a => { a.outValue[5] = 1n; })),
            "asset 15 has no input, so any output of it must be rejected",
        );
    });

    it("FAILS on burning: an input asset with no output of that asset", async () => {
        await expectWitnessFails(
            ctx.circuit,
            perAssetValueBalanceInput(shape(a => { a.inAsset[3] = 17n; })),
            "asset 17 has no output, so the input must not vanish",
        );
    });

    // ===== duplicate candidates =====
    //
    // `cand` is not deduplicated: an asset held by several slots produces
    // several identical rows. Each must still be the full sum over that asset,
    // rather than the one slot that produced the row.

    it("accepts a single asset spread across every slot", async () => {
        await expectAccepts(ctx.circuit, perAssetValueBalanceInput({
            inAsset: [11n, 11n, 11n, 11n],
            inValue: [10n, 20n, 30n, 40n],
            outAsset: [11n, 11n, 11n, 11n, 11n, 11n],
            outValue: [1n, 2n, 3n, 4n, 5n, 85n],
            publicAssetId: 11n,
            publicIn: 0n,
            publicOut: 0n,
        }));
    });

    it("FAILS when duplicate rows hide an imbalance in a second asset", async () => {
        await expectWitnessFails(ctx.circuit, perAssetValueBalanceInput({
            inAsset: [11n, 11n, 11n, 12n],
            inValue: [10n, 20n, 30n, 40n],
            outAsset: [11n, 11n, 11n, 12n, 12n, 12n],
            outValue: [20n, 20n, 20n, 20n, 10n, 5n], // asset 12: 40 in, 35 out
            publicAssetId: 11n,
            publicIn: 0n,
            publicOut: 0n,
        }), "an imbalance must not be absorbed by a duplicated candidate row");
    });

    // A dummy input carries value 0 (DummyZeroValue, below) and may declare any
    // asset id; the row it adds is 0 == 0. Documented in the template header.
    it("a zero-value slot is neutral whatever asset it declares", async () => {
        await expectAccepts(ctx.circuit, perAssetValueBalanceInput(shape(a => {
            a.inAsset[3] = 0xdeadbeefn;
            a.inValue[3] = 0n;
            a.outValue[4] = 0n; // asset 14's 20 is no longer funded
            a.outAsset[4] = 0xfeedn;
        })));
    });

    // ===== the caller's obligation: 64-bit range checks =====

    it("accepts sums at the 64-bit ceiling without wrapping", async () => {
        const max = TWO_64 - 1n;
        await expectAccepts(ctx.circuit, perAssetValueBalanceInput({
            inAsset: [11n, 11n, 11n, 11n],
            inValue: [max, max, max, max],
            outAsset: [11n, 11n, 11n, 11n, 11n, 11n],
            outValue: [max, max, max, max, 0n, 0n],
            publicAssetId: 11n,
            publicIn: 0n,
            publicOut: 0n,
        }));
    });

    // The template header calls the caller's RangeCheck64 soundness-critical:
    // without it the equality is modular, not integer. This pins that the
    // gadget alone really does admit a wrapping witness, so the obligation is
    // load-bearing rather than belt-and-braces. `SpentNote`, `OutputNote` and
    // `Transact` supply the checks; `transact/tamper.test.ts` covers them at
    // 2^64 on every slot.
    it("admits a field-wrapping witness — conservation is integer-exact only under the caller's RangeCheck64", async () => {
        // -1 + 2 == 1 (mod R), while as integers the input side is ~2^254.
        await expectAccepts(ctx.circuit, perAssetValueBalanceInput({
            inAsset: [11n, 11n, 11n, 11n],
            inValue: [mod(-1n, BN254_FR), 2n, 0n, 0n],
            outAsset: [11n, 11n, 11n, 11n, 11n, 11n],
            outValue: [1n, 0n, 0n, 0n, 0n, 0n],
            publicAssetId: 11n,
            publicIn: 0n,
            publicOut: 0n,
        }));
    });
});

describe("PerAssetPointBalance (defence in depth)", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useCircuit(
        generatedFixture("lib/balance.circom", "PerAssetPointBalance", [N_IN, N_OUT]),
    );

    /** cv = value·V^asset + rcv·H and rH = rcv·H, as SpentNote/OutputNote emit them. */
    function commitments(
        notes: readonly { asset: Field; value: Field; rcv: Field }[],
    ): { cv: Point[]; rH: Point[] } {
        const { J } = ctx;
        return {
            cv: notes.map(n => J.commit(n.asset, n.value, n.rcv)),
            rH: notes.map(n => J.mulPointEscalar(H_BASE, n.rcv)),
        };
    }

    /** A balanced single-asset bundle: 100 + 50 in, 60 + 90 out, nothing public. */
    function balanced() {
        const ins = [
            { asset: 11n, value: 100n, rcv: 7n },
            { asset: 11n, value: 50n, rcv: 9n },
            { asset: 11n, value: 0n, rcv: 0n },
            { asset: 11n, value: 0n, rcv: 0n },
        ];
        const outs = [
            { asset: 11n, value: 60n, rcv: 3n },
            { asset: 11n, value: 90n, rcv: 5n },
            { asset: 11n, value: 0n, rcv: 0n },
            { asset: 11n, value: 0n, rcv: 0n },
            { asset: 11n, value: 0n, rcv: 0n },
            { asset: 11n, value: 0n, rcv: 0n },
        ];
        const inSide = commitments(ins);
        const outSide = commitments(outs);
        return {
            inCv: inSide.cv,
            inRH: inSide.rH,
            outCv: outSide.cv,
            outRH: outSide.rH,
            pubInPt: EDWARDS_IDENTITY,
            pubOutPt: EDWARDS_IDENTITY,
        };
    }

    it("accepts an honest bundle", async () => {
        await expectAccepts(ctx.circuit, perAssetPointBalanceInput(balanced()));
    });

    it("FAILS when one output commitment is replaced", async () => {
        const { J } = ctx;
        const a = balanced();
        a.outCv[0] = J.addPoint(a.outCv[0], J.mulPointEscalar(H_BASE, 1n));
        await expectWitnessFails(
            ctx.circuit,
            perAssetPointBalanceInput(a),
            "the Edwards sums must not match after an output commitment changes",
        );
    });

    it("FAILS when an rH is not the blinder's own multiple of H", async () => {
        const { J } = ctx;
        const a = balanced();
        a.inRH[0] = J.mulPointEscalar(H_BASE, 8n); // in_rcv[0] is 7
        await expectWitnessFails(
            ctx.circuit,
            perAssetPointBalanceInput(a),
            "a mismatched rH must break the point equality",
        );
    });

    // The template header states this equality is NOT a conservation check:
    // V^1 + V^3 == 2·V^2, so X of asset 1 plus X of asset 3 mints 2X of asset 2
    // and the points still balance. Asserted here so nothing re-derives
    // conservation from this gadget; `PerAssetValueBalance` above is what
    // rejects the same shape (see its "FAILS on burning" row, and
    // `transact/multi_asset.test.ts` end to end).
    it("accepts a cross-asset forgery, which is why it cannot stand alone", async () => {
        const X = 1000n;
        const inSide = commitments([
            { asset: 1n, value: X, rcv: 4n },
            { asset: 3n, value: X, rcv: 6n },
            { asset: 1n, value: 0n, rcv: 0n },
            { asset: 1n, value: 0n, rcv: 0n },
        ]);
        const outSide = commitments([
            { asset: 2n, value: 2n * X, rcv: 10n },
            { asset: 2n, value: 0n, rcv: 0n },
            { asset: 2n, value: 0n, rcv: 0n },
            { asset: 2n, value: 0n, rcv: 0n },
            { asset: 2n, value: 0n, rcv: 0n },
            { asset: 2n, value: 0n, rcv: 0n },
        ]);
        await expectAccepts(ctx.circuit, perAssetPointBalanceInput({
            inCv: inSide.cv,
            inRH: inSide.rH,
            outCv: outSide.cv,
            outRH: outSide.rH,
            pubInPt: EDWARDS_IDENTITY,
            pubOutPt: EDWARDS_IDENTITY,
        }));
    });
});

describe("DummyZeroValue (dummy bookkeeping)", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useCircuit(generatedFixture("lib/balance.circom", "DummyZeroValue", [N_IN]));

    const input = (dummy: bigint[], value: bigint[]) => ({
        dummy: dummy.map(String),
        value: value.map(String),
    });

    it("accepts real slots with any value and dummy slots at zero", async () => {
        await expectAccepts(ctx.circuit, input([0n, 1n, 0n, 1n], [12345n, 0n, TWO_64 - 1n, 0n]));
    });

    it("FAILS when a dummy slot carries value", async () => {
        await expectWitnessFails(
            ctx.circuit,
            input([0n, 1n, 0n, 0n], [1n, 1n, 0n, 0n]),
            "dummy[i] * value[i] === 0 must reject a valued dummy",
        );
    });

    for (const bad of [2n, mod(-1n, BN254_FR)]) {
        it(`FAILS when a dummy flag is ${bad === 2n ? "2" : "-1"}`, async () => {
            await expectWitnessFails(
                ctx.circuit,
                input([bad, 0n, 0n, 0n], [0n, 0n, 0n, 0n]),
                "dummy[i] * (dummy[i] - 1) === 0 must reject a non-boolean flag",
            );
        });
    }
});

describe("RangeCheck64 and ValueTimesGen", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const range = useCircuit(generatedFixture("lib/balance.circom", "RangeCheck64", []));
    const times = useCircuit(generatedFixture("lib/balance.circom", "ValueTimesGen", []));

    it("decomposes a value LSB-first", async () => {
        const v = 0xdead_beef_0123_4567n;
        const w = await range.circuit.calculateWitness({ v: v.toString() }, true);
        const bits = Array.from({ length: 64 }, (_, i) => readOutput(w, i));
        expect(bits).to.deep.equal(scalarBits(v, 64).map(BigInt));
    });

    it("accepts 2^64 - 1 and rejects 2^64", async () => {
        await expectAccepts(range.circuit, { v: (TWO_64 - 1n).toString() });
        await expectWitnessFails(
            range.circuit,
            { v: TWO_64.toString() },
            "Num2Bits(64) must reject a 65-bit value",
            { template: "Num2Bits" },
        );
    });

    it("multiplies the generator by the value", async () => {
        const { J } = times;
        const gen = J.hashToAssetGen(11n);
        for (const value of [0n, 1n, 2n, 1000n, TWO_64 - 1n]) {
            const w = await times.circuit.calculateWitness({
                value: value.toString(),
                gen: pointJson(gen),
            }, true);
            expect(readPoint(w)).to.deep.equal(
                value === 0n ? EDWARDS_IDENTITY : J.mulPointEscalar(gen, value),
                `value·gen mismatch at ${value}`,
            );
        }
    });

    it("FAILS at 2^64, so the transparent bucket cannot exceed its range", async () => {
        const gen = times.J.hashToAssetGen(11n);
        await expectWitnessFails(times.circuit, {
            value: TWO_64.toString(),
            gen: pointJson(gen),
        }, "ValueTimesGen must range-check its value", { template: "Num2Bits" });
    });
});
