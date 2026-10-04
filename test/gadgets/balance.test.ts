// Unit tests for `lib/balance.circom`: the conservation check, and the range
// and dummy bookkeeping around it.
//
// `PerAssetValueBalance` sweeps N_CAND = N_IN + N_OUT + 1 = 11 candidate assets
// against every slot, so its cost grows as (N_IN + N_OUT)^2 while the shapes
// that exercise it multiply. Driving it through `transact_4x6` costs a full
// TxBuilder run and a full-circuit witness per case, which is why the
// transact suites only ever reach two assets; here a case is a plain field
// array, so the combinatorics the production circuit cannot afford — every slot
// a distinct asset, duplicate candidates, an asset present on one side only —
// are covered exhaustively.
//
// The full-circuit counterpart is `transact/multi_asset.test.ts`, which pins the
// same conservation property end to end on a handful of shapes.

import { BN254_FR, mod } from "../helpers";
import { generatedFixture } from "../lib/circuit";
import { expectAccepts, expectWitnessFails } from "../lib/expect";
import { perAssetValueBalanceInput, type PerAssetBalanceArgs } from "../lib/inputs";
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
    //   asset 16: the public bucket, nothing withdrawn
    const MAX_DISTINCT: PerAssetBalanceArgs = {
        inAsset: [11n, 12n, 13n, 14n],
        inValue: [100n, 50n, 30n, 20n],
        outAsset: [11n, 11n, 12n, 13n, 14n, 15n],
        outValue: [60n, 40n, 50n, 30n, 20n, 0n],
        publicAssetId: 16n,
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

    // Each of the value slots feeds exactly one candidate row here, so a
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
    // The bucket sits on the output side only: a transact proof never moves
    // tokens in.

    it("FAILS on a withdrawal of an asset no note carries", async () => {
        await expectWitnessFails(
            ctx.circuit,
            perAssetValueBalanceInput(shape(a => { a.publicOut = 7n; })),
            "public_out on an orphan asset reads 0 == 7",
        );
    });

    it("accepts a withdrawal from an asset the notes do carry", async () => {
        await expectAccepts(ctx.circuit, perAssetValueBalanceInput(shape(a => {
            a.publicAssetId = 11n;
            a.publicOut = 5n;
            a.outValue[0] -= 5n; // asset 11 now has 100 in, 55 + 40 + 5 out
        })));
    });

    it("FAILS when a withdrawal is not covered by the shielded side", async () => {
        await expectWitnessFails(
            ctx.circuit,
            perAssetValueBalanceInput(shape(a => { a.publicAssetId = 11n; a.publicOut = 5n; })),
            "public_out must be funded by the same asset's inputs",
        );
    });

    it("FAILS when a withdrawal is funded by another asset's outputs", async () => {
        await expectWitnessFails(ctx.circuit, perAssetValueBalanceInput(shape(a => {
            a.publicAssetId = 11n;
            a.publicOut = 5n;
            a.outValue[2] -= 5n; // taken from asset 12
        })), "the bucket must balance against its own asset's row");
    });

    it("the gadget has no input side for the bucket: nothing can be deposited through it", async () => {
        // The only way to add value on the left of a row is an input note. An
        // output inflated by 5 with the bucket naming its asset stays rejected
        // whatever public_out is.
        for (const publicOut of [0n, 5n]) {
            await expectWitnessFails(ctx.circuit, perAssetValueBalanceInput(shape(a => {
                a.publicAssetId = 11n;
                a.publicOut = publicOut;
                a.outValue[0] += 5n;
            })), `an inflated output must not balance at public_out = ${publicOut}`);
        }
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
                publicOut: 0n,
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

describe("RangeCheck64", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const range = useCircuit(generatedFixture("lib/balance.circom", "RangeCheck64", []));

    it("accepts 0, a mid-range value and 2^64 - 1", async () => {
        for (const v of [0n, 0xdead_beef_0123_4567n, TWO_64 - 1n]) {
            await expectAccepts(range.circuit, { v: v.toString() });
        }
    });

    it("rejects 2^64 and -1", async () => {
        for (const v of [TWO_64, mod(-1n, BN254_FR)]) {
            await expectWitnessFails(
                range.circuit,
                { v: v.toString() },
                "Num2Bits(64) must reject a value past 64 bits",
                { template: "Num2Bits" },
            );
        }
    });
});
