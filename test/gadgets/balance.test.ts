// Unit tests for `lib/balance.circom`: the conservation check, and the range
// and dummy bookkeeping around it.
//
// `PerAssetValueBalance` is instantiated at (N_IN, N_OUT) and driven with plain
// field arrays. It range-checks nothing: the equality is integer-exact only
// under the RangeCheck64 that `SpentNote`, `OutputNote` and `Transact` apply.

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
    // No two slots share an asset except out[0]/out[1], which split asset 11,
    // so a skipped row shows up as an accepted imbalance in the sweep below.
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

    // Vacuity guard for the rejections below: the untouched shape must pass.
    it("accepts a shape carrying five distinct assets plus a sixth public one", async () => {
        await expectAccepts(ctx.circuit, perAssetValueBalanceInput(MAX_DISTINCT));
    });

    // Each value slot feeds one candidate row here, so an accepted +1 names a
    // row the gadget never evaluates.
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
            a.outValue[0] -= 5n; // asset 11: 100 in, 55 + 40 + 5 out
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
    // several identical rows, each the full sum over that asset.

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
    // asset id; the row it adds is 0 == 0.
    it("a zero-value slot is neutral whatever asset it declares", async () => {
        await expectAccepts(ctx.circuit, perAssetValueBalanceInput(shape(a => {
            a.inAsset[3] = 0xdeadbeefn;
            a.inValue[3] = 0n;
            a.outValue[4] = 0n; // asset 14's 20 has no funding input
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

    // The template does not make the flag boolean: SpentNote does, through
    // MerkleProofOrDummy. Any non-zero flag still pins the value to zero.
    for (const flag of [2n, mod(-1n, BN254_FR)]) {
        const label = flag === 2n ? "2" : "-1";
        it(`accepts a flag of ${label} on a zero-value slot`, async () => {
            await expectAccepts(ctx.circuit, input([flag, 0n, 0n, 0n], [0n, 0n, 0n, 0n]));
        });

        it(`FAILS when a slot flagged ${label} carries value`, async () => {
            await expectWitnessFails(
                ctx.circuit,
                input([flag, 0n, 0n, 0n], [1n, 0n, 0n, 0n]),
                "dummy[i] * value[i] === 0 must reject under any non-zero flag",
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
