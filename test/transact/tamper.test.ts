// One tampered field per test: take an honest witness, change exactly one
// field, and require the circuit to reject it.
//
// Each row's `reason` names the constraint expected to fire, so a failure
// reports which constraint stopped firing.

import {
    type CircomTransactInput,
    type TransactWitnessBundle,
    TAG_CM,
    buildInner,
    buildNullifierFromNsk,
    dummyOutput,
} from "../helpers";
import { expectAccepts, expectWitnessFails } from "../lib/expect";
import { ALICE_NSK, N_IN, N_OUT, TIMEOUT_CIRCUIT, TWO_64 } from "../lib/constants";
import { DEFAULT_ASSET, rebindFiatShamir } from "../lib/transact";
import { readSignal, writeSignal } from "../lib/signal_path";
import { useTransactCircuit } from "./setup";

interface TamperCase {
    /** Field to change, addressed the way the circom names it. */
    path: string;
    /** The constraint that must reject the change. */
    reason: string;
    /** Defaults to `+1`; range rows push the field past its bound instead. */
    value?: (input: CircomTransactInput) => bigint;
    /** Defaults to the balanced 2-in-2-out witness. */
    base?: TamperBase;
}

type TamperBase = "balanced" | "oneRealRestDummy" | "fullShape" | "withdraw";

// ===== per-slot expansion =====
//
// Rows are written once with `%` as the slot index and expanded over every slot
// the shape declares. `Transact` takes N_IN = 4 inputs and N_OUT = 6 outputs,
// while the scenario factories fill at most two of each; a constraint
// mis-indexed for slot >= 2 (a loop bound one short, an unwired high slot) is
// satisfied by every witness built from `balanced()`.
//
// Expanded rows run against `fullShape`, where every slot holds a real note. In
// `balanced` the high slots are dummies and padding, which carry weaker
// constraints and would need per-index expectations.

/** `"in_rcm[%]"` -> one row per input slot. */
function perInput(path: string, reason: string, extra: Partial<TamperCase> = {}): TamperCase[] {
    return expand(path, reason, N_IN, extra);
}

/** `"out_cm[%]"` -> one row per output slot. */
function perOutput(path: string, reason: string, extra: Partial<TamperCase> = {}): TamperCase[] {
    return expand(path, reason, N_OUT, extra);
}

function expand(
    path: string,
    reason: string,
    count: number,
    extra: Partial<TamperCase>,
): TamperCase[] {
    if (!path.includes("%")) throw new Error(`expand: "${path}" has no % slot placeholder`);
    return Array.from({ length: count }, (_, k) => ({
        path: path.replace("%", String(k)),
        reason,
        base: "fullShape" as const,
        ...extra,
    }));
}

// ===== rows =====
//
// Grouped by what the field feeds rather than by name, so coverage gaps are
// visible in the list.
const TAMPER_CASES: TamperCase[] = [
    // -- note commitments: cm = Poseidon(TAG_CM, packed_av, Poseidon(TAG_INNER, pk, rho, rcm)) --
    ...perOutput("out_rcm[%]", "note commitment binding rejects"),
    ...perInput("in_rcm[%]",   "a different cm is a different leaf, so Merkle rejects"),
    ...perOutput("out_rho[%]", "output note commitment binding (distinct from the out_rcm path)"),
    ...perInput("in_rho[%]",   "nullifier mismatch and Merkle leaf change, both fire"),
    ...perOutput("out_pk[%]",  "the owner key is inside cm"),
    // Every slot's out_cm is constrained, not only the ones a caller filled.
    ...perOutput("out_cm[%]",  "out_cm must equal the recomputed commitment"),

    // -- (asset, value) inside cm: the leaf is cm, so either moves the leaf --
    ...perInput("in_asset[%]",   "a relabelled input opens a different leaf, and unbalances its asset"),
    ...perInput("in_value[%]",   "a revalued input opens a different leaf, and unbalances"),
    ...perOutput("out_asset[%]", "out_cm no longer matches, and the asset is unbalanced"),
    ...perOutput("out_value[%]", "out_cm no longer matches, and the transaction is unbalanced"),

    // -- keys and nullifiers --
    ...perInput("in_pk[%]",     "pk === DerivePk(nsk) rejects a forged pk"),
    ...perInput("nullifier[%]", "nf === Poseidon(TAG_NF, nk, rho, cm) rejects a forged nullifier"),

    // -- 64-bit range checks: RangeCheck64 on every asset id and every value --
    ...perInput("in_asset[%]",   "RangeCheck64 on a spent note's asset id", { value: () => TWO_64 }),
    ...perOutput("out_asset[%]", "RangeCheck64 on an output note's asset id", { value: () => TWO_64 }),
    ...perInput("in_value[%]",   "value is bounded to 64 bits", { value: () => TWO_64 }),
    ...perOutput("out_value[%]", "value is bounded to 64 bits", { value: () => TWO_64 }),
    { path: "public_asset_id", reason: "RangeCheck64 on the public bucket's asset id",
      value: () => TWO_64, base: "withdraw" },
    { path: "public_out",      reason: "RangeCheck64 on the public bucket", value: () => TWO_64, base: "withdraw" },

    // -- transparent bucket --
    // On the balanced transfer public_out is 0, so naming an asset touches no
    // candidate sum: the bucket constraint is the only one that can reject.
    { path: "public_asset_id", reason: "public_out == 0 forces public_asset_id == 0",
      value: () => DEFAULT_ASSET },
    { path: "public_out",      reason: "a withdrawal nothing funds is unbalanced" },
    { path: "public_out",      reason: "withdrawing one unit more than the inputs fund", base: "withdraw" },
    { path: "public_asset_id", reason: "a withdrawal under id 0 is unbalanced: no real note carries id 0",
      value: () => 0n, base: "withdraw" },
    { path: "public_asset_id", reason: "a withdrawal relabelled to an asset no input carries",
      base: "withdraw" },

    // -- booleanity --
    // On `fullShape` every slot is real (is_dummy = 0). The row below covers the
    // is_dummy = 1 side in slot 1, which `oneRealRestDummy` fills with a dummy.
    ...perInput("in_is_dummy[%]", "in_is_dummy must be 0 or 1", { value: () => 2n }),
    { path: "in_is_dummy[1]", reason: "in_is_dummy must be 0 or 1, in a dummy slot too",
      value: () => 2n, base: "oneRealRestDummy" },

    // -- Merkle path --
    // Both halves of an authentication path, per input: a bad digit and a
    // perturbed sibling fail through different gadgets.
    ...perInput("in_path_indices[%][0]", "a quaternary path index above 3 is not selectable",
        { value: () => 4n }),
    ...perInput("in_path_elements[%][0][0]",
        "a perturbed sibling must not recompute to the declared root"),
    { path: "merkle_root", reason: "the recomputed root must equal the declared one" },
];

describe("transact_4x6 / single-field tamper", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useTransactCircuit();

    /**
     * The honest bases, built once and handed out as deep copies.
     *
     * Each base costs a full `TxBuilder` run (a tree, four inserts, four
     * authentication paths), which dominates per-row time; `structuredClone` of
     * the finished input is negligible. A row writes only its own copy, so the
     * shared originals are not modified.
     */
    type BaseName = NonNullable<TamperCase["base"]>;
    const bases = {} as Record<BaseName, CircomTransactInput>;

    before(() => {
        bases.fullShape = ctx.tx.fullShape();
        bases.balanced = ctx.tx.balanced();
        bases.oneRealRestDummy = oneRealRestDummy();
        bases.withdraw = withdraw();
    });

    // `base` is optional on a row; omitted means the balanced shape.
    function honest(base: TamperCase["base"]): CircomTransactInput {
        return structuredClone(bases[base ?? "balanced"]);
    }

    /**
     * One real input in slot 0, dummies in slots 1..N_IN-1, balanced and honest.
     *
     * The base for rows that tamper a dummy slot. It must not be all-dummy:
     * `Transact` asserts `all_dummy.out === 0` (src/lib/transact.circom), so an
     * all-dummy bundle is rejected regardless of the tamper and a rejection test
     * built on it passes vacuously.
     */
    function oneRealRestDummy(): CircomTransactInput {
        const { tx } = ctx;
        return tx.spend(
            tx.oneRealOneDummy(1000n, ALICE_NSK),
            [tx.note(1000n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
        );
    }

    /**
     * One real input of 1000, 900 kept and 100 withdrawn in the note's asset.
     *
     * The base for the transparent-bucket rows: on a transfer `public_out` is 0
     * and the bucket is empty, so its range checks and its balance term have
     * nothing to act on.
     */
    function withdraw(): CircomTransactInput {
        const { tx } = ctx;
        return tx.spend(
            tx.oneRealOneDummy(1000n, ALICE_NSK),
            [tx.note(900n, ALICE_NSK, 9n)],
            { publicOut: 100n },
        );
    }

    // Vacuity guard for the per-slot base: if the untouched witness were
    // unsatisfiable, every rejection below would pass regardless of the tamper.
    it("accepts the fully-occupied shape: every input and output slot real", async () => {
        await expectAccepts(ctx.circuit, ctx.tx.fullShape());
    });

    // Vacuity guard for the dummy-slot base.
    it("accepts one real input with the remaining slots dummy", async () => {
        await expectAccepts(ctx.circuit, oneRealRestDummy());
    });

    // Vacuity guard for the transparent-bucket base.
    it("accepts a withdrawal in the spent note's asset", async () => {
        await expectAccepts(ctx.circuit, withdraw());
    });

    for (const { path, reason, value, base } of TAMPER_CASES) {
        // The default mutation nudges the field by one: enough to break any binding.
        const mutate = value ?? ((input: CircomTransactInput) => readSignal(input, path) + 1n);
        it(`FAILS when ${path} is tampered — ${reason}`, async () => {
            const input = honest(base);
            writeSignal(input, path, mutate(input));
            await expectWitnessFails(ctx.circuit, input, `${path}: ${reason} — did not reject`);
        });
    }

    // ===== asset-id range, isolated =====
    //
    // The rows above push an asset id to 2^64 in an otherwise honest witness, so
    // the stale cm rejects it as well and the range check is not shown to fire.
    // These two build the note consistently around the oversized id, with the
    // commitment and nullifier recomputed over it, on slots whose value is 0 so
    // conservation is untouched. RangeCheck64 on asset_id is then the only
    // constraint left to reject, and it is the one NoteCommitment's packing
    // depends on: asset·2^64 + value is injective only under both bounds.

    /** A zero-value `cm` over any asset id, including one the reference refuses to pack. */
    function oversizedCm(asset: bigint, n: { pk: bigint; rho: bigint; rcm: bigint }): bigint {
        const { P } = ctx.tx;
        return P.hash([TAG_CM, asset * TWO_64, buildInner(P, n)]);
    }

    /** `oneRealRestDummy` with dummy slot 1 rebuilt around `asset`. */
    function dummyDeclaring(asset: bigint): TransactWitnessBundle {
        const { P } = ctx.tx;
        const input = oneRealRestDummy() as TransactWitnessBundle;
        const rho = readSignal(input, "in_rho[1]");
        const cm = oversizedCm(asset, { pk: 0n, rho, rcm: 0n });
        writeSignal(input, "in_asset[1]", asset);
        writeSignal(input, "nullifier[1]", buildNullifierFromNsk(P, 0n, rho, cm));
        return rebindFiatShamir(input);
    }

    /** `oneRealRestDummy` with its zero-value output (slot 1) rebuilt around `asset`. */
    function zeroOutputDeclaring(asset: bigint): TransactWitnessBundle {
        const input = oneRealRestDummy() as TransactWitnessBundle;
        const n = {
            pk: readSignal(input, "out_pk[1]"),
            rho: readSignal(input, "out_rho[1]"),
            rcm: readSignal(input, "out_rcm[1]"),
        };
        writeSignal(input, "out_asset[1]", asset);
        writeSignal(input, "out_cm[1]", oversizedCm(asset, n));
        return rebindFiatShamir(input);
    }

    // The control for each rejection below: the same rebuild at the largest id
    // in range is accepted, so the rebuild itself is sound and 2^64 is rejected
    // for its width alone.
    it("accepts a dummy input declaring asset_id = 2^64 - 1, cm and nullifier consistent", async () => {
        await expectAccepts(ctx.circuit, dummyDeclaring(TWO_64 - 1n));
    });

    it("FAILS when a dummy input declares asset_id = 2^64, cm and nullifier consistent", async () => {
        await expectWitnessFails(ctx.circuit, dummyDeclaring(TWO_64),
            "the asset range check must hold on a dummy slot: nothing else reads its asset id");
    });

    it("accepts a zero-value output declaring asset_id = 2^64 - 1, cm consistent", async () => {
        await expectAccepts(ctx.circuit, zeroOutputDeclaring(TWO_64 - 1n));
    });

    it("FAILS when a zero-value output declares asset_id = 2^64, cm consistent", async () => {
        await expectWitnessFails(ctx.circuit, zeroOutputDeclaring(TWO_64),
            "the asset range check must hold on an output whose value contributes nothing to balance");
    });

    // The two out_cm cases need their own bases: one slot holds a real note, the
    // other a padding output, and a different constraint rejects each.
    /** One real output in slot 0, a padding output in slot 1. */
    function realAndPaddingOutput(): CircomTransactInput {
        const { tx } = ctx;
        return tx.spend(
            tx.oneRealOneDummy(100n, ALICE_NSK),
            [tx.note(100n, ALICE_NSK, 9n), dummyOutput(tx.P, 1)],
        );
    }

    it("FAILS when a real output's out_cm is replaced", async () => {
        const input = realAndPaddingOutput();
        writeSignal(input, "out_cm[0]", 12345n);
        await expectWitnessFails(ctx.circuit, input, "out_cm[0] must equal the recomputed commitment");
    });

    it("FAILS when a padding output's out_cm is replaced", async () => {
        const { circuit } = ctx;
        const input = realAndPaddingOutput();
        writeSignal(input, "out_cm[1]", 777n);
        await expectWitnessFails(circuit, input, "the padding slot's out_cm is constrained too");
    });

    it("FAILS when a dummy input's nullifier is replaced", async () => {
        const input = oneRealRestDummy();
        // Slot 1 is a dummy; slot 0 holds the real note that keeps the bundle
        // past `all_dummy.out === 0`.
        writeSignal(input, "nullifier[1]", 42n);
        await expectWitnessFails(ctx.circuit, input, "nf is constrained in dummy slots as well");
    });
});
