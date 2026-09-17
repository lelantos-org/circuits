// One tampered field per test: take an honest witness, change exactly one
// field, and require the circuit to reject it.
//
// Each row's `reason` names the constraint expected to fire, so a failure
// reports which constraint stopped firing.

import {
    type CircomTransactInput,
    dummyOutput,
} from "../helpers";
import { expectAccepts, expectWitnessFails } from "../lib/expect";
import { ALICE_NSK, N_IN, N_OUT, TIMEOUT_CIRCUIT, TWO_64, TWO_252 } from "../lib/constants";
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

type TamperBase = "balanced" | "oneRealRestDummy" | "fullShape";

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

/** `"in_rcv[%]"` -> one row per input slot. */
function perInput(path: string, reason: string, extra: Partial<TamperCase> = {}): TamperCase[] {
    return expand(path, reason, N_IN, extra);
}

/** `"out_cv[%][0]"` -> one row per output slot. */
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
    // -- value commitments: cv = value·V^asset + rcv·H --
    ...perInput("in_rcv[%]",   "cv binding rejects a wrong input blinding"),
    ...perOutput("out_rcv[%]", "cv binding rejects a wrong output blinding"),
    ...perInput("in_cv[%][0]",   "in_cv must equal the ValueCommit recomputation"),
    ...perInput("in_cv[%][1]",   "the y-coordinate half of the same equality"),
    ...perOutput("out_cv[%][0]", "out_cv must equal the ValueCommit recomputation"),
    ...perOutput("out_cv[%][1]", "the y-coordinate half of the same equality"),

    // -- deposit anchor: cv_dep, which also feeds the Merkle leaf --
    ...perInput("in_rcv_dep[%]",    "leaf hash changes, so the Merkle proof no longer matches"),
    ...perOutput("out_rcv_dep[%]",  "the out_cv_dep equality constraint rejects"),
    ...perOutput("out_cv_dep[%][0]", "out_cv_dep[j][0] === out_note[j].cv_dep[0]"),
    ...perOutput("out_cv_dep[%][1]", "the y-coordinate half of the same equality"),

    // -- note commitments: cm = Poseidon over (packed_av, pk, rho, rcm) --
    ...perOutput("out_rcm[%]", "note commitment binding rejects"),
    ...perInput("in_rcm[%]",   "a different cm gives a different leaf, so Merkle rejects"),
    ...perOutput("out_rho[%]", "output note commitment binding (distinct from the out_rcm path)"),
    ...perInput("in_rho[%]",   "nullifier mismatch and Merkle leaf change, both fire"),
    // Every slot's out_cm is constrained, not only the ones a caller filled.
    ...perOutput("out_cm[%]",  "out_cm must equal the recomputed commitment"),

    // -- keys and nullifiers --
    ...perInput("in_pk[%]",     "pk === DerivePk(nsk) rejects a forged pk"),
    ...perInput("nullifier[%]", "nf === Poseidon(TAG_NF, nk, rho, cm) rejects a forged nullifier"),

    // -- 64-bit range checks: HashToAssetGen's Num2Bits(64) and RangeCheck64 --
    { path: "public_asset_id", reason: "HashToAssetGen Num2Bits(64)", value: () => TWO_64 },
    ...perInput("in_asset[%]",   "per-note Num2Bits(64) in HashToAssetGen", { value: () => TWO_64 }),
    ...perOutput("out_asset[%]", "per-note Num2Bits(64) in HashToAssetGen", { value: () => TWO_64 }),
    { path: "public_in",       reason: "RangeCheck64 on the public bucket", value: () => TWO_64 },
    { path: "public_out",      reason: "RangeCheck64 on the public bucket", value: () => TWO_64 },
    ...perInput("in_value[%]",   "value is bounded to 64 bits", { value: () => TWO_64 }),
    ...perOutput("out_value[%]", "value is bounded to 64 bits", { value: () => TWO_64 }),

    // -- 252-bit blinder range: MulH's Num2Bits(RCV_BITS) --
    ...perInput("in_rcv[%]", "Num2Bits(252) rejects a 253-bit blinder", { value: () => TWO_252 }),

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
     * The three honest bases, built once and handed out as deep copies.
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

    // Vacuity guard for the per-slot base: if the untouched witness were
    // unsatisfiable, every rejection below would pass regardless of the tamper.
    it("accepts the fully-occupied shape: every input and output slot real", async () => {
        await expectAccepts(ctx.circuit, ctx.tx.fullShape());
    });

    // Vacuity guard for the dummy-slot base.
    it("accepts one real input with the remaining slots dummy", async () => {
        await expectAccepts(ctx.circuit, oneRealRestDummy());
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

    // Honest witness: the top of the declared blinder range must stay spendable.
    // A Num2Bits one bit too narrow in MulH would make notes near the ceiling
    // unspendable; the SDK does not mint blinders this large, so no other test
    // covers it.
    it("accepts blinders at the top of the 252-bit range", async () => {
        const { tx, circuit } = ctx;
        const maxRcv = TWO_252 - 1n;

        const wide = { ...tx.note(100n, ALICE_NSK, 1n), rcv: maxRcv, rcvDep: maxRcv - 1n };
        const outA = { ...tx.note(75n, ALICE_NSK, 9n), rcv: maxRcv - 2n, rcvDep: maxRcv - 3n };
        await expectAccepts(circuit, tx.spend(
            tx.plant([wide, tx.note(50n, ALICE_NSK, 2n)], ALICE_NSK),
            [outA, tx.note(75n, ALICE_NSK, 11n)],
        ));
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
