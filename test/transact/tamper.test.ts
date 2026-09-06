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
import { useTransactCircuit } from "./setup";

/** Read/write a witness field addressed as `out_cv_dep[1][0]`. */
function parsePath(path: string): { key: string; idx: number[] } {
    const [key, ...rest] = path.split("[");
    return { key, idx: rest.map(part => Number(part.replace("]", ""))) };
}

function readField(input: CircomTransactInput, path: string): string {
    const { key, idx } = parsePath(path);
    let cur: unknown = (input as Record<string, unknown>)[key];
    for (const i of idx) cur = (cur as unknown[])[i];
    return cur as string;
}

function writeField(input: CircomTransactInput, path: string, value: bigint): void {
    const { key, idx } = parsePath(path);
    if (idx.length === 0) {
        (input as Record<string, unknown>)[key] = value.toString();
        return;
    }
    let cur = (input as Record<string, unknown>)[key] as unknown[];
    for (const i of idx.slice(0, -1)) cur = cur[i] as unknown[];
    cur[idx[idx.length - 1]] = value.toString();
}

/** The default mutation: nudge the field by one. Enough to break any binding. */
function bumped(input: CircomTransactInput, path: string): bigint {
    return BigInt(readField(input, path)) + 1n;
}

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

type TamperBase = "balanced" | "allDummy" | "fullShape";

// ===== per-slot expansion =====
//
// The rows below are written once with a `%` where the slot index goes, then
// expanded over EVERY slot the shape declares. The point is that `Transact`
// takes N_IN = 4 inputs and N_OUT = 6 outputs while the scenario factories fill
// at most two of each: a constraint that is mis-indexed for slot >= 2 — a loop
// bound one short, a high slot never wired up — is satisfied by every witness
// built from `balanced()`, so testing slot 0 proves nothing about slot 3.
//
// These run against `fullShape`, where every slot holds a real note; on
// `balanced` the high slots are dummies and padding, which carry deliberately
// weaker constraints and would need different expectations per index.

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
// Grouped by what the field feeds rather than by name, so a coverage gap reads
// as a gap in the list.
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
    // On `fullShape` every slot is real (is_dummy = 0), so 2 is out of range for
    // each of them; the `allDummy` row below covers the is_dummy = 1 side.
    ...perInput("in_is_dummy[%]", "in_is_dummy must be 0 or 1", { value: () => 2n }),
    { path: "in_is_dummy[0]", reason: "in_is_dummy must be 0 or 1, in a dummy slot too",
      value: () => 2n, base: "allDummy" },

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

    function honest(base: TamperCase["base"]): CircomTransactInput {
        const { tx } = ctx;
        if (base === "allDummy") {
            const { root, inputs } = tx.allDummyInputs();
            return tx.build({
                inputs,
                outputs: [tx.note(0n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
                merkleRoot: root,
            });
        }
        if (base === "fullShape") return tx.fullShape();
        return tx.balanced();
    }

    // The base every per-slot row tampers. Without it a row could "pass" because
    // the untouched witness was already unsatisfiable — every rejection below
    // would then be vacuous, and the whole expansion would prove nothing.
    it("accepts the fully-occupied shape: every input and output slot real", async () => {
        await expectAccepts(ctx.circuit, ctx.tx.fullShape());
    });

    for (const { path, reason, value, base } of TAMPER_CASES) {
        const mutate = value ?? ((input: CircomTransactInput) => bumped(input, path));
        it(`FAILS when ${path} is tampered — ${reason}`, async () => {
            const input = honest(base);
            writeField(input, path, mutate(input));
            await expectWitnessFails(ctx.circuit, input, `${path}: ${reason} — did not reject`);
        });
    }

    // An honest witness, not a tamper case: the top of the declared blinder
    // range must stay spendable. A Num2Bits one bit too narrow in MulH would
    // make notes near the ceiling unspendable, and the SDK never mints one this
    // large, so nothing else covers it.
    it("accepts blinders at the top of the 252-bit range", async () => {
        const { tx, circuit } = ctx;
        const maxRcv = TWO_252 - 1n;
        const tree = tx.newTree();

        const wide = { ...tx.note(100n, ALICE_NSK, 1n), rcv: maxRcv, rcvDep: maxRcv - 1n };
        let inA = tx.insert(tree, wide, ALICE_NSK);
        let inB = tx.insert(tree, tx.note(50n, ALICE_NSK, 2n), ALICE_NSK);
        const root = tree.root();
        inA = tx.finalize(tree, inA);
        inB = tx.finalize(tree, inB);

        const outA = { ...tx.note(75n, ALICE_NSK, 9n), rcv: maxRcv - 2n, rcvDep: maxRcv - 3n };
        const input = tx.build({
            inputs: [inA, inB],
            outputs: [outA, tx.note(75n, ALICE_NSK, 11n)],
            merkleRoot: root,
        });

        const w = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(w);
    });

    // The two out_cm cases need their own bases: one slot holds a real note, the
    // other a padding output, and a different constraint rejects each.
    it("FAILS when a real output's out_cm is replaced", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.oneRealOneDummy(100n, ALICE_NSK);
        const input = tx.build({
            inputs,
            outputs: [tx.note(100n, ALICE_NSK, 9n), dummyOutput(tx.P, 1)],
            merkleRoot: root,
        });
        writeField(input, "out_cm[0]", 12345n);
        await expectWitnessFails(circuit, input, "out_cm[0] must equal the recomputed commitment");
    });

    it("FAILS when a padding output's out_cm is replaced", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.oneRealOneDummy(100n, ALICE_NSK);
        const input = tx.build({
            inputs,
            outputs: [tx.note(100n, ALICE_NSK, 9n), dummyOutput(tx.P, 1)],
            merkleRoot: root,
        });
        writeField(input, "out_cm[1]", 777n);
        await expectWitnessFails(circuit, input, "the padding slot's out_cm is constrained too");
    });

    it("FAILS when a dummy input's nullifier is replaced", async () => {
        const { tx, circuit } = ctx;
        const { root, inputs } = tx.allDummyInputs();
        const input = tx.build({
            publicIn: 1000n,
            inputs,
            outputs: [tx.note(1000n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            merkleRoot: root,
        });
        writeField(input, "nullifier[0]", 42n);
        await expectWitnessFails(circuit, input, "nf is constrained in dummy slots as well");
    });
});
