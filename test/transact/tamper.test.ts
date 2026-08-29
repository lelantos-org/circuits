// One tampered field per test: take an honest witness, change exactly one
// field, and require the circuit to reject it.
//
// Each row's `reason` names the constraint expected to fire, so a regression
// reports which one stopped firing.

import {
    type CircomTransactInput,
    dummyOutput,
} from "../helpers";
import { expectWitnessFails } from "../lib/expect";
import { ALICE_NSK, TIMEOUT_CIRCUIT, TWO_64, TWO_252 } from "../lib/constants";
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
    base?: "balanced" | "allDummy";
}

// ===== rows =====
//
// Grouped by what the field feeds rather than by name, so a coverage gap reads
// as a gap in the list.
const TAMPER_CASES: TamperCase[] = [
    // -- value commitments: cv = value·V^asset + rcv·H --
    { path: "in_rcv[0]",  reason: "cv binding rejects a wrong input blinding" },
    { path: "out_rcv[0]", reason: "cv binding rejects a wrong output blinding" },
    { path: "in_cv[0][0]", reason: "in_cv must equal the ValueCommit recomputation",
      value: () => 42n },
    { path: "out_cv[0][0]", reason: "out_cv must equal the ValueCommit recomputation" },

    // -- deposit anchor: cv_dep, which also feeds the Merkle leaf --
    { path: "in_rcv_dep[0]",  reason: "leaf hash changes, so the Merkle proof no longer matches" },
    { path: "out_rcv_dep[0]", reason: "the out_cv_dep equality constraint rejects" },
    { path: "out_cv_dep[0][0]", reason: "out_cv_dep[j][0] === out_note[j].cv_dep[0]" },
    { path: "out_cv_dep[0][1]", reason: "the y-coordinate half of the same equality" },
    { path: "out_cv_dep[1][0]", reason: "the second output's x-coordinate" },
    { path: "out_cv_dep[1][1]", reason: "the second output's y-coordinate" },

    // -- note commitments: cm = Poseidon over (packed_av, pk, rho, rcm) --
    { path: "out_rcm[0]", reason: "note commitment binding rejects" },
    { path: "in_rcm[0]",  reason: "a different cm gives a different leaf, so Merkle rejects" },
    { path: "out_rho[0]", reason: "output note commitment binding (distinct from the out_rcm path)" },
    { path: "in_rho[0]",  reason: "nullifier mismatch and Merkle leaf change, both fire" },

    // -- keys and nullifiers --
    { path: "in_pk[0]",     reason: "pk === DerivePk(nsk) rejects a forged pk" },
    { path: "nullifier[0]", reason: "nf === Poseidon(TAG_NF, nk, rho, cm) rejects a forged nullifier" },

    // -- 64-bit range checks: HashToAssetGen's Num2Bits(64) and RangeCheck64 --
    { path: "public_asset_id", reason: "HashToAssetGen Num2Bits(64)", value: () => TWO_64 },
    { path: "in_asset[0]",     reason: "per-note Num2Bits(64) in HashToAssetGen", value: () => TWO_64 },
    { path: "out_asset[0]",    reason: "per-note Num2Bits(64) in HashToAssetGen", value: () => TWO_64 },
    { path: "public_in",       reason: "RangeCheck64 on the public bucket", value: () => TWO_64 },
    { path: "public_out",      reason: "RangeCheck64 on the public bucket", value: () => TWO_64 },
    { path: "in_value[0]",     reason: "value is bounded to 64 bits", value: () => TWO_64,
      base: "allDummy" },
    { path: "out_value[0]",    reason: "value is bounded to 64 bits", value: () => TWO_64,
      base: "allDummy" },

    // -- 252-bit blinder range: MulH's Num2Bits(RCV_BITS) --
    { path: "in_rcv[0]", reason: "Num2Bits(252) rejects a 253-bit blinder", value: () => TWO_252 },

    // -- booleanity --
    { path: "in_is_dummy[0]", reason: "in_is_dummy must be 0 or 1", value: () => 2n,
      base: "allDummy" },

    // -- Merkle path --
    { path: "in_path_indices[0][0]", reason: "a quaternary path index above 3 is not selectable",
      value: () => 4n },
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
        return tx.balanced();
    }

    for (const { path, reason, value, base } of TAMPER_CASES) {
        const mutate = value ?? ((input: CircomTransactInput) => bumped(input, path));
        it(`FAILS when ${path} is tampered — ${reason}`, async () => {
            const input = honest(base);
            writeField(input, path, mutate(input));
            await expectWitnessFails(ctx.circuit, input, `${path}: ${reason} — did not reject`);
        });
    }

    // Not a tamper case: the witness is honest, and the assertion is that the
    // top of the declared blinder range remains spendable. A Num2Bits width one
    // bit too narrow in MulH would make notes near the ceiling unspendable, and
    // the SDK never mints one this large, so nothing else covers it.
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
            outputs: [tx.note(100n, ALICE_NSK, 9n), dummyOutput()],
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
            outputs: [tx.note(100n, ALICE_NSK, 9n), dummyOutput()],
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
