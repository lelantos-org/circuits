// Input search for a mutant no test rejects: looks for an input the shipped
// circuit rejects and the mutant accepts. Such an input is the missing test.
//
// Runs as its own process inside a worker (see `campaign.ts`), against whatever
// `src/` that worker holds:
//
//   node test/mutation/probe.ts corpus <root> <out.json>
//       Against the unmutated circuit. Tamper one field of each honest base to
//       each candidate value, and keep the inputs a constraint rejects.
//   node test/mutation/probe.ts replay <root> <corpus.json> <out.json>
//       Against a mutant. Replay the corpus and keep the inputs it accepts.
//
// The witness calculator stands in for the constraint system here, so a defect
// that leaves the calculator unchanged (`<==` turned into `<--`) has no such
// input by construction.

import * as fs from "fs";
import { pathToFileURL } from "url";

import { Poseidon, circuitSignals } from "../helpers";
import { BatchBuilder } from "../lib/batch";
import { loadCircuit, srcPath, type CircuitInput, type CircuitSignal, type CircuitTester } from "../lib/circuit";
import { ALICE_NSK, BOB_NSK, DEPTH, MAX_L, TWO_64 } from "../lib/constants";
import { treeUpdateBatchInputJson } from "../lib/inputs";
import { readSignal, writeSignal } from "../lib/signal_path";
import { buildTxBuilder } from "../lib/transact";
import type { Root } from "./mutants";

/** One tampered input: `path` of honest base `base` set to `value`. */
export interface Tamper {
    base: string;
    path: string;
    value: string;
}

// ===== honest bases =====

async function transactBases(): Promise<Record<string, CircuitInput>> {
    const tx = await buildTxBuilder(DEPTH);
    const bundles = {
        balanced: tx.balanced(),
        fullShape: tx.fullShape(),
        multiAsset: tx.fullShapeMultiAsset(),
        withdraw: tx.spend(
            tx.oneRealOneDummy(1000n, ALICE_NSK),
            [tx.note(600n, ALICE_NSK, 9n), tx.note(0n, ALICE_NSK, 11n)],
            { publicOut: 400n },
        ),
        // Real notes of value 0: the rules that only bind a non-zero value are idle.
        zeroValues: tx.spend(
            tx.plant([tx.note(0n, ALICE_NSK, 1n)], ALICE_NSK),
            [tx.note(0n, ALICE_NSK, 9n), tx.note(0n, BOB_NSK, 11n)],
        ),
    };
    return Object.fromEntries(
        Object.entries(bundles).map(([name, b]) => [name, circuitSignals(b) as unknown as CircuitInput]),
    );
}

async function batchBases(): Promise<Record<string, CircuitInput>> {
    const batch = new BatchBuilder(await Poseidon.build());
    const witnesses = {
        oneDeposit: batch.single({ val: 100n, isDeposit: 1 }),
        oneSpend: batch.single({ val: 100n, isDeposit: 0 }),
        zeroDeposit: batch.single({ val: 0n, isDeposit: 1 }),
        mixed: batch.honest(5, [batch.seeded(0, 1), batch.seeded(1, 0), batch.seeded(2, 1)]),
        full: batch.honest(0, batch.seededMany(MAX_L, i => (i % 2) as 0 | 1)),
    };
    return Object.fromEntries(
        Object.entries(witnesses).map(([name, w]) => [name, treeUpdateBatchInputJson(w) as CircuitInput]),
    );
}

const BASES: Record<Root, () => Promise<Record<string, CircuitInput>>> = {
    "4x6": transactBases,
    tree_update_batch: batchBases,
};

// ===== tampers =====

/** A dimension wider than this is sampled at its first and last index. */
const WIDE = 8;

/** Every scalar entry of `input`, as a `key[i][j]` path. */
function leaves(input: CircuitInput): string[] {
    const out: string[] = [];
    const walk = (node: CircuitSignal, path: string) => {
        if (!Array.isArray(node)) {
            out.push(path);
            return;
        }
        const indices = node.length > WIDE ? [0, node.length - 1] : node.map((_, i) => i);
        for (const i of indices) walk(node[i], `${path}[${i}]`);
    };
    for (const key of Object.keys(input)) walk(input[key], key);
    return out;
}

/** The values a field is set to: off by one, the small constants, and the 64-bit bound. */
function candidates(current: bigint): bigint[] {
    return [...new Set([current + 1n, 0n, 1n, 2n, TWO_64])].filter(v => v !== current);
}

type Verdict = "accepts" | "rejects" | "other";

async function verdict(circuit: CircuitTester, input: CircuitInput): Promise<Verdict> {
    try {
        await circuit.calculateWitness(input, true);
        return "accepts";
    } catch (e) {
        const text = e instanceof Error ? e.message : String(e);
        // Anything else is a malformed input object, which says nothing about a constraint.
        return /Assert Failed/.test(text) ? "rejects" : "other";
    }
}

function tampered(base: CircuitInput, t: Tamper): CircuitInput {
    const input = structuredClone(base);
    writeSignal(input, t.path, BigInt(t.value));
    return input;
}

// ===== modes =====

async function corpus(root: Root, outFile: string): Promise<void> {
    const circuit = await loadCircuit(srcPath(`${root}.circom`));
    const bases = await BASES[root]();
    const rejected: Tamper[] = [];
    for (const [base, input] of Object.entries(bases)) {
        if ((await verdict(circuit, input)) !== "accepts") {
            throw new Error(`probe base "${base}" is not accepted by ${root}.circom`);
        }
        for (const path of leaves(input)) {
            for (const value of candidates(readSignal(input, path))) {
                const t = { base, path, value: value.toString() };
                if ((await verdict(circuit, tampered(input, t))) === "rejects") rejected.push(t);
            }
        }
    }
    fs.writeFileSync(outFile, JSON.stringify(rejected));
}

async function replay(root: Root, corpusFile: string, outFile: string): Promise<void> {
    const circuit = await loadCircuit(srcPath(`${root}.circom`));
    const bases = await BASES[root]();
    const tampers = JSON.parse(fs.readFileSync(corpusFile, "utf8")) as Tamper[];
    const accepted: Tamper[] = [];
    for (const t of tampers) {
        if ((await verdict(circuit, tampered(bases[t.base], t))) === "accepts") accepted.push(t);
    }
    fs.writeFileSync(outFile, JSON.stringify({ tried: tampers.length, accepted }));
}

async function main(): Promise<void> {
    const [mode, root, a, b] = process.argv.slice(2);
    if (!(root in BASES)) throw new Error(`probe: unknown circuit "${root}"`);
    if (mode === "corpus") await corpus(root as Root, a);
    else if (mode === "replay") await replay(root as Root, a, b);
    else throw new Error(`probe: unknown mode "${mode}"`);
}

// Runs only as a script: `campaign.ts` imports the types above.
if (process.argv[1] !== undefined && import.meta.url === pathToFileURL(process.argv[1]).href) {
    main().then(
        () => process.exit(0),
        err => {
            console.error(err instanceof Error ? err.message : err);
            process.exit(1);
        },
    );
}
