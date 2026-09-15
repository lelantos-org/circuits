import { expect } from "chai";
import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import { loadCircuit, srcPath, type CircuitInput } from "../lib/circuit";
import { circuitSignals, type TransactWitnessBundle } from "../ref/witness";
import { readOutput } from "../lib/expect";
import { TIMEOUT_HEAVY } from "../lib/constants";

// Groth16 public-signal order for the transact and batch shapes.
//
// The exported Solidity verifier takes `_pubSignals` as a flat `uint[2]`, so a
// transposition is not a type error: the two field elements arrive in the wrong
// order and every proof fails to verify, indistinguishably from a bad zkey or a
// stale ceremony.
//
// circom orders the main component's signals as:
//
//   witness[0]                = the constant 1
//   witness[1 .. nOutputs]    = main's OUTPUT signals, declaration order
//   witness[.. + nPubInputs]  = main's PUBLIC INPUT signals, declaration order
//
// `Transact` declares `signal output y` and receives `z` via
// `component main { public [z] }`, so the order is `[y, z]`, not `[z, y]`.
// `PubInputs.sol :: _finalizeRaw` depends on this: it returns
// `out[0] = y, out[1] = z`.
//
// Asserted against the compiled circuit, so adding an output to `Transact` or
// making another input public fails here rather than at on-chain verification.
//
// `TreeUpdateBatch` gets the same checks: it declares `signal output y`, takes
// `z` via `component main { public [ z ] }`, and `PubInputs.sol :: compress`
// returns the pair in the same order for both overloads. It needs no signal
// projection because, unlike transact, all of its logical public inputs are
// declared signals; the same property makes challenge-only words forgeable for
// it, which `tree_update_batch.test.ts :: divergent witness` checks.

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(HERE, "../..");

// Every shape whose public-signal order is pinned here.
//
// `4x6` has `nIn != nOut`, so it catches an ordering that only holds when the
// two arities agree. `project` maps a published witness to the circom input:
// transact's vector carries the challenge-only fields, which are logical public
// inputs but not signals, so the calculator rejects them; the batch declares
// every word it publishes and needs no projection.
interface Shape {
    label: string;
    circuit: string;
    vector: string;
    project?: (w: CircuitInput) => CircuitInput;
}

const SHAPES: Shape[] = [
    {
        label: "transact_4x6",
        circuit: "4x6.circom",
        vector: "vectors/transact-4x6.json",
        project: w => circuitSignals(w as unknown as TransactWitnessBundle) as never,
    },
    {
        label: "tree_update_batch_8",
        circuit: "tree_update_batch.circom",
        vector: "vectors/tree-update-batch-8.json",
    },
];

interface PublishedVector {
    // Parsed straight out of the published JSON, so it is typed as the circom
    // input shape rather than re-declared here.
    witness: CircuitInput;
    compression: { z: string; y: string };
    circuitOutput: { y: string };
}

function loadVector(file: string): PublishedVector {
    const p = resolve(ROOT, file);
    const parsed = JSON.parse(readFileSync(p, "utf8"));
    expect(parsed.vectors, `${p} has no vectors`).to.be.an("array").that.is.not.empty;
    return parsed.vectors[0];
}

describe("groth16 public-signal order", function () {
    this.timeout(TIMEOUT_HEAVY);

    for (const shape of SHAPES) {
        describe(shape.label, () => {
            let witness: bigint[];
            let vector: PublishedVector;

            before(async () => {
                vector = loadVector(shape.vector);
                const circuit = await loadCircuit(srcPath(shape.circuit));
                const input = shape.project ? shape.project(vector.witness) : vector.witness;
                witness = await circuit.calculateWitness(input, true);
            });

            it("witness[0] is the constant 1", () => {
                expect(BigInt(witness[0].toString())).to.equal(1n);
            });

            // The order assertions: the first public signal is y, the second z.
            it("witness[1] is `y`, the first public signal", () => {
                expect(readOutput(witness, 0).toString()).to.equal(vector.circuitOutput.y);
                expect(readOutput(witness, 0).toString()).to.equal(vector.compression.y);
            });

            it("witness[2] is `z`, the second public signal", () => {
                expect(readOutput(witness, 1).toString()).to.equal(vector.compression.z);
            });

            // If `y` equals `z`, the order assertions above hold vacuously under a
            // transposition.
            it("`y` and `z` are distinct, so the order is actually observable", () => {
                expect(vector.compression.y).to.not.equal(vector.compression.z);
            });

            it("the exported verifier consumes exactly these two, in this order", () => {
                // _pubSignals = [y, z], written out as the reference for other
                // consumers.
                const pubSignals = [BigInt(witness[1].toString()), BigInt(witness[2].toString())];
                expect(pubSignals.map(String)).to.deep.equal([
                    vector.compression.y,
                    vector.compression.z,
                ]);
            });
        });
    }
});
