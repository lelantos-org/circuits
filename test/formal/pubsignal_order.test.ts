import { expect } from "chai";

import { loadCircuit, srcPath, type CircuitInput } from "../lib/circuit";
import { readJson } from "../lib/files";
import { circuitSignals, type TransactWitnessBundle } from "../ref/witness";
import { readOutput } from "../lib/expect";
import { TIMEOUT_HEAVY } from "../lib/constants";

// Groth16 public-signal order for the transact and batch shapes, asserted
// against the compiled circuits.
//
// The exported Solidity verifier takes `_pubSignals` as a flat `uint[3]`, so a
// transposition is not a type error: every proof fails to verify.
//
// circom orders the main component's signals as:
//
//   witness[0]                = the constant 1
//   witness[1 .. nOutputs]    = main's output signals, declaration order
//   witness[.. + nPubInputs]  = main's public input signals, declaration order
//
// `Transact` declares `signal output y`, then `signal output digest`, and
// receives `z` via `component main { public [z] }`, so the order is
// `[y, digest, z]`, which `PubInputs.sol` must return. `TreeUpdateBatch`
// declares the same two outputs in the same order and takes `z` the same way.

// `4x6` has `nIn != nOut`, so it catches an ordering that only holds when the
// two arities agree. `project` maps a published witness to the circom input:
// transact's vector carries the challenge-only fields, which are not signals,
// so the calculator rejects them.
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
    witness: CircuitInput;
    compression: { z: string; y: string; digest: string };
    circuitOutput: { y: string; digest: string };
}

function loadVector(file: string): PublishedVector {
    const parsed = readJson(file);
    expect(parsed.vectors, `${file} has no vectors`).to.be.an("array").that.is.not.empty;
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
                expect(witness[0]).to.equal(1n);
            });

            it("witness[1] is `y`, the first public signal", () => {
                expect(readOutput(witness, 0).toString()).to.equal(vector.circuitOutput.y);
                expect(readOutput(witness, 0).toString()).to.equal(vector.compression.y);
            });

            it("witness[2] is `digest`, the second public signal", () => {
                expect(readOutput(witness, 1).toString()).to.equal(vector.circuitOutput.digest);
                expect(readOutput(witness, 1).toString()).to.equal(vector.compression.digest);
            });

            it("witness[3] is `z`, the third public signal", () => {
                expect(readOutput(witness, 2).toString()).to.equal(vector.compression.z);
            });

            // If two of the three coincide, the order assertions above hold
            // vacuously under a transposition of that pair.
            it("`y`, `digest` and `z` are distinct, so the order is actually observable", () => {
                const three = [vector.compression.y, vector.compression.digest, vector.compression.z];
                expect(new Set(three).size).to.equal(3);
            });

            it("the exported verifier consumes exactly these three, in this order", () => {
                // _pubSignals = [y, digest, z].
                const pubSignals = [0, 1, 2].map(i => readOutput(witness, i));
                expect(pubSignals.map(String)).to.deep.equal([
                    vector.compression.y,
                    vector.compression.digest,
                    vector.compression.z,
                ]);
            });
        });
    }
});
