import { expect } from "chai";
import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import { loadCircuit, srcPath } from "../lib/circuit";

// Groth16 public-signal ORDER for the transact shapes.
//
// The exported Solidity verifier takes `_pubSignals` as a flat `uint[2]`, so a
// transposition is not a type error anywhere: it is two field elements handed
// over in the wrong order, and every proof simply fails to verify. That is a
// silent, total integration break, and the failure mode looks identical to a
// bad zkey or a stale ceremony — which is exactly why it deserves a pin rather
// than a sentence in a README.
//
// circom orders the main component's signals as:
//
//   witness[0]                = the constant 1
//   witness[1 .. nOutputs]    = main's OUTPUT signals, declaration order
//   witness[.. + nPubInputs]  = main's PUBLIC INPUT signals, declaration order
//
// `Transact` declares `signal output y` and receives `z` via
// `component main { public [z] }`, so the order is `[y, z]` — NOT `[z, y]`.
// The consumer relies on this: `PubInputs.sol :: _finalizeRaw` returns
// `out[0] = y, out[1] = z`.
//
// This asserts it against the compiled circuit rather than against prose, so
// adding an output to `Transact`, or promoting another input to public, fails
// here instead of at the first on-chain verification.

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(HERE, "../../..");

// Every shape that ships a published vector. `3x3` is the deployed one; `2x2`
// is retained as a second instantiation of `Transact` and pins that the
// ordering is a property of the template, not of one arity.
const SHIPPED_SHAPES = ["2x2", "3x3"] as const;

interface PublishedVector {
    witness: Record<string, unknown>;
    compression: { z: string; y: string };
    circuitOutput: { y: string };
}

function loadVector(shape: string): PublishedVector {
    const p = resolve(ROOT, `vectors/transact-${shape}.json`);
    const parsed = JSON.parse(readFileSync(p, "utf8"));
    expect(parsed.vectors, `${p} has no vectors`).to.be.an("array").that.is.not.empty;
    return parsed.vectors[0];
}

describe("groth16 public-signal order", function () {
    this.timeout(600000);

    for (const shape of SHIPPED_SHAPES) {
        describe(`transact_${shape}`, () => {
            let witness: bigint[];
            let vector: PublishedVector;

            before(async () => {
                vector = loadVector(shape);
                const circuit = await loadCircuit(srcPath(`${shape}.circom`));
                witness = await circuit.calculateWitness(vector.witness, true);
            });

            it("witness[0] is the constant 1", () => {
                expect(BigInt(witness[0].toString())).to.equal(1n);
            });

            // The two assertions that matter. Together they say: the first
            // public signal is y and the second is z.
            it("witness[1] is `y`, the first public signal", () => {
                expect(BigInt(witness[1].toString()).toString()).to.equal(vector.circuitOutput.y);
                expect(BigInt(witness[1].toString()).toString()).to.equal(vector.compression.y);
            });

            it("witness[2] is `z`, the second public signal", () => {
                expect(BigInt(witness[2].toString()).toString()).to.equal(vector.compression.z);
            });

            // Guards the inference above: if `y` and `z` were ever equal the
            // order assertions would hold vacuously under a transposition.
            it("`y` and `z` are distinct, so the order is actually observable", () => {
                expect(vector.compression.y).to.not.equal(vector.compression.z);
            });

            it("the exported verifier consumes exactly these two, in this order", () => {
                // _pubSignals = [y, z]. Spelled out so a reader porting this to
                // another consumer copies the right pair.
                const pubSignals = [BigInt(witness[1].toString()), BigInt(witness[2].toString())];
                expect(pubSignals.map(String)).to.deep.equal([
                    vector.compression.y,
                    vector.compression.z,
                ]);
            });
        });
    }
});
