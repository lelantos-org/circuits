// Assertions over circom_tester witnesses.
//
// `circuit.calculateWitness(input, true)` either succeeds or throws, so a
// rejection test reduces to a try/catch.

import { expect } from "chai";

import { readOutput, type CircuitInput, type CircuitTester } from "./circuit";
import type { Field } from "../helpers";

// Defined in ./circuit, which carries no chai dependency; re-exported here
// alongside the other witness assertions.
export { readOutput };

/**
 * Assert that witness generation for `input` throws.
 *
 * `message` should name the constraint under test: a failure here means that
 * constraint did not fire.
 */
export async function expectWitnessFails(
    circuit: CircuitTester,
    input: CircuitInput,
    message = "expected witness generation to fail",
): Promise<void> {
    let threw = false;
    try {
        await circuit.calculateWitness(input, true);
    } catch {
        threw = true;
    }
    if (!threw) throw new Error(message);
}

/**
 * Generate the witness, check every constraint, and assert the circuit's first
 * output equals `expectedY`.
 *
 * For the PolyEval circuits the output check is what pins the layout: `z` alone
 * does not, since a permuted compress yields a different but still satisfiable
 * challenge. `y` binds the slot order to `lib/inputs.ts`, and through it to
 * PubInputs.sol::compress.
 */
export async function expectWitnessY(
    circuit: CircuitTester,
    input: CircuitInput,
    expectedY: Field,
): Promise<bigint[]> {
    const witness = await circuit.calculateWitness(input, true);
    await circuit.checkConstraints(witness);
    expect(readOutput(witness).toString()).to.equal(
        expectedY.toString(),
        "circuit y must match reference PolyEval",
    );
    return witness;
}

/** Generate the witness and check every constraint. */
export async function expectAccepts(
    circuit: CircuitTester,
    input: CircuitInput,
): Promise<bigint[]> {
    const witness = await circuit.calculateWitness(input, true);
    await circuit.checkConstraints(witness);
    return witness;
}

// Boolean variant, for the merkle-permutation property tests.
export async function witnessMatchesRoot(
    circuit: CircuitTester,
    w: bigint[],
    root: bigint,
): Promise<boolean> {
    try {
        await circuit.assertOut(w, { root: root.toString() });
        return true;
    } catch {
        return false;
    }
}
