// Assertions over circom_tester witnesses.

import { expect } from "chai";

import { readOutput, type CircuitInput, type CircuitTester } from "./circuit";
import type { Field } from "../helpers";

// Defined in ./circuit, which carries no chai dependency.
export { readOutput };

// The witness calculator fails in two unrelated ways. A violated constraint
// raises `Assert Failed.`, followed by one
// `Error in template <Name>_<id> line: <n>` frame per enclosing template. A
// malformed input object raises one of the SHAPE_ERROR messages; a mistyped
// signal name lands there too, as "Too many values", because circom counts the
// values it receives.
//
// `expectWitnessFails` treats the second class as a test bug: accepting it
// would let a rejection test pass on a wrong input object.
const SHAPE_ERROR =
    /Not enough values for input signal|Too many values for input signal|Not all inputs have been set/;

const CONSTRAINT_ERROR = /Assert Failed/;

/**
 * Throws unless `text` is a constraint failure. `context` is prepended to the
 * diagnostic.
 */
function requireConstraintFailure(text: string, context: string): void {
    if (SHAPE_ERROR.test(text)) {
        throw new Error(
            `${context}\n` +
                "  ...but the witness calculator rejected the INPUT OBJECT, not a constraint. " +
                "A signal is misnamed, missing, or has the wrong arity — note that an unknown " +
                "key reports as \"Too many values\". Fix the test input; this proves nothing " +
                `about the circuit.\n  ${text.trim()}`,
        );
    }
    if (!CONSTRAINT_ERROR.test(text)) {
        throw new Error(
            `${context}\n` +
                "  ...but the failure is neither a constraint assert nor a known input-shape " +
                `error, so it cannot be attributed to the circuit.\n  ${text.trim()}`,
        );
    }
}

/** `Error in template Foo_12 line: 34` -> `Foo`, for every frame, outermost last. */
function failingTemplates(message: string): string[] {
    return [...message.matchAll(/Error in template (\w+?)_\d+ line/g)].map(m => m[1]);
}

export interface WitnessFailureOptions {
    /**
     * Circom template whose assert must fire, without the numeric suffix
     * (`Num2Bits`, not `Num2Bits_0`). Matched against every frame of the
     * error, so either the gadget or an enclosing template may be named.
     */
    template?: string;
}

/**
 * Assert that witness generation for `input` fails a constraint. `message`
 * should name the constraint under test. An input-shape error (see
 * `SHAPE_ERROR`) is reported as a test bug, not a pass.
 */
export async function expectWitnessFails(
    circuit: CircuitTester,
    input: CircuitInput,
    message = "expected witness generation to fail",
    opts: WitnessFailureOptions = {},
): Promise<void> {
    let err: unknown;
    try {
        await circuit.calculateWitness(input, true);
    } catch (e) {
        err = e;
    }

    if (err === undefined) throw new Error(message);

    const text = err instanceof Error ? err.message : String(err);
    requireConstraintFailure(text, message);

    if (opts.template !== undefined) {
        const frames = failingTemplates(text);
        if (!frames.includes(opts.template)) {
            throw new Error(
                `${message}\n` +
                    `  ...a constraint fired, but not in template "${opts.template}". ` +
                    `Asserts came from: ${frames.length > 0 ? frames.join(" <- ") : "(no template frame)"}`,
            );
        }
    }
}

/**
 * Generate the witness, check every constraint, and assert the circuit's first
 * output equals `expectedY`.
 *
 * For the PolyEval circuits `y` binds the slot order to `lib/inputs.ts`, and
 * through it to PubInputs.sol::compress; `z` alone does not, since a permuted
 * compress yields a different but still satisfiable challenge.
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

/**
 * `expectWitnessY`, and the circuit's second output equals `expected.digest`:
 * the Poseidon commitment to the coefficients, which the contract compares
 * against the calldata digest word.
 */
export async function expectWitnessPublic(
    circuit: CircuitTester,
    input: CircuitInput,
    expected: { y: Field; digest: Field },
): Promise<bigint[]> {
    const witness = await expectWitnessY(circuit, input, expected.y);
    expect(readOutput(witness, 1).toString()).to.equal(
        expected.digest.toString(),
        "circuit digest must match the reference CoeffDigest",
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

/**
 * Assert that `fn` throws or rejects, for any reason. Weaker than
 * `expectWitnessFails`, which requires a constraint to fire; for cases where
 * the reference builder or the witness calculator may reject first.
 */
export async function expectThrows(fn: () => unknown, message: string): Promise<void> {
    try {
        await fn();
    } catch {
        return;
    }
    throw new Error(message);
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

/**
 * Assert that a witness diverging from the calldata it is proved against cannot
 * be forged into a passing proof.
 *
 * `input.z` must already be the calldata challenge, and `calldata` the other two
 * public signals the contract hands the verifier: its `y` over the calldata
 * coefficients and the calldata digest word. See `lib/batch.ts ::
 * bindFiatShamir`.
 *
 * Passes if a constraint rejects the witness, or if it is admitted with a `y`
 * or `digest` different from the contract's, so the proof is for other public
 * signals and fails. Throws if the witness is admitted and both outputs match:
 * the contract validated one set of values and the proof attests to another.
 */
export async function expectNotForgeable(
    circuit: CircuitTester,
    input: CircuitInput,
    calldata: { y: Field; digest: Field },
    field: string,
): Promise<void> {
    let witness: bigint[] | undefined;
    let err: unknown;
    try {
        witness = await circuit.calculateWitness(input, true);
        await circuit.checkConstraints(witness);
    } catch (e) {
        err = e;
    }

    if (err !== undefined) {
        const text = err instanceof Error ? err.message : String(err);
        requireConstraintFailure(
            text,
            `divergent witness on ${field} was expected to be rejected by a constraint`,
        );
        // A constraint fired: the divergence is pinned in-circuit.
        return;
    }

    const y = readOutput(witness!, 0);
    const digest = readOutput(witness!, 1);
    if (y === calldata.y && digest === calldata.digest) {
        throw new Error(
            `FORGERY: ${field} diverges from the calldata word it is proved against, yet the ` +
                "circuit admitted the witness AND emitted the calldata's own y " +
                `(${calldata.y.toString()}) and digest (${calldata.digest.toString()}).\n` +
                "  The contract will therefore accept a proof attesting to values it never " +
                "validated. Either this field is not a coefficient, or it is not absorbed by " +
                "the coefficient digest — hashing it into z binds nothing on its own, because " +
                "the prover reads z before choosing the witness.\n" +
                "  See src/README.md § 2a and src/lib/poly_eval.circom.",
        );
    }
}

/**
 * Assert that a witness view and a calldata view describe different statements;
 * precondition for a divergence case. With a shallow `calldataView` the two
 * share arrays and every case compares a view against itself.
 *
 * Both arguments are challenge preimages (`treeUpdateBatchChallenge` for the
 * batch, `flatten` for transact): the words the contract hashes.
 */
export function assertViewsDiverge(witness: Field[], calldata: Field[], field: string): void {
    expect(witness.join(","), `${field}: the witness and calldata views are identical, so ` +
        "this case proves nothing about the circuit. Either `calldataView` is not returning a " +
        "deep copy, or this case's `diverge` writes a value the honest base already holds — " +
        "several cases assign a constant rather than bumping, so a change to the base can " +
        "silently make one a no-op.")
        .to.not.equal(calldata.join(","));
}
