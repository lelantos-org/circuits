// Assertions over circom_tester witnesses.
//
// `circuit.calculateWitness(input, true)` either succeeds or throws. A
// rejection test does NOT reduce to a bare try/catch, because the two throw
// classes mean opposite things: see `SHAPE_ERROR` below.

import { expect } from "chai";

import { readOutput, type CircuitInput, type CircuitTester } from "./circuit";
import type { Field } from "../helpers";

// Defined in ./circuit, which carries no chai dependency; re-exported here
// alongside the other witness assertions.
export { readOutput };

// The witness calculator fails in two unrelated ways, and only one of them is
// evidence that a constraint fired.
//
// A violated constraint raises `Assert Failed.`, followed by one
// `Error in template <Name>_<id> line: <n>` frame per enclosing template:
//
//     Error: Assert Failed.
//     Error in template Num2Bits_0 line: 38
//     Error in template Probe_1 line: 8
//
// A malformed input object raises something else entirely — and, critically, a
// MISTYPED SIGNAL NAME lands here rather than being ignored: circom counts the
// values it was handed, so an unknown key reads as a surplus value.
//
//     Not enough values for input signal b
//     Too many values for input signal zzz      <- the typo case
//     Not all inputs have been set. Only 1 out of 3
//
// A rejection test that accepts either class is vacuous: rename a signal and it
// still "passes", now proving only that the test's own input object is wrong.
// `expectWitnessFails` therefore treats the second class as a test bug.
const SHAPE_ERROR =
    /Not enough values for input signal|Too many values for input signal|Not all inputs have been set/;

const CONSTRAINT_ERROR = /Assert Failed/;

/**
 * Decide what a witness-calculator failure means, or throw saying it proves
 * nothing.
 *
 * Returns normally only for the one class that is evidence about the circuit: a
 * constraint fired. The other two are test bugs, and reporting them as passes is
 * how a rejection suite goes green while checking nothing.
 *
 * `context` is prepended to the diagnostic, so each caller names what it was
 * asserting.
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
     * Name of the circom template whose assert must fire, without the numeric
     * suffix circom appends (`Num2Bits`, not `Num2Bits_0`). Matched against
     * every frame of the error, so either the gadget or an enclosing template
     * may be named.
     *
     * Pins WHICH constraint rejected, not merely that something did. Worth
     * setting wherever two different constraints could plausibly cover a field
     * and the test is asserting a specific one.
     */
    template?: string;
}

/**
 * Assert that witness generation for `input` fails a CONSTRAINT.
 *
 * `message` should name the constraint under test: a failure here means that
 * constraint did not fire.
 *
 * An input-shape error (see `SHAPE_ERROR` above) is reported as a test bug
 * rather than counted as a pass, so a renamed or mistyped signal cannot turn a
 * rejection suite green while proving nothing.
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

/**
 * Assert that a witness diverging from the calldata it is proved against cannot
 * be forged into a passing proof.
 *
 * This is the soundness shape the rest of this file cannot express. Every other
 * batch assertion derives `(y, z)` from the same object it feeds the circuit, so
 * the witness and the calldata are the same thing by construction. A real
 * prover authors them separately: `z` arrives from the contract's hash over
 * calldata, and nothing forces the witness to agree with it. The gap between the
 * two is where an unpinned coefficient lives.
 *
 * `input.z` must already be the CALLDATA challenge and `calldataY` the value the
 * contract will compare against — see `lib/batch.ts :: bindFiatShamir`.
 *
 * The circuit is sound on this field if EITHER:
 *   - a constraint rejects the divergent witness, or
 *   - it is admitted but yields `y != calldataY`, so the on-chain equality
 *     fails.
 *
 * It is BROKEN if the witness is admitted and `y == calldataY`: the contract
 * validated one set of values and the proof attests to another. That is a
 * forgery, and it is what this assertion exists to name.
 */
export async function expectNotForgeable(
    circuit: CircuitTester,
    input: CircuitInput,
    calldataY: Field,
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

    const y = readOutput(witness!);
    if (y === calldataY) {
        throw new Error(
            `FORGERY: ${field} diverges from the calldata word it is proved against, yet the ` +
                "circuit admitted the witness AND emitted the calldata's own y " +
                `(${calldataY.toString()}).\n` +
                "  The contract will therefore accept a proof attesting to values it never " +
                "validated. This field is neither a PolyEval coefficient nor pinned by any " +
                "constraint that reaches one — hashing it into z binds nothing, because the " +
                "prover reads z before choosing the witness.\n" +
                "  See src/README.md § 2a and BatchCompress in src/lib/poly_eval.circom.",
        );
    }
}

/**
 * Assert that a witness view and a calldata view describe different statements.
 *
 * The guard a divergence case needs before it asserts anything. It exists
 * because a mutation run showed all 49 batch cases surviving a SHALLOW
 * `calldataView`: the snapshot then shares the witness's arrays, the mutation
 * moves both, and every case compares a view against itself and passes.
 *
 * Both arguments are challenge preimages — `treeUpdateBatchChallenge` for the
 * batch, `flatten` for transact — so the comparison covers exactly the words the
 * contract hashes.
 */
export function assertViewsDiverge(witness: Field[], calldata: Field[], field: string): void {
    expect(witness.join(","), `${field}: the witness and calldata views are identical, so ` +
        "this case proves nothing about the circuit. Either `calldataView` is not returning a " +
        "deep copy, or this case's `diverge` writes a value the honest base already holds — " +
        "several cases assign a constant rather than bumping, so a change to the base can " +
        "silently make one a no-op.")
        .to.not.equal(calldata.join(","));
}
