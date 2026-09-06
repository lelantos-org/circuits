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

    if (SHAPE_ERROR.test(text)) {
        throw new Error(
            `${message}\n` +
                "  ...but the witness calculator rejected the INPUT OBJECT, not a constraint. " +
                "A signal is misnamed, missing, or has the wrong arity — note that an unknown " +
                "key reports as \"Too many values\". Fix the test input; this proves nothing " +
                `about the circuit.\n  ${text.trim()}`,
        );
    }

    if (!CONSTRAINT_ERROR.test(text)) {
        throw new Error(
            `${message}\n` +
                "  ...but the failure is neither a constraint assert nor a known input-shape " +
                `error, so it cannot be attributed to the circuit.\n  ${text.trim()}`,
        );
    }

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
