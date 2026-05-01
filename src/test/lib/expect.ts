// `await circuit.calculateWitness(input, true)` either succeeds or throws.
// Tests repeatedly used a try/catch+flag pattern; collapse it here.

export async function expectWitnessFails(
    circuit: any,
    input: any,
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

// Variant returning bool — used by the merkle-permutation property tests.
export async function witnessMatchesRoot(circuit: any, w: any, root: bigint): Promise<boolean> {
    try {
        await circuit.assertOut(w, { root: root.toString() });
        return true;
    } catch {
        return false;
    }
}
