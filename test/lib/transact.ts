// Transact-circuit witness builders shared by the spec and fuzz suites.

import {
    Poseidon,
    Jubjub,
    MerkleTree,
    derivePk,
    commit,
    nullifier,
    buildRho,
    toCircomInput,
    deterministicClueGen,
    buildLeaf,
    dummyInputAt,
    dummyOutput,
    fiatShamirZ,
    flatten,
    type CircomTransactInput,
    type ClueInputs,
    type Field,
    type Note,
    type SpentNote,
} from "../helpers";
import { ALICE_NSK, N_IN, N_OUT } from "./constants";

// Default asset id, for tests that do not depend on which asset is in use.
export const DEFAULT_ASSET: Field = 7n;

// Stand-in for `auxDigest(aux)`. The tests build clue witnesses but no
// encrypted-note payload, and the circuit constrains this slot only through
// PolyEval. Non-zero, so a test that drops the field fails rather than matching
// a default.
export const TEST_AUX_DIGEST: Field = 0xa17d19e57n;

export interface TxBuildArgs {
    inputs: SpentNote[];
    outputs: Note[];
    merkleRoot: Field;
    /** Defaults to DEFAULT_ASSET. Pass 0n explicitly for the all-dummy zero tx. */
    publicAssetId?: Field;
    /** Both default to 0n, the shielded-to-shielded case. */
    publicIn?: bigint;
    publicOut?: bigint;
    outputClues?: ClueInputs[];
    outputAuxDigest?: Field;
    /**
     * Overrides the Fiat-Shamir derivation. For tests that need a chosen
     * challenge; leave unset so `build` derives it from the coefficients.
     */
    z?: Field;
}

export class TxBuilder {
    private readonly clues: ReturnType<typeof deterministicClueGen>;
    constructor(public readonly P: Poseidon, public readonly J: Jubjub, public readonly depth: number) {
        this.clues = deterministicClueGen(P, J);
    }

    note(value: bigint, ownerNsk: Field, rho: Field, asset: Field = DEFAULT_ASSET): Note {
        return {
            asset,
            value,
            pk: derivePk(this.P, ownerNsk),
            rho,
            rcm: rho + 1n,
            rcv: rho + 2n,
            rcvDep: rho + 3n,
        };
    }

    // Insert a note into `tree`, returning a SpentNote with an empty proof;
    // `finalize` populates path and indices once the root is frozen. Leaf
    // format: Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y), the deposit anchor
    // pinning (asset, value) to the leaf.
    insert(tree: MerkleTree, n: Note, nsk: Field): SpentNote {
        const cm = commit(this.P, n);
        const assetGen = this.J.hashToAssetGen(n.asset);
        const cvDep = this.J.valueCommit(n.value, assetGen, n.rcvDep);
        const idx = tree.insert(buildLeaf(this.P, cm, cvDep));
        return {
            ...n, nsk, cm,
            nf: nullifier(this.P, nsk, n.rho, cm),
            leafIndex: idx,
            pathElements: [], pathIndices: [], isDummy: false,
        };
    }

    finalize(tree: MerkleTree, sn: SpentNote): SpentNote {
        const { pathElements, pathIndices } = tree.proof(sn.leafIndex);
        return { ...sn, pathElements, pathIndices };
    }

    // Build the JSON object the circuit consumes. The public asset generator is
    // derived in-circuit from publicAssetId.
    //
    // Output rho is forced to the derivation the circuit enforces,
    // rho = Poseidon(TAG_RHO, nullifier[0], out_index), overriding any note.rho
    // the caller supplied. Matches the SDK bundle builders.
    build(args: TxBuildArgs): CircomTransactInput {
        const nf0 = args.inputs[0].nf;
        // `Transact` takes exactly N_IN inputs and N_OUT outputs; a short
        // witness fails witness calculation. Unused slots take dummy inputs
        // (`is_dummy = 1`, bypassing the pk, Merkle and asset checks) and
        // value-0 output notes, which are real leaves and hash as such.
        const inputs = padInputs(this.P, this.depth, args.inputs);
        const padded = padOutputs(this.P, args.outputs);
        const outputs = padded.map((o, j) => ({ ...o, rho: buildRho(this.P, nf0, j) }));
        const outputClues = args.outputClues
            ? padClues(args.outputClues, outputs.length, this.clues)
            : outputs.map(() => this.clues.next());
        const outputAuxDigest = args.outputAuxDigest ?? TEST_AUX_DIGEST;
        const input = toCircomInput(this.P, this.J, {
            ...args,
            inputs,
            publicAssetId: args.publicAssetId ?? DEFAULT_ASSET,
            publicIn: args.publicIn ?? 0n,
            publicOut: args.publicOut ?? 0n,
            outputs,
            outputClues,
            outputAuxDigest,
        });
        // Derive the challenge from the coefficients, as the contract does.
        // `toCircomInput` defaults z to 1, at which PolyEval collapses to a
        // plain sum and y is permutation-invariant, so a TransactCompressN that
        // transposed two slots would still satisfy the suite. An explicit
        // `args.z` takes precedence.
        if (args.z !== undefined) input.z = args.z.toString();
        else rebindFiatShamir(input);
        return input;
    }

    newTree(): MerkleTree {
        return new MerkleTree(this.P, this.depth);
    }

    // ===== scenario factories =====
    //
    // Each builds a tree, freezes its root, then finalizes the proofs; the root
    // must be frozen before proofs are taken.

    /** Two real inputs from one owner. */
    twoRealInputs(values: [bigint, bigint], nsk: Field, asset: Field = DEFAULT_ASSET): Scenario {
        const tree = this.newTree();
        let inA = this.insert(tree, this.note(values[0], nsk, 1n, asset), nsk);
        let inB = this.insert(tree, this.note(values[1], nsk, 2n, asset), nsk);
        const root = tree.root();
        inA = this.finalize(tree, inA);
        inB = this.finalize(tree, inB);
        return { tree, root, inputs: [inA, inB] };
    }

    /** One real input plus a dummy: the withdraw / single-spend shape. */
    oneRealOneDummy(value: bigint, nsk: Field, asset: Field = DEFAULT_ASSET): Scenario {
        const tree = this.newTree();
        let inA = this.insert(tree, this.note(value, nsk, 1n, asset), nsk);
        const dB = dummyInputAt(this.P, this.depth, 99n);
        const root = tree.root();
        inA = this.finalize(tree, inA);
        return { tree, root, inputs: [inA, dB] };
    }

    /** Two dummy inputs against an empty tree: the deposit / all-dummy shape. */
    allDummyInputs(): Scenario {
        const tree = this.newTree();
        return {
            tree,
            root: tree.root(),
            inputs: [dummyInputAt(this.P, this.depth, 0n), dummyInputAt(this.P, this.depth, 1n)],
        };
    }

    /**
     * A balanced witness with two real inputs and two real outputs: 100 + 50 in,
     * 75 + 75 out, one owner, one asset, nothing public.
     *
     * The base for the tamper tests, which mutate a single field and expect
     * rejection, so it is honest in every respect but the field under test.
     */
    balanced(nsk: Field = ALICE_NSK): CircomTransactInput {
        const { root, inputs } = this.twoRealInputs([100n, 50n], nsk);
        return this.build({
            inputs,
            outputs: [this.note(75n, nsk, 9n), this.note(75n, nsk, 11n)],
            merkleRoot: root,
        });
    }
}

/**
 * Re-derive the Fiat-Shamir challenge `z` from the witness in its current state.
 *
 * Mirrors `lib/batch.ts :: rebindFiatShamir`. Call after mutating a
 * PolyEval-bound field when the test needs the challenge to describe the
 * witness it is evaluating; a tamper test expecting a constraint to fire does
 * not, since `z` carries no constraint of its own and a stale one only moves
 * the `y` the circuit outputs.
 */
export function rebindFiatShamir(input: CircomTransactInput): CircomTransactInput {
    input.z = fiatShamirZ(flatten(input)).toString();
    return input;
}

/**
 * Top up `inputs` to `N_IN` with dummies, distinct by `rho` so their nullifiers
 * differ.
 *
 * Pairwise distinctness is a consumer obligation, not a circuit constraint:
 * `Transact` places no relation between nullifier slots, and `src/4x6.circom`
 * assigns the pairwise check to the consumer (`MASP.sol`). Dummies are kept
 * distinct here so a witness matches what the SDK emits.
 */
function padInputs(P: Poseidon, depth: number, inputs: SpentNote[]): SpentNote[] {
    if (inputs.length > N_IN) {
        throw new Error(`padInputs: ${inputs.length} inputs exceeds N_IN = ${N_IN}`);
    }
    const out = [...inputs];
    // Offset well clear of the rho values the scenario factories hand out.
    for (let k = out.length; k < N_IN; k++) out.push(dummyInputAt(P, depth, 1000n + BigInt(k)));
    return out;
}

/**
 * Top up `outputs` to `N_OUT` with value-0 notes.
 *
 * Each padding note is seeded by the slot it lands in, so no two share a
 * blinder and none commits to the identity point; see `dummyOutput`.
 */
function padOutputs(P: Poseidon, outputs: Note[]): Note[] {
    if (outputs.length > N_OUT) {
        throw new Error(`padOutputs: ${outputs.length} outputs exceeds N_OUT = ${N_OUT}`);
    }
    const out = [...outputs];
    while (out.length < N_OUT) out.push(dummyOutput(P, out.length));
    return out;
}

/** Top up a caller-supplied clue list to match the padded output count. */
function padClues(
    clues: ClueInputs[],
    count: number,
    gen: ReturnType<typeof deterministicClueGen>,
): ClueInputs[] {
    const out = [...clues];
    while (out.length < count) out.push(gen.next());
    return out;
}

/** A frozen tree plus the finalized inputs spent from it. */
export interface Scenario {
    tree: MerkleTree;
    root: Field;
    inputs: SpentNote[];
}

/** Re-exported so suites import their transact vocabulary from one module. */
export { dummyInputAt, dummyOutput };

export async function buildTxBuilder(depth: number): Promise<TxBuilder> {
    const [P, J] = await Promise.all([Poseidon.build(), Jubjub.build()]);
    return new TxBuilder(P, J, depth);
}
