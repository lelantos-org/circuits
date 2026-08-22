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
    type CircomTransactInput,
    type ClueInputs,
    type Field,
    type Note,
    type SpentNote,
} from "../helpers";
import { ALICE_NSK } from "./constants";

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

    // Insert a note into `tree`, returning a SpentNote with an empty proof.
    // Call `finalize` once the root is frozen to populate path and indices.
    // Leaf format: Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y), the deposit
    // anchor pinning (asset, value) to the leaf.
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
        const outputs = args.outputs.map((o, j) => ({ ...o, rho: buildRho(this.P, nf0, j) }));
        const outputClues =
            args.outputClues ?? outputs.map(() => this.clues.next());
        const outputAuxDigest = args.outputAuxDigest ?? TEST_AUX_DIGEST;
        return toCircomInput(this.P, this.J, {
            ...args,
            publicAssetId: args.publicAssetId ?? DEFAULT_ASSET,
            publicIn: args.publicIn ?? 0n,
            publicOut: args.publicOut ?? 0n,
            outputs,
            outputClues,
            outputAuxDigest,
        });
    }

    newTree(): MerkleTree {
        return new MerkleTree(this.P, this.depth);
    }

    // ===== scenario factories =====
    //
    // Each builds a tree, freezes its root, and finalizes the proofs, in that
    // order — the root must be frozen before proofs are taken. Between them they
    // cover every input shape the suite uses.

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
     * A balanced 2-in-2-out witness: 100 + 50 in, 75 + 75 out, one owner, one
     * asset, nothing public.
     *
     * The base for the tamper tests, which mutate a single field and expect
     * rejection, so it must be honest in every respect but the field under test.
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
