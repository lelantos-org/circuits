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
    type ClueInputs,
    type Field,
    type Note,
    type SpentNote,
} from "../helpers";

// Default asset id used by tests that don't care which asset they're on.
export const DEFAULT_ASSET: Field = 7n;

// Stand-in for `auxDigest(aux)`. These tests build clue witnesses but no real
// encrypted-note payload, and the circuit places no constraint on this slot —
// it is bound by PolyEval only. Non-zero so a test that drops the field fails
// loudly rather than matching an accidental default.
export const TEST_AUX_DIGEST: Field = 0xa17d19e57n;

export interface TxBuildArgs {
    publicAssetId: Field;
    publicIn: bigint;
    publicOut: bigint;
    inputs: SpentNote[];
    outputs: Note[];
    merkleRoot: Field;
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

    // Insert a note into `tree`, returning a SpentNote with empty proof — call
    // `finalize` once the tree's root is frozen to populate path/indices.
    // Leaf format: Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y) — the deposit
    // anchor that pins (asset, value) to the leaf.
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

    // Build the JSON object that the circuit consumes. The public asset
    // generator is derived in-circuit from publicAssetId.
    //
    // Output rho is forced to the Orchard-style derivation the circuit now
    // enforces: rho = Poseidon(TAG_RHO, nullifier[0], out_index). Any note.rho
    // the caller passed is overridden (matches the SDK bundle builders).
    build(args: TxBuildArgs): any {
        const nf0 = args.inputs[0].nf;
        const outputs = args.outputs.map((o, j) => ({ ...o, rho: buildRho(this.P, nf0, j) }));
        const outputClues =
            args.outputClues ?? outputs.map(() => this.clues.next());
        const outputAuxDigest = args.outputAuxDigest ?? TEST_AUX_DIGEST;
        return toCircomInput(this.P, this.J, {
            ...args,
            outputs,
            outputClues,
            outputAuxDigest,
        });
    }

    newTree(): MerkleTree {
        return new MerkleTree(this.P, this.depth);
    }
}

export async function buildTxBuilder(depth: number): Promise<TxBuilder> {
    const [P, J] = await Promise.all([Poseidon.build(), Jubjub.build()]);
    return new TxBuilder(P, J, depth);
}
