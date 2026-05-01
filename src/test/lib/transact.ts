// Transact-circuit witness builders shared by spec + fuzz tests.
//
// The original tests open-coded `insert` / `finalize` / `note` / `toCircomInput`
// in two files; they now live here so a single source builds witnesses.

import {
    Poseidon,
    Jubjub,
    MerkleTree,
    derivePk,
    commit,
    nullifier,
    toCircomInput,
    type Field,
    type Note,
    type SpentNote,
} from "../helpers";

// Default asset id used by tests that don't care which asset they're on.
export const DEFAULT_ASSET: Field = 7n;

export interface TxBuildArgs {
    publicAssetId: Field;
    publicIn: bigint;
    publicOut: bigint;
    inputs: SpentNote[];
    outputs: Note[];
    merkleRoot: Field;
    publicAssetGen?: [Field, Field];
}

export class TxBuilder {
    constructor(public readonly P: Poseidon, public readonly J: Jubjub, public readonly depth: number) {}

    note(value: bigint, ownerNsk: Field, rho: Field, asset: Field = DEFAULT_ASSET): Note {
        return { asset, value, pk: derivePk(this.P, ownerNsk), rho, rcm: rho + 1n, rcv: rho + 2n };
    }

    // Insert a note into `tree`, returning a SpentNote with empty proof — call
    // `finalize` once the tree's root is frozen to populate path/indices.
    insert(tree: MerkleTree, n: Note, nsk: Field): SpentNote {
        const cm = commit(this.P, n);
        const idx = tree.insert(cm);
        return {
            ...n, nsk, cm,
            nf: nullifier(this.P, nsk, n.rho),
            leafIndex: idx,
            pathElements: [], pathIndices: [], isDummy: false,
        };
    }

    finalize(tree: MerkleTree, sn: SpentNote): SpentNote {
        const { pathElements, pathIndices } = tree.proof(sn.leafIndex);
        return { ...sn, pathElements, pathIndices };
    }

    // Build the JSON object that the circuit consumes. `publicAssetGen` is
    // optional — when omitted, toCircomInput derives it from publicAssetId.
    build(args: TxBuildArgs): any {
        return toCircomInput(this.P, this.J, args);
    }

    newTree(): MerkleTree {
        return new MerkleTree(this.P, this.depth);
    }
}

export async function buildTxBuilder(depth: number): Promise<TxBuilder> {
    const [P, J] = await Promise.all([Poseidon.build(), Jubjub.build()]);
    return new TxBuilder(P, J, depth);
}
