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
    FMD_DEFAULT_GAMMA,
    fmdFlag,
    fmdFlagKeyFromDetection,
    fmdGenDetectionKey,
    BABYJUB_SUBGROUP_ORDER,
    type Field,
    type Note,
    type OutputClueWitness,
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
    /// Per-output FMD clue witnesses. When omitted, deterministic Poseidon-v2
    /// clues are synthesized so ClueCheck constraints are satisfied.
    outputClues?: OutputClueWitness[];
}

// Deterministic clue synth: tests don't care about clue contents, only that
// the witness satisfies ClueCheck. Build (dk, fk) once per builder, derive
// per-output r from a counter, and run `fmdFlag` so clue_bits[i] = 1 - bit_i
// holds by construction.
function makeClueGen(P: Poseidon, J: Jubjub) {
    const dk = fmdGenDetectionKey(() => 1n, FMD_DEFAULT_GAMMA);
    const fk = fmdFlagKeyFromDetection(J, dk);
    let counter = 0n;
    return (): OutputClueWitness => {
        counter += 1n;
        const r = (counter * 1234567n + 89n) % BABYJUB_SUBGROUP_ORDER;
        const clue = fmdFlag(J, P, fk, r === 0n ? 1n : r);
        // gamma=5 ⇒ clue.bits is 1 byte; pack to single Field (LSB-first).
        let packed = 0n;
        for (let i = 0; i < clue.bits.length; i++) {
            packed |= BigInt(clue.bits[i]) << BigInt(8 * i);
        }
        return { r, fk: fk.X, clueBits: packed };
    };
}

export class TxBuilder {
    private readonly nextClue: () => OutputClueWitness;
    constructor(public readonly P: Poseidon, public readonly J: Jubjub, public readonly depth: number) {
        this.nextClue = makeClueGen(P, J);
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
        const TAG_LEAF = 10n;
        const leaf = this.P.hash([TAG_LEAF, cm, cvDep[0], cvDep[1]]);
        const idx = tree.insert(leaf);
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

    // Build the JSON object that the circuit consumes. The public asset
    // generator is derived in-circuit from publicAssetId.
    build(args: TxBuildArgs): any {
        const outputClues =
            args.outputClues ?? args.outputs.map(() => this.nextClue());
        return toCircomInput(this.P, this.J, { ...args, outputClues });
    }

    newTree(): MerkleTree {
        return new MerkleTree(this.P, this.depth);
    }
}

export async function buildTxBuilder(depth: number): Promise<TxBuilder> {
    const [P, J] = await Promise.all([Poseidon.build(), Jubjub.build()]);
    return new TxBuilder(P, J, depth);
}
