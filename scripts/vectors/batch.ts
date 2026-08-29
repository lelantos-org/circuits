// tree_update_batch vectors.
//
// A batch commits `actual_count` individual leaves starting at `start_index`;
// the remaining slots are padding the circuit constrains to zero. Cases cover
// a single deposit, the odd count a 3-output transact bundle produces, and a
// mixed deposit/spend batch at a non-zero start index.

import {
    Jubjub,
    MerkleTree,
    Poseidon,
    abiEncodeCoeffs,
    batchLayoutNames,
    buildLeaf,
    fiatShamirZ,
    flattenBatch,
    hornerEval,
    type Field,
    type Point,
} from "../../test/ref/index.js";
import { loadCircuit, readOutput, srcPath } from "../../test/lib/circuit.js";
import { padToSlots, treeUpdateBatchInputJson } from "../../test/lib/inputs.js";
import { DEPTH, MAX_L } from "../../test/lib/constants.js";
import {
    SCHEMA,
    hex,
    layoutDigest,
    pt,
    s,
    sharedConstants,
    type Compression,
} from "./common.js";

interface BatchLeafSpec {
    asset: bigint;
    value: bigint;
    isDeposit: 0 | 1;
}

interface BatchCase {
    name: string;
    description: string;
    /** Throwaway leaves already in the tree, so start_index is non-zero. */
    prefilled: number;
    leaves: BatchLeafSpec[];
}

const BATCH_CASES: BatchCase[] = [
    {
        name: "single-deposit-empty-tree",
        description: "One deposit leaf into an empty tree; per-leaf binding active.",
        prefilled: 0,
        leaves: [{ asset: 7n, value: 1000n, isDeposit: 1 }],
    },
    {
        name: "odd-three-leaf-batch",
        description: "Three leaves — the odd count a 3-output transact bundle produces.",
        prefilled: 0,
        leaves: [
            { asset: 7n, value: 10n, isDeposit: 1 },
            { asset: 7n, value: 20n, isDeposit: 0 },
            { asset: 9n, value: 30n, isDeposit: 1 },
        ],
    },
    {
        name: "mixed-batch-nonzero-start",
        description: "Deposit and spend leaves in one batch at a non-zero start index.",
        prefilled: 5,
        leaves: [
            { asset: 7n, value: 42n, isDeposit: 1 },
            { asset: 7n, value: 7n, isDeposit: 0 },
        ],
    },
];

/** One built leaf: the commitment, its deposit anchor, and the leaf hash of both. */
interface BuiltLeaf {
    cm: Field;
    cvDep: Point;
    leaf: Field;
    leafAsset: Field;
    leafPublicIn: Field;
    isDeposit: 0 | 1;
    rcv: Field;
}

/**
 * Build a leaf from its spec.
 *
 * The commitment is hashed directly rather than via `buildNoteCommitment`: the
 * batch circuit constrains no note structure, so a distinct well-formed field
 * element suffices. Only deposit leaves declare an asset and a public_in; a
 * spend leaf zeroes both and skips the binding check.
 */
function buildLeafFor(P: Poseidon, J: Jubjub, l: BatchLeafSpec, k: number): BuiltLeaf {
    const rho = BigInt(k + 1);
    const rcvDep = BigInt(5 * (k + 1));
    const cm = P.hash([l.asset * (1n << 64n) + l.value, 0xabcn, rho, 3n]);
    const cvDep = J.valueCommit(l.value, J.hashToAssetGen(l.asset), rcvDep);
    return {
        cm,
        cvDep,
        leaf: buildLeaf(P, cm, cvDep),
        leafAsset: l.isDeposit === 1 ? l.asset : 0n,
        leafPublicIn: l.isDeposit === 1 ? l.value : 0n,
        isDeposit: l.isDeposit,
        rcv: rcvDep,
    };
}

export async function buildBatchVectors() {
    const [P, J] = await Promise.all([Poseidon.build(), Jubjub.build()]);
    const circuit = await loadCircuit(srcPath("tree_update_batch.circom"));
    const layout = batchLayoutNames(MAX_L);

    const vectors = [];

    for (const c of BATCH_CASES) {
        const tree = new MerkleTree(P, DEPTH);
        for (let i = 0; i < c.prefilled; i++) tree.insert(BigInt(0xdead + i));
        const oldRoot = tree.root();
        const frontier = tree.frontier();

        const built = c.leaves.map((l, k) => buildLeafFor(P, J, l, k));
        for (const b of built) tree.insert(b.leaf);
        const newRoot = tree.root();

        const witnessArgs = {
            oldRoot,
            newRoot,
            startIndex: c.prefilled,
            actualCount: built.length,
            cms: padToSlots(built.map((b) => b.cm), MAX_L, 0n),
            cvDep: padToSlots(built.map((b) => b.cvDep), MAX_L, [0n, 0n] as Point),
            leafAsset: padToSlots(built.map((b) => b.leafAsset), MAX_L, 0n),
            leafPublicIn: padToSlots(built.map((b) => b.leafPublicIn), MAX_L, 0n),
            isDeposit: padToSlots(built.map((b) => b.isDeposit as number), MAX_L, 0),
            rcv: padToSlots(built.map((b) => b.rcv), MAX_L, 0n),
            frontier,
            z: 0n,
        };

        const coeffs = flattenBatch({
            old_root: witnessArgs.oldRoot,
            new_root: witnessArgs.newRoot,
            start_index: witnessArgs.startIndex,
            actual_count: witnessArgs.actualCount,
            cms: witnessArgs.cms,
            cv_dep: witnessArgs.cvDep,
            leaf_asset: witnessArgs.leafAsset,
            leaf_public_in: witnessArgs.leafPublicIn,
            is_deposit: witnessArgs.isDeposit,
        });
        const z = fiatShamirZ(coeffs);
        const y = hornerEval(coeffs, z);
        const witnessInput = treeUpdateBatchInputJson({ ...witnessArgs, z });

        const w = await circuit.calculateWitness(witnessInput, true);
        await circuit.checkConstraints(w);
        const circuitY = readOutput(w);
        if (circuitY !== y) {
            throw new Error(
                `${c.name}: circuit y (${circuitY}) != reference PolyEval y (${y}). ` +
                    `The layout in test/ref/compress.ts disagrees with BatchCompress.`,
            );
        }

        const compression: Compression = {
            coeffs: coeffs.map(s),
            abiEncodedCoeffs: hex(abiEncodeCoeffs(coeffs)),
            zDerivation: "fiat-shamir",
            z: s(z),
            y: s(y),
        };

        vectors.push({
            name: c.name,
            description: c.description,
            expect: "accept",
            intermediates: {
                startIndex: c.prefilled,
                actualCount: built.length,
                oldRoot: s(oldRoot),
                newRoot: s(newRoot),
                frontierIn: frontier.map((lvl) => lvl.map(s)),
                leaves: built.map((b, k) => ({
                    slot: k,
                    cm: s(b.cm),
                    cvDep: pt(b.cvDep),
                    leafHash: s(b.leaf),
                    leafAsset: s(b.leafAsset),
                    leafPublicIn: s(b.leafPublicIn),
                    isDeposit: b.isDeposit,
                    rcv: s(b.rcv),
                })),
                assetGens: [...new Set(c.leaves.map((l) => l.asset))].map((a) => ({
                    assetId: s(a),
                    gen: pt(J.hashToAssetGen(a)),
                })),
            },
            witness: witnessInput,
            compression,
            circuitOutput: { y: s(circuitY) },
        });
    }

    return {
        schema: SCHEMA,
        circuit: {
            id: "tree_update_batch",
            template: `TreeUpdateBatch(${DEPTH}, ${MAX_L})`,
            source: "src/tree_update_batch.circom",
            shape: { depth: DEPTH, maxL: MAX_L },
            coeffCount: 4 + 6 * MAX_L,
            layout,
            layoutDigest: layoutDigest(layout),
            unconstrained: [],
        },
        constants: sharedConstants(P, J),
        vectors,
    };
}
