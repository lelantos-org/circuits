// tree_update_batch vectors.
//
// A batch commits `actual_count` leaves starting at `start_index`; the
// remaining slots are padding the circuit constrains to zero.

import {
    Jubjub,
    MerkleTree,
    Poseidon,
    abiEncodeCoeffs,
    batchCoeffs,
    batchDigest,
    batchLayoutNames,
    buildInner,
    commitWithInner,
    fiatShamirZ,
    flattenBatch,
    hornerEval,
    type Field,
} from "../../test/ref/index.js";
import { loadCircuit, readOutput, srcPath } from "../../test/lib/circuit.js";
import { padToSlots, treeUpdateBatchInputJson } from "../../test/lib/inputs.js";
import { DEPTH, MAX_L } from "../../test/lib/constants.js";
import {
    SCHEMA,
    hex,
    layoutDigest,
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
    /** Leaves already in the tree, making start_index non-zero. */
    prefilled: number;
    leaves: BatchLeafSpec[];
}

const BATCH_CASES: BatchCase[] = [
    {
        name: "single-deposit-empty-tree",
        description: "One deposit leaf into an empty tree; the circuit builds the leaf from the public amount.",
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

/** The owner half of every vector note; `rho` varies per slot. */
const VECTOR_PK = 0xabcn;
const VECTOR_RCM = 3n;

interface BuiltLeaf {
    /** What `cms[k]` carries: the note commitment on a spend leaf, `inner` on a deposit leaf. */
    word: Field;
    /** `Poseidon(TAG_INNER, pk, rho, rcm)` of the note. */
    inner: Field;
    /** The note commitment, which is the tree leaf on both kinds of slot. */
    leaf: Field;
    leafAsset: Field;
    leafPublicIn: Field;
    isDeposit: 0 | 1;
    rho: Field;
}

/**
 * Build a leaf from its spec. A deposit slot publishes `inner` beside the
 * asset and public amount, and the circuit hashes the three; a spend slot
 * publishes the commitment itself and zeroes the two amount fields.
 */
function buildLeafFor(P: Poseidon, l: BatchLeafSpec, k: number): BuiltLeaf {
    const rho = BigInt(k + 1);
    const inner = buildInner(P, { pk: VECTOR_PK, rho, rcm: VECTOR_RCM });
    const leaf = commitWithInner(P, l.asset, l.value, inner);
    return {
        word: l.isDeposit === 1 ? inner : leaf,
        inner,
        leaf,
        leafAsset: l.isDeposit === 1 ? l.asset : 0n,
        leafPublicIn: l.isDeposit === 1 ? l.value : 0n,
        isDeposit: l.isDeposit,
        rho,
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

        const built = c.leaves.map((l, k) => buildLeafFor(P, l, k));
        for (const b of built) tree.insert(b.leaf);
        const newRoot = tree.root();

        const witnessArgs = {
            oldRoot,
            newRoot,
            startIndex: c.prefilled,
            actualCount: built.length,
            cms: padToSlots(built.map((b) => b.word), MAX_L, 0n),
            leafAsset: padToSlots(built.map((b) => b.leafAsset), MAX_L, 0n),
            leafPublicIn: padToSlots(built.map((b) => b.leafPublicIn), MAX_L, 0n),
            isDeposit: padToSlots(built.map((b) => b.isDeposit as number), MAX_L, 0),
            frontier,
            digest: 0n,
            z: 0n,
        };

        const coeffSlots = {
            old_root: witnessArgs.oldRoot,
            new_root: witnessArgs.newRoot,
            start_index: witnessArgs.startIndex,
            actual_count: witnessArgs.actualCount,
            cms: witnessArgs.cms,
            leaf_asset: witnessArgs.leafAsset,
            leaf_public_in: witnessArgs.leafPublicIn,
            is_deposit: witnessArgs.isDeposit,
        };
        // The digest commits the 36 coefficients; z is hashed over those and the
        // digest word; y is evaluated over the coefficients alone.
        const digest = batchDigest(coeffSlots);
        const challenge = flattenBatch({ ...coeffSlots, digest });
        const z = fiatShamirZ(challenge);
        const y = hornerEval(batchCoeffs(coeffSlots), z);
        const witnessInput = treeUpdateBatchInputJson({ ...witnessArgs, digest, z });

        const w = await circuit.calculateWitness(witnessInput, true);
        await circuit.checkConstraints(w);
        const circuitY = readOutput(w, 0);
        const circuitDigest = readOutput(w, 1);
        if (circuitY !== y) {
            throw new Error(
                `${c.name}: circuit y (${circuitY}) != reference PolyEval y (${y}). ` +
                    `The layout in test/ref/compress.ts disagrees with BatchCompress.`,
            );
        }
        if (circuitDigest !== digest) {
            throw new Error(
                `${c.name}: circuit digest (${circuitDigest}) != reference CoeffDigest (${digest}).`,
            );
        }

        const compression: Compression = {
            coeffs: batchCoeffs(coeffSlots).map(s),
            digest: s(digest),
            challenge: challenge.map(s),
            abiEncodedChallenge: hex(abiEncodeCoeffs(challenge)),
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
                // Per slot: the calldata word and the leaf the tree holds, which
                // differ on a deposit slot:
                //   leaf = isDeposit ? Poseidon(TAG_CM, leafAsset·2^64 + leafPublicIn, cms) : cms
                leaves: built.map((b, k) => ({
                    slot: k,
                    cms: s(b.word),
                    leaf: s(b.leaf),
                    leafAsset: s(b.leafAsset),
                    leafPublicIn: s(b.leafPublicIn),
                    isDeposit: b.isDeposit,
                    // The note the leaf commits to.
                    note: {
                        asset: s(c.leaves[k].asset),
                        value: s(c.leaves[k].value),
                        pk: s(VECTOR_PK),
                        rho: s(b.rho),
                        rcm: s(VECTOR_RCM),
                        inner: s(b.inner),
                    },
                })),
            },
            witness: witnessInput,
            compression,
            circuitOutput: { y: s(circuitY), digest: s(circuitDigest) },
        });
    }

    return {
        schema: SCHEMA,
        circuit: {
            id: "tree_update_batch",
            template: `TreeUpdateBatch(${DEPTH}, ${MAX_L})`,
            source: "src/tree_update_batch.circom",
            shape: { depth: DEPTH, maxL: MAX_L },
            coeffCount: 4 + 4 * MAX_L,
            // The coefficients, then the digest word.
            challengeWords: 5 + 4 * MAX_L,
            // The verifier's `_pubSignals`, in order.
            publicSignals: ["y", "digest", "z"],
            layout,
            layoutDigest: layoutDigest(layout),
            // Empty: every input signal of the batch is evaluated into `y`, and
            // the one other preimage word, the digest, is a public signal.
            // `test/reference.test.ts` rejects any entry added here.
            //
            // The deposit fields must not be challenge-only: they are signals of
            // this circuit, and hashing a signal into `z` binds nothing because
            // the prover learns `z` before choosing the witness.
            challengeOnly: [] as string[],
        },
        constants: sharedConstants(P, J),
        vectors,
    };
}
