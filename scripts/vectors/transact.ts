// Transact vectors for every shipped shape (4x6 only); one case produces one
// vector. The construction matches `TxBuilder` in test/lib/transact.ts but
// keeps its own leaf and dummy bookkeeping, since the published `intermediates`
// block exposes values TxBuilder does not return.

import {
    Jubjub,
    MerkleTree,
    Poseidon,
    buildInner,
    buildNoteCommitment,
    buildNullifierFromNsk,
    buildRho,
    derivePk,
    deriveIvk,
    deriveNk,
    deterministicClueGen,
    dummyInputAt,
    abiEncodeCoeffs,
    circuitSignals,
    coeffs,
    digestPrefix,
    fiatShamirZ,
    flatten,
    hornerEval,
    toCircomInput,
    FMD_DEFAULT_GAMMA,
    type Field,
    type Note,
    type SpentNote,
} from "../../test/ref/index.js";
import { loadCircuit, readOutput, srcPath } from "../../test/lib/circuit.js";
import { TEST_AUX_DIGEST, TEST_INTENT_HASH } from "../../test/lib/transact.js";
import {
    SCHEMA,
    hex,
    layoutDigest,
    pt,
    readLeanLayout,
    s,
    sharedConstants,
    type Compression,
} from "./common.js";

interface TransactCase {
    name: string;
    description: string;
    /** One entry per input slot; a null entry becomes a dummy slot. */
    inputs: ({ nsk: bigint; value: bigint } | null)[];
    outputs: { nsk: bigint; value: bigint }[];
    /** Withdrawn from the pool, in `asset`. Zero for a transfer. */
    publicOut: bigint;
    asset: bigint;
}

/**
 * The transparent bucket's asset id: the circuit requires 0 when nothing is
 * withdrawn, so a transfer does not publish the asset it moves.
 */
function publicAssetOf(c: TransactCase): bigint {
    return c.publicOut === 0n ? 0n : c.asset;
}

interface TransactShape {
    /** Shape id, matching `lean/expected/layout-<id>.txt`. */
    id: string;
    nIn: number;
    nOut: number;
    /**
     * Quaternary tree depth this shape's circuit is instantiated at; the
     * Merkle path length in the witness must match it.
     */
    depth: number;
    source: string;
    cases: TransactCase[];
}

/** A real input's leaf, published so the SDK can rebuild the tree. */
interface RealLeafMeta {
    slot: number;
    /** The note commitment, which is the tree leaf. */
    cm: Field;
    leafIndex: number;
    nsk: bigint;
}

/** A dummy slot's `rho`, published so the SDK can reproduce its nullifier. */
interface DummyMeta {
    slot: number;
    rho: Field;
}

// Value conservation the circuit enforces, per asset:
//   sum(input values) == sum(output values) + public_out
export const TRANSACT_SHAPES: TransactShape[] = [
    {
        id: "4x6",
        nIn: 4,
        nOut: 6,
        depth: 11,
        source: "src/4x6.circom",
        // These vectors pin the 38-word challenge preimage, whose leading 13
        // words are the coefficients, as a byte-exact target for the
        // `PubInputs.compress` overload.
        cases: [
            {
                name: "internal-4in6out-balanced",
                description:
                    "Four real inputs, six real outputs, nothing withdrawn: "
                    + "public_asset_id is 0.",
                inputs: [
                    { nsk: 11n, value: 100n },
                    { nsk: 12n, value: 50n },
                    { nsk: 13n, value: 25n },
                    { nsk: 14n, value: 25n },
                ],
                outputs: [
                    { nsk: 21n, value: 60n },
                    { nsk: 22n, value: 50n },
                    { nsk: 23n, value: 40n },
                    { nsk: 24n, value: 30n },
                    { nsk: 25n, value: 15n },
                    { nsk: 26n, value: 5n },
                ],
                publicOut: 0n,
                asset: 7n,
            },
            {
                name: "transfer-3in6out-one-dummy",
                description: "One dummy input slot; three real notes transferred.",
                inputs: [
                    { nsk: 11n, value: 100n },
                    { nsk: 12n, value: 50n },
                    { nsk: 13n, value: 25n },
                    null,
                ],
                outputs: [
                    { nsk: 21n, value: 60n },
                    { nsk: 22n, value: 50n },
                    { nsk: 23n, value: 30n },
                    { nsk: 24n, value: 20n },
                    { nsk: 25n, value: 15n },
                    { nsk: 26n, value: 0n },
                ],
                publicOut: 0n,
                asset: 7n,
            },
            {
                name: "withdraw-4in6out-public-out",
                description:
                    "Value leaves via public_out under the note's asset id, with change "
                    + "split across six slots: the decomposition the six-output shape exists for.",
                inputs: [
                    { nsk: 11n, value: 100n },
                    { nsk: 12n, value: 100n },
                    { nsk: 13n, value: 50n },
                    { nsk: 14n, value: 30n },
                ],
                outputs: [
                    { nsk: 21n, value: 40n },
                    { nsk: 22n, value: 30n },
                    { nsk: 23n, value: 25n },
                    { nsk: 24n, value: 15n },
                    { nsk: 25n, value: 10n },
                    { nsk: 26n, value: 10n },
                ],
                publicOut: 150n,
                asset: 7n,
            },
        ],
    },
];

/**
 * Reject a case the circuit would reject, so a mis-specified case surfaces here
 * rather than as a constraint failure inside circom.
 */
function validateCase(shape: TransactShape, c: TransactCase): void {
    if (c.inputs.length !== shape.nIn || c.outputs.length !== shape.nOut) {
        throw new Error(
            `${shape.id}/${c.name}: case has ${c.inputs.length}x${c.outputs.length}, ` +
                `shape is ${shape.nIn}x${shape.nOut}`,
        );
    }
    const inSum = c.inputs.reduce((a, i) => a + (i?.value ?? 0n), 0n);
    const outSum = c.outputs.reduce((a, o) => a + o.value, 0n);
    if (inSum !== outSum + c.publicOut) {
        throw new Error(
            `${shape.id}/${c.name}: unbalanced — in ${inSum} != ` +
                `out ${outSum} + publicOut ${c.publicOut}`,
        );
    }
}

/**
 * The diversifier a vector key's `pk` is derived under: 128-bit, non-zero and
 * distinct per key. Published per key in `intermediates.keys`.
 */
function keyDiversifier(nsk: bigint): Field {
    return (1n << 127n) | nsk;
}

/** `rcm` is rho + 1, as in `TxBuilder.note`; `pk` is under the key's diversifier. */
function note(P: Poseidon, asset: Field, nsk: bigint, value: bigint, rho: Field): Note {
    return { asset, value, pk: derivePk(P, nsk, keyDiversifier(nsk)), rho, rcm: rho + 1n };
}

/**
 * Insert every real input into `tree`, in slot order. Returns the spent notes
 * with empty proofs, since the root is not yet frozen, plus the leaves the
 * published `intermediates` block exposes.
 */
function insertRealInputs(P: Poseidon, tree: MerkleTree, c: TransactCase) {
    const spent: SpentNote[] = [];
    const realMeta: RealLeafMeta[] = [];

    c.inputs.forEach((inp, i) => {
        if (!inp) return;
        const n = note(P, c.asset, inp.nsk, inp.value, BigInt(1000 * (i + 1)));
        const cm = buildNoteCommitment(P, n);
        const leafIndex = tree.insert(cm);
        spent.push({
            ...n,
            nsk: inp.nsk,
            d: keyDiversifier(inp.nsk),
            cm,
            nf: buildNullifierFromNsk(P, inp.nsk, n.rho, cm),
            leafIndex,
            pathElements: [],
            pathIndices: [],
            isDummy: false,
        });
        realMeta.push({ slot: i, cm, leafIndex, nsk: inp.nsk });
    });

    return { spent, realMeta };
}

/** Reassemble the input array in slot order, filling dummies where asked. */
function fillSlots(P: Poseidon, depth: number, c: TransactCase, finalizedReal: SpentNote[]) {
    let realCursor = 0;
    const dummyMeta: DummyMeta[] = [];

    const inputs: SpentNote[] = c.inputs.map((inp, i) => {
        if (inp) return finalizedReal[realCursor++];
        const rho = BigInt(90000 + i);
        dummyMeta.push({ slot: i, rho });
        return dummyInputAt(P, depth, rho);
    });

    return { inputs, dummyMeta };
}

/**
 * Two-pass Fiat-Shamir: build the witness at z = 0, flatten it into the
 * challenge preimage, hash that into the real z, then set z. The coefficient
 * digest is fixed in the first pass: it is a function of the coefficient
 * signals alone and is itself a word of the preimage.
 *
 * `flatten` and `coeffs` differ: 38 words hashed, 13 evaluated.
 */
function buildWitness(
    P: Poseidon,
    c: TransactCase,
    inputs: SpentNote[],
    outputs: Note[],
    clueList: ReturnType<ReturnType<typeof deterministicClueGen>["next"]>[],
    merkleRoot: Field,
) {
    const base = toCircomInput(P, {
        publicAssetId: publicAssetOf(c),
        publicOut: c.publicOut,
        inputs,
        outputs,
        outputClues: clueList,
        merkleRoot,
        outputAuxDigest: TEST_AUX_DIGEST,
        // Nonzero, so consumers exercise the word's position and full width
        // rather than matching on a zero value.
        intentHash: TEST_INTENT_HASH,
        z: 0n,
    });
    const challenge = flatten(base);
    const z = fiatShamirZ(challenge);
    const polyCoeffs = coeffs(base);
    return {
        witnessInput: { ...base, z: s(z) },
        challenge,
        coeffs: polyCoeffs,
        z,
        y: hornerEval(polyCoeffs, z),
    };
}

function compressionOf(
    challenge: Field[],
    polyCoeffs: Field[],
    digest: string,
    z: Field,
    y: Field,
): Compression {
    return {
        challenge: challenge.map(s),
        abiEncodedChallenge: hex(abiEncodeCoeffs(challenge)),
        coeffs: polyCoeffs.map(s),
        digest,
        zDerivation: "fiat-shamir",
        z: s(z),
        y: s(y),
    };
}

export async function buildTransactVectors(shape: TransactShape) {
    const layout = readLeanLayout(shape.id);
    const [P, J] = await Promise.all([Poseidon.build(), Jubjub.build()]);
    const circuit = await loadCircuit(srcPath(shape.source.replace(/^src\//, "")));

    const vectors = [];

    for (const c of shape.cases) {
        validateCase(shape, c);

        const clues = deterministicClueGen(P, J);
        const tree = new MerkleTree(P, shape.depth);

        const { spent, realMeta } = insertRealInputs(P, tree, c);
        const merkleRoot = tree.root();
        const finalizedReal = spent.map((sn) => ({ ...sn, ...tree.proof(sn.leafIndex) }));
        const { inputs, dummyMeta } = fillSlots(P, shape.depth, c, finalizedReal);

        // Output rho is forced to the derivation the circuit enforces; `rcm`
        // stays the value `note` gave it.
        const nf0 = inputs[0].nf;
        const outputs: Note[] = c.outputs.map((o, j) => ({
            ...note(P, c.asset, o.nsk, o.value, BigInt(3000 * (j + 1))),
            rho: buildRho(P, nf0, j),
        }));
        const clueList = outputs.map(() => clues.next());

        const { witnessInput, challenge, coeffs: polyCoeffs, z, y } =
            buildWitness(P, c, inputs, outputs, clueList, merkleRoot);

        // The compiled circuit is the oracle for `y`. `circuitSignals` drops the
        // challenge-only fields: the witness calculator rejects a key the
        // circuit does not declare.
        const w = await circuit.calculateWitness(circuitSignals(witnessInput), true);
        await circuit.checkConstraints(w);
        const circuitY = readOutput(w, 0);
        const circuitDigest = readOutput(w, 1);
        if (circuitY !== y) {
            throw new Error(
                `${c.name}: circuit y (${circuitY}) != reference PolyEval y (${y}). ` +
                    `The layout in test/ref/compress.ts disagrees with TransactCompressN.`,
            );
        }
        if (s(circuitDigest) !== witnessInput.digest) {
            throw new Error(
                `${c.name}: circuit digest (${circuitDigest}) != reference CoeffDigest ` +
                    `(${witnessInput.digest}).`,
            );
        }
        if (polyCoeffs.length !== layout.length) {
            throw new Error(
                `${c.name}: ${polyCoeffs.length} coefficients but the Lean layout names ` +
                    `${layout.length}`,
            );
        }

        const keys = [...new Set(
            c.inputs.filter(Boolean).map((i) => i!.nsk).concat(c.outputs.map((o) => o.nsk)),
        )].sort((a, b) => (a < b ? -1 : 1));

        vectors.push({
            name: c.name,
            description: c.description,
            expect: "accept",
            intermediates: {
                keys: keys.map((nsk) => ({
                    nsk: s(nsk),
                    ivk: s(deriveIvk(P, nsk)),
                    nk: s(deriveNk(P, nsk)),
                    // pk = Poseidon(TAG_PK, ivk, d).
                    d: s(keyDiversifier(nsk)),
                    pk: s(derivePk(P, nsk, keyDiversifier(nsk))),
                })),
                // Every note commits in two steps:
                //   inner = Poseidon(TAG_INNER, pk, rho, rcm)
                //   cm    = Poseidon(TAG_CM, asset·2^64 + value, inner)
                // and cm is the tree leaf.
                inputs: inputs.map((n, i) => ({
                    slot: i,
                    isDummy: n.isDummy,
                    inner: s(buildInner(P, n)),
                    cm: s(n.cm),
                    nf: s(n.nf),
                    leafIndex: n.leafIndex,
                })),
                realLeaves: realMeta.map((m) => ({
                    slot: m.slot,
                    leaf: s(m.cm),
                    leafIndex: m.leafIndex,
                })),
                dummies: dummyMeta.map((d) => ({
                    slot: d.slot,
                    rho: s(d.rho),
                })),
                outputs: outputs.map((o, j) => ({
                    slot: j,
                    rho: s(o.rho),
                    inner: s(buildInner(P, o)),
                    cm: s(buildNoteCommitment(P, o)),
                })),
                // The second public signal: a Poseidon(5) fold over the
                // coefficients, four per block, zero-padded,
                //   h_0     = Poseidon(TAG_DIGEST, w[0..3])
                //   h_{b+1} = Poseidon(h_b, w[4b+4 .. 4b+7])
                digest: {
                    absorbed: digestPrefix(witnessInput).map(s),
                    value: witnessInput.digest,
                },
                merkle: {
                    depth: shape.depth,
                    leaves: tree.leaves.map(s),
                    root: s(merkleRoot),
                    proofs: finalizedReal.map((sn) => ({
                        leafIndex: sn.leafIndex,
                        pathElements: sn.pathElements.map((lvl) => lvl.map(s)),
                        pathIndices: sn.pathIndices,
                    })),
                },
                fmd: {
                    gamma: FMD_DEFAULT_GAMMA,
                    dkX: clues.dk.x.map(s),
                    fkX: clues.fk.X.map(pt),
                    perOutput: clueList.map((clue, j) => ({
                        slot: j,
                        r: s(clue.r),
                        cluePackedR: hex(clue.clue.R),
                        clueBitsPacked: hex(clue.clue.bits),
                        clueRx: s(clue.clueRx),
                        clueRy: s(clue.clueRy),
                        clueBits: s(clue.clueBits),
                    })),
                },
            },
            witness: witnessInput,
            compression: compressionOf(challenge, polyCoeffs, witnessInput.digest, z, y),
            circuitOutput: { y: s(circuitY), digest: s(circuitDigest) },
        });
    }

    return {
        schema: SCHEMA,
        circuit: {
            id: "transact",
            template: `Transact(${shape.depth}, ${shape.nIn}, ${shape.nOut})`,
            source: shape.source,
            shape: { depth: shape.depth, nIn: shape.nIn, nOut: shape.nOut },
            coeffCount: 3 + shape.nIn + shape.nOut,
            challengeWords: 10 + shape.nIn + 4 * shape.nOut,
            // The verifier's `_pubSignals`, in order.
            publicSignals: ["y", "digest", "z"],
            layout,
            layoutDigest: layoutDigest(layout),
            // The circuit has no signal for these, so they are not coefficients:
            // they enter the challenge preimage and bind through `z`. `digest`
            // is not listed: it is hashed too, but the verifier compares it as a
            // public signal against the circuit's own output.
            challengeOnly: [
                "recipient_address",
                "chain_id",
                "payer_address",
                "relayer_address",
                "intent_hash",
                "out_clue_Rx",
                "out_clue_Ry",
                "out_clue_bits",
                "out_aux_digest",
            ],
        },
        constants: sharedConstants(P, J),
        vectors,
    };
}
