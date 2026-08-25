// Transact vectors, for every shipped shape (2x2, 3x3, 4x4).
//
// One case produces one vector. The construction matches `TxBuilder` in
// src/test/lib/transact.ts — same note derivation, forced output rho and aux
// digest — but keeps its own leaf and dummy bookkeeping, since the published
// `intermediates` block exposes values TxBuilder does not return.

import {
    Jubjub,
    MerkleTree,
    Poseidon,
    buildLeaf,
    buildNoteCommitment,
    buildNullifierFromNsk,
    buildRho,
    derivePk,
    deriveIvk,
    deriveNk,
    deterministicClueGen,
    dummyInputAt,
    abiEncodeCoeffs,
    fiatShamirZ,
    flatten,
    hornerEval,
    toCircomInput,
    FMD_DEFAULT_GAMMA,
    type Field,
    type Note,
    type Point,
    type SpentNote,
} from "../../src/test/ref/index.js";
import { loadCircuit, readOutput, srcPath } from "../../src/test/lib/circuit.js";
import { DEPTH } from "../../src/test/lib/constants.js";
import { TEST_AUX_DIGEST } from "../../src/test/lib/transact.js";
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
    publicIn: bigint;
    publicOut: bigint;
    asset: bigint;
}

interface TransactShape {
    /** Shape id, matching `lean/expected/layout-<id>.txt`. */
    id: string;
    nIn: number;
    nOut: number;
    source: string;
    cases: TransactCase[];
}

/** A real input's leaf preimage, published so the SDK can rebuild the tree. */
interface RealLeafMeta {
    slot: number;
    cm: Field;
    cvDep: Point;
    leaf: Field;
    leafIndex: number;
    nsk: bigint;
}

/** A dummy slot's derived blinders, published so the SDK can reproduce them. */
interface DummyMeta {
    slot: number;
    rho: Field;
    rcv: Field;
    rcvDep: Field;
}

// Value conservation the circuit enforces, per asset:
//   sum(input values) + public_in == sum(output values) + public_out
export const TRANSACT_SHAPES: TransactShape[] = [
    {
        id: "2x2",
        nIn: 2,
        nOut: 2,
        source: "src/2x2.circom",
        cases: [
            {
                name: "internal-2in2out-balanced",
                description: "Two real inputs, two real outputs, no public flow.",
                inputs: [
                    { nsk: 11n, value: 100n },
                    { nsk: 12n, value: 50n },
                ],
                outputs: [
                    { nsk: 21n, value: 90n },
                    { nsk: 22n, value: 60n },
                ],
                publicIn: 0n,
                publicOut: 0n,
                asset: 7n,
            },
            {
                name: "deposit-1in2out-public-in",
                description: "One dummy input; value enters the pool via public_in.",
                inputs: [{ nsk: 11n, value: 100n }, null],
                outputs: [
                    { nsk: 21n, value: 130n },
                    { nsk: 22n, value: 20n },
                ],
                publicIn: 50n,
                publicOut: 0n,
                asset: 7n,
            },
            {
                name: "withdraw-2in2out-public-out",
                description: "Value leaves the pool via public_out.",
                inputs: [
                    { nsk: 11n, value: 100n },
                    { nsk: 12n, value: 100n },
                ],
                outputs: [
                    { nsk: 21n, value: 80n },
                    { nsk: 22n, value: 40n },
                ],
                publicIn: 0n,
                publicOut: 80n,
                asset: 7n,
            },
        ],
    },
    {
        id: "3x3",
        nIn: 3,
        nOut: 3,
        source: "src/3x3.circom",
        // Built and published, but not yet wired on-chain: that requires a
        // 42-slot `PubInputs.compress` overload. These vectors pin the 42-slot
        // layout the Lean development proves against, so the on-chain side has a
        // byte-exact target.
        cases: [
            {
                name: "internal-3in3out-balanced",
                description: "Three real inputs, three real outputs, no public flow.",
                inputs: [
                    { nsk: 11n, value: 100n },
                    { nsk: 12n, value: 50n },
                    { nsk: 13n, value: 25n },
                ],
                outputs: [
                    { nsk: 21n, value: 90n },
                    { nsk: 22n, value: 60n },
                    { nsk: 23n, value: 25n },
                ],
                publicIn: 0n,
                publicOut: 0n,
                asset: 7n,
            },
            {
                name: "deposit-2in3out-public-in",
                description: "One dummy input slot; value enters the pool via public_in.",
                inputs: [{ nsk: 11n, value: 100n }, { nsk: 12n, value: 50n }, null],
                outputs: [
                    { nsk: 21n, value: 90n },
                    { nsk: 22n, value: 60n },
                    { nsk: 23n, value: 30n },
                ],
                publicIn: 30n,
                publicOut: 0n,
                asset: 7n,
            },
            {
                name: "withdraw-3in3out-public-out",
                description: "Value leaves the pool via public_out.",
                inputs: [
                    { nsk: 11n, value: 100n },
                    { nsk: 12n, value: 100n },
                    { nsk: 13n, value: 50n },
                ],
                outputs: [
                    { nsk: 21n, value: 80n },
                    { nsk: 22n, value: 40n },
                    { nsk: 23n, value: 50n },
                ],
                publicIn: 0n,
                publicOut: 80n,
                asset: 7n,
            },
        ],
    },
    {
        id: "4x4",
        nIn: 4,
        nOut: 4,
        source: "src/4x4.circom",
        // Neither deployed nor wired on-chain: that requires a 53-slot
        // `PubInputs.compress` overload, and a verifier built on a 2^17 ptau.
        // These vectors pin the 53-slot layout the Lean development proves
        // against, so the on-chain side has a byte-exact target.
        cases: [
            {
                name: "internal-4in4out-balanced",
                description: "Four real inputs, four real outputs, no public flow.",
                inputs: [
                    { nsk: 11n, value: 100n },
                    { nsk: 12n, value: 50n },
                    { nsk: 13n, value: 25n },
                    { nsk: 14n, value: 25n },
                ],
                outputs: [
                    { nsk: 21n, value: 90n },
                    { nsk: 22n, value: 60n },
                    { nsk: 23n, value: 25n },
                    { nsk: 24n, value: 25n },
                ],
                publicIn: 0n,
                publicOut: 0n,
                asset: 7n,
            },
            {
                name: "deposit-3in4out-public-in",
                description: "One dummy input slot; value enters the pool via public_in.",
                inputs: [
                    { nsk: 11n, value: 100n },
                    { nsk: 12n, value: 50n },
                    { nsk: 13n, value: 25n },
                    null,
                ],
                outputs: [
                    { nsk: 21n, value: 90n },
                    { nsk: 22n, value: 60n },
                    { nsk: 23n, value: 30n },
                    { nsk: 24n, value: 25n },
                ],
                publicIn: 30n,
                publicOut: 0n,
                asset: 7n,
            },
            {
                name: "withdraw-4in4out-public-out",
                description: "Value leaves the pool via public_out.",
                inputs: [
                    { nsk: 11n, value: 100n },
                    { nsk: 12n, value: 100n },
                    { nsk: 13n, value: 50n },
                    { nsk: 14n, value: 30n },
                ],
                outputs: [
                    { nsk: 21n, value: 80n },
                    { nsk: 22n, value: 40n },
                    { nsk: 23n, value: 50n },
                    { nsk: 24n, value: 30n },
                ],
                publicIn: 0n,
                publicOut: 80n,
                asset: 7n,
            },
        ],
    },
];

/**
 * Reject a case the circuit would reject.
 *
 * Catches a mis-specified case here rather than as an opaque constraint failure
 * inside circom.
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
    if (inSum + c.publicIn !== outSum + c.publicOut) {
        throw new Error(
            `${shape.id}/${c.name}: unbalanced — in ${inSum} + publicIn ${c.publicIn} != ` +
                `out ${outSum} + publicOut ${c.publicOut}`,
        );
    }
}

/** Note derivation shared with `TxBuilder.note`: blinders are rho + 1..3. */
function note(P: Poseidon, asset: Field, nsk: bigint, value: bigint, rho: Field): Note {
    return { asset, value, pk: derivePk(P, nsk), rho, rcm: rho + 1n, rcv: rho + 2n, rcvDep: rho + 3n };
}

/**
 * Insert every real input into `tree`, in slot order.
 *
 * Returns the spent notes with empty proofs, since the root is not yet frozen,
 * plus the leaf preimages the published `intermediates` block exposes.
 */
function insertRealInputs(P: Poseidon, J: Jubjub, tree: MerkleTree, c: TransactCase) {
    const spent: SpentNote[] = [];
    const realMeta: RealLeafMeta[] = [];

    c.inputs.forEach((inp, i) => {
        if (!inp) return;
        const n = note(P, c.asset, inp.nsk, inp.value, BigInt(1000 * (i + 1)));
        const cm = buildNoteCommitment(P, n);
        const cvDep = J.valueCommit(n.value, J.hashToAssetGen(n.asset), n.rcvDep);
        const leaf = buildLeaf(P, cm, cvDep);
        const leafIndex = tree.insert(leaf);
        spent.push({
            ...n,
            nsk: inp.nsk,
            cm,
            nf: buildNullifierFromNsk(P, inp.nsk, n.rho, cm),
            leafIndex,
            pathElements: [],
            pathIndices: [],
            isDummy: false,
        });
        realMeta.push({ slot: i, cm, cvDep, leaf, leafIndex, nsk: inp.nsk });
    });

    return { spent, realMeta };
}

/** Reassemble the input array in slot order, filling dummies where asked. */
function fillSlots(P: Poseidon, c: TransactCase, finalizedReal: SpentNote[]) {
    let realCursor = 0;
    const dummyMeta: DummyMeta[] = [];

    const inputs: SpentNote[] = c.inputs.map((inp, i) => {
        if (inp) return finalizedReal[realCursor++];
        const rho = BigInt(90000 + i);
        // Blinders come from a deterministic derivation over rho; read them back
        // off the result rather than recomputing the derivation here.
        const dummy = dummyInputAt(P, DEPTH, rho);
        dummyMeta.push({ slot: i, rho, rcv: dummy.rcv, rcvDep: dummy.rcvDep });
        return dummy;
    });

    return { inputs, dummyMeta };
}

/**
 * Two-pass Fiat-Shamir: build the witness at z = 0, flatten it, hash the
 * coefficients into the real z, then rebuild. `z` is a public input, so it
 * cannot be part of what derives it.
 */
function buildWitness(
    P: Poseidon,
    J: Jubjub,
    c: TransactCase,
    inputs: SpentNote[],
    outputs: Note[],
    clueList: ReturnType<ReturnType<typeof deterministicClueGen>["next"]>[],
    merkleRoot: Field,
) {
    const base = toCircomInput(P, J, {
        publicAssetId: c.asset,
        publicIn: c.publicIn,
        publicOut: c.publicOut,
        inputs,
        outputs,
        outputClues: clueList,
        merkleRoot,
        outputAuxDigest: TEST_AUX_DIGEST,
        z: 0n,
    });
    const coeffs = flatten(base);
    const z = fiatShamirZ(coeffs);
    return { witnessInput: { ...base, z: s(z) }, coeffs, z, y: hornerEval(coeffs, z) };
}

function compressionOf(coeffs: Field[], z: Field, y: Field): Compression {
    return {
        coeffs: coeffs.map(s),
        abiEncodedCoeffs: hex(abiEncodeCoeffs(coeffs)),
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
        const tree = new MerkleTree(P, DEPTH);

        const { spent, realMeta } = insertRealInputs(P, J, tree, c);
        const merkleRoot = tree.root();
        const finalizedReal = spent.map((sn) => ({ ...sn, ...tree.proof(sn.leafIndex) }));
        const { inputs, dummyMeta } = fillSlots(P, c, finalizedReal);

        // Output rho is forced to the derivation the circuit enforces. Only
        // `rho` is replaced: rcm/rcv/rcvDep are rho + k, and a derived rho is a
        // full-width Poseidon output, so deriving the blinders from it would put
        // rcv above the Num2Bits(RCV_BITS) width MulH enforces.
        const nf0 = inputs[0].nf;
        const outputs: Note[] = c.outputs.map((o, j) => ({
            ...note(P, c.asset, o.nsk, o.value, BigInt(3000 * (j + 1))),
            rho: buildRho(P, nf0, j),
        }));
        const clueList = outputs.map(() => clues.next());

        const { witnessInput, coeffs, z, y } =
            buildWitness(P, J, c, inputs, outputs, clueList, merkleRoot);

        // The circuit is the oracle, not the Horner loop below. Recording only the TS
        // value would make the file a TS-to-TS tautology.
        const w = await circuit.calculateWitness(witnessInput, true);
        await circuit.checkConstraints(w);
        const circuitY = readOutput(w);
        if (circuitY !== y) {
            throw new Error(
                `${c.name}: circuit y (${circuitY}) != reference PolyEval y (${y}). ` +
                    `The layout in src/test/ref/compress.ts disagrees with TransactCompressN.`,
            );
        }
        if (coeffs.length !== layout.length) {
            throw new Error(
                `${c.name}: ${coeffs.length} coefficients but the Lean layout names ${layout.length}`,
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
                    pk: s(derivePk(P, nsk)),
                })),
                assetGens: [{ assetId: s(c.asset), gen: pt(J.hashToAssetGen(c.asset)) }],
                inputs: inputs.map((n, i) => ({
                    slot: i,
                    isDummy: n.isDummy,
                    cm: s(n.cm),
                    nf: s(n.nf),
                    cv: pt(J.valueCommit(n.value, J.hashToAssetGen(n.asset), n.rcv)),
                    cvDep: pt(J.valueCommit(n.value, J.hashToAssetGen(n.asset), n.rcvDep)),
                    leafIndex: n.leafIndex,
                })),
                realLeaves: realMeta.map((m) => ({
                    slot: m.slot,
                    cm: s(m.cm),
                    cvDep: pt(m.cvDep),
                    leaf: s(m.leaf),
                    leafIndex: m.leafIndex,
                })),
                dummies: dummyMeta.map((d) => ({
                    slot: d.slot,
                    rho: s(d.rho),
                    rcv: s(d.rcv),
                    rcvDep: s(d.rcvDep),
                })),
                outputs: outputs.map((o, j) => ({
                    slot: j,
                    rho: s(o.rho),
                    cm: s(buildNoteCommitment(P, o)),
                    cv: pt(J.valueCommit(o.value, J.hashToAssetGen(o.asset), o.rcv)),
                    cvDep: pt(J.valueCommit(o.value, J.hashToAssetGen(o.asset), o.rcvDep)),
                })),
                merkle: {
                    depth: DEPTH,
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
            compression: compressionOf(coeffs, z, y),
            circuitOutput: { y: s(circuitY) },
        });
    }

    return {
        schema: SCHEMA,
        circuit: {
            id: "transact",
            template: `Transact(${DEPTH}, ${shape.nIn}, ${shape.nOut})`,
            source: shape.source,
            shape: { depth: DEPTH, nIn: shape.nIn, nOut: shape.nOut },
            coeffCount: 9 + 3 * shape.nIn + 8 * shape.nOut,
            layout,
            layoutDigest: layoutDigest(layout),
            // No in-circuit constraint binds these; PolyEval is their only tie.
            // The SDK derives out_aux_digest from its own abi-hash module, so
            // only the slot is contractual, not the value.
            unconstrained: ["out_clue_Rx", "out_clue_Ry", "out_clue_bits", "out_aux_digest"],
        },
        constants: sharedConstants(P, J),
        vectors,
    };
}
