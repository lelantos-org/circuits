// Golden test-vector generator — the cross-repo contract with @lelantos-org/sdk.
//
// This repo owns the circom, so it owns the layout. Rather than have the SDK
// import code from here (or, as before, this repo import code from the SDK),
// the two are held together by DATA: versioned vectors published in the npm
// package and checked by the SDK's own test suite.
//
// Two rules make these vectors a real contract rather than a self-fulfilling
// snapshot:
//
//   1. Every `y` is read out of a witness produced by the COMPILED CIRCUIT,
//      then compared against the TypeScript Horner evaluation. If they
//      disagree the generator refuses to write. Recording only the TS value
//      would make the file a TS-to-TS tautology that could not catch a
//      circuit change.
//   2. The slot-name layout is read from `lean/expected/layout-2x2.txt`, the
//      Lean model's own dump — not regenerated here. The vector file is what
//      physically carries Lean's ordering to the SDK.
//
// Determinism is mandatory (`just vectors-check` diffs a regeneration against
// the committed files): no randomness, no timestamps, no absolute paths.
//
//   just vectors        regenerate
//   just vectors-check  regenerate into a temp dir and diff

import { keccak_256 } from "@noble/hashes/sha3";
import { createHash } from "node:crypto";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import {
    Poseidon,
    Jubjub,
    MerkleTree,
    H_BASE,
    BN254_FR,
    TAGS,
    BABYJUB_SUBGROUP_ORDER,
    buildLeaf,
    buildNoteCommitment,
    buildNullifierFromNsk,
    buildRho,
    derivePk,
    deriveIvk,
    deriveNk,
    flatten,
    flattenBatch,
    hornerEval,
    fiatShamirZ,
    abiEncodeCoeffs,
    toCircomInput,
    dummyInputAt,
    deterministicClueGen,
    FMD_DEFAULT_GAMMA,
    type Field,
    type Point,
    type Note,
    type SpentNote,
} from "../src/test/ref/index.js";

// @ts-ignore — circom_tester ships without types
import { wasm as wasmTester } from "circom_tester";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.join(__dirname, "..");
const SRC = path.join(ROOT, "src");
const NODE_MODULES = path.join(ROOT, "node_modules");
const LEAN_EXPECTED = path.join(ROOT, "lean", "expected");

const SCHEMA = "lelantos.circuits.vectors/1";
const DEPTH = 10;
const MAX_L = 8;

const outDir = process.argv[2] ? path.resolve(process.argv[2]) : path.join(ROOT, "vectors");

const s = (x: Field | number | bigint): string => x.toString();
const pt = (p: Point) => ({ x: s(p[0]), y: s(p[1]) });
const hex = (b: Uint8Array) => "0x" + Buffer.from(b).toString("hex");

/** keccak256 over the newline-joined slot names — one line that moves when the layout does. */
function layoutDigest(layout: string[]): string {
    return hex(keccak_256(new TextEncoder().encode(layout.join("\n"))));
}

function readLeanLayout(shape: string): string[] {
    const p = path.join(LEAN_EXPECTED, `layout-${shape}.txt`);
    if (!fs.existsSync(p)) {
        throw new Error(
            `missing ${p} — run 'just lean-update' so the Lean model publishes its layout first`,
        );
    }
    return fs.readFileSync(p, "utf8").trim().split("\n");
}

async function loadCircuit(rel: string) {
    return wasmTester(path.join(SRC, rel), { include: [NODE_MODULES] });
}

/** Read output signal `y` (witness[1]; witness[0] is the constant 1). */
function witnessY(w: any[]): Field {
    return BigInt(w[1].toString());
}

// ===================== transact =====================

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

// Value conservation the circuit enforces, per asset:
//   sum(input values) + public_in == sum(output values) + public_out
const TRANSACT_SHAPES: TransactShape[] = [
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
        // Built and published (compile + ceremony recipes in the justfile, prover
        // artifacts in the npm package since 0.8.0), but with no on-chain wiring:
        // it needs a 42-slot `PubInputs.compress` overload. The vectors pin that
        // 42-slot layout — the same one the Lean development proves against — so
        // whoever wires it up inherits a byte-exact target instead of re-deriving it.
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
];

async function buildTransactVectors(shape: TransactShape) {
    const layout = readLeanLayout(shape.id);
    const [P, J] = await Promise.all([Poseidon.build(), Jubjub.build()]);
    const circuit = await loadCircuit(path.basename(shape.source));

    const vectors = [];

    for (const c of shape.cases) {
        if (c.inputs.length !== shape.nIn || c.outputs.length !== shape.nOut) {
            throw new Error(
                `${shape.id}/${c.name}: case has ${c.inputs.length}x${c.outputs.length}, ` +
                    `shape is ${shape.nIn}x${shape.nOut}`,
            );
        }
        // Conservation is what the circuit enforces; a mis-specified case would
        // otherwise surface as an opaque constraint failure inside circom.
        const inSum = c.inputs.reduce((a, i) => a + (i?.value ?? 0n), 0n);
        const outSum = c.outputs.reduce((a, o) => a + o.value, 0n);
        if (inSum + c.publicIn !== outSum + c.publicOut) {
            throw new Error(
                `${shape.id}/${c.name}: unbalanced — in ${inSum} + publicIn ${c.publicIn} != ` +
                    `out ${outSum} + publicOut ${c.publicOut}`,
            );
        }

        const clues = deterministicClueGen(P, J);
        const tree = new MerkleTree(P, DEPTH);

        const note = (nsk: bigint, value: bigint, rho: bigint): Note => ({
            asset: c.asset,
            value,
            pk: derivePk(P, nsk),
            rho,
            rcm: rho + 1n,
            rcv: rho + 2n,
            rcvDep: rho + 3n,
        });

        // Insert the real inputs, recording the leaf preimage for `intermediates`.
        const realMeta: any[] = [];
        const spent: SpentNote[] = [];
        c.inputs.forEach((inp, i) => {
            if (!inp) return;
            const n = note(inp.nsk, inp.value, BigInt(1000 * (i + 1)));
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

        const merkleRoot = tree.root();
        const finalizedReal = spent.map((sn) => ({ ...sn, ...tree.proof(sn.leafIndex) }));

        // Reassemble in slot order, filling dummies where the case asked for one.
        let realCursor = 0;
        const dummyMeta: any[] = [];
        const inputs: SpentNote[] = c.inputs.map((inp, i) => {
            if (inp) return finalizedReal[realCursor++];
            const rho = BigInt(90000 + i);
            // Blinders default to a deterministic derivation from rho; read them
            // back off the result rather than recomputing them here.
            const dummy = dummyInputAt(P, DEPTH, rho);
            dummyMeta.push({ slot: i, rho, rcv: dummy.rcv, rcvDep: dummy.rcvDep });
            return dummy;
        });

        // Output rho is forced to the Orchard-style derivation the circuit enforces.
        // Only `rho` is replaced: the blinders stay derived from the small base
        // value, because `rcm`/`rcv`/`rcvDep` are `rho + k` and a derived rho is a
        // full-width Poseidon output — `rcv` would land above the Num2Bits(253)
        // width MulH enforces. Matches TxBuilder.build in src/test/lib/transact.ts.
        const nf0 = inputs[0].nf;
        const outputs: Note[] = c.outputs.map((o, j) => ({
            ...note(o.nsk, o.value, BigInt(3000 * (j + 1))),
            rho: buildRho(P, nf0, j),
        }));
        const clueList = outputs.map(() => clues.next());
        const outputAuxDigest = 0xa17d19e57n;

        // Two-pass Fiat-Shamir: build at z=0, flatten, hash, rebuild at the real z.
        const base = toCircomInput(P, J, {
            publicAssetId: c.asset,
            publicIn: c.publicIn,
            publicOut: c.publicOut,
            inputs,
            outputs,
            outputClues: clueList,
            merkleRoot,
            outputAuxDigest,
            z: 0n,
        });
        const coeffs = flatten(base);
        const z = fiatShamirZ(coeffs);
        const witnessInput = { ...base, z: z.toString() };
        const y = hornerEval(coeffs, z);

        // The circuit is the oracle, not our Horner loop.
        const w = await circuit.calculateWitness(witnessInput, true);
        await circuit.checkConstraints(w);
        const circuitY = witnessY(w);
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

        vectors.push({
            name: c.name,
            description: c.description,
            expect: "accept",
            intermediates: {
                keys: [...new Set(c.inputs.filter(Boolean).map((i) => i!.nsk).concat(c.outputs.map((o) => o.nsk)))]
                    .sort((a, b) => (a < b ? -1 : 1))
                    .map((nsk) => ({
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
                    perOutput: clueList.map((c2, j) => ({
                        slot: j,
                        r: s(c2.r),
                        cluePackedR: hex(c2.clue.R),
                        clueBitsPacked: hex(c2.clue.bits),
                        clueRx: s(c2.clueRx),
                        clueRy: s(c2.clueRy),
                        clueBits: s(c2.clueBits),
                    })),
                },
            },
            witness: witnessInput,
            compression: {
                coeffs: coeffs.map(s),
                abiEncodedCoeffs: hex(abiEncodeCoeffs(coeffs)),
                zDerivation: "fiat-shamir",
                z: s(z),
                y: s(y),
            },
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
            // The SDK derives out_aux_digest from its own abi-hash module, so a
            // value comparison there would be meaningless — only the SLOT is contractual.
            unconstrained: ["out_clue_Rx", "out_clue_Ry", "out_clue_bits", "out_aux_digest"],
        },
        constants: sharedConstants(P, J),
        vectors,
    };
}

// ===================== tree_update_batch =====================

/** Slot names for BatchCompress(MAX_L), in src/lib/poly_eval.circom order. */
function batchLayout(maxL: number): string[] {
    const names = ["oldRoot", "newRoot", "startIndex", "actualCount"];
    for (let k = 0; k < maxL; k++) names.push(`cms ${k}`);
    for (let k = 0; k < maxL; k++) {
        names.push(`cvDepX ${k}`);
        names.push(`cvDepY ${k}`);
    }
    for (let k = 0; k < maxL; k++) names.push(`leafAsset ${k}`);
    for (let k = 0; k < maxL; k++) names.push(`leafPublicIn ${k}`);
    for (let k = 0; k < maxL; k++) names.push(`isDeposit ${k}`);
    return names;
}

interface BatchLeafSpec {
    asset: bigint;
    value: bigint;
    isDeposit: 0 | 1;
}

interface BatchCase {
    name: string;
    description: string;
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

async function buildBatchVectors() {
    const [P, J] = await Promise.all([Poseidon.build(), Jubjub.build()]);
    const circuit = await loadCircuit("tree_update_batch.circom");
    const layout = batchLayout(MAX_L);

    const pad = <T,>(real: T[], zero: T): T[] => {
        const out = real.slice();
        while (out.length < MAX_L) out.push(zero);
        return out;
    };

    const vectors = [];

    for (const c of BATCH_CASES) {
        const tree = new MerkleTree(P, DEPTH);
        for (let i = 0; i < c.prefilled; i++) tree.insert(BigInt(0xdead + i));
        const oldRoot = tree.root();
        const frontier = tree.frontier();

        const built = c.leaves.map((l, k) => {
            const rho = BigInt(k + 1);
            const rcvDep = BigInt(5 * (k + 1));
            const cm = P.hash([l.asset * (1n << 64n) + l.value, 0xabcn, rho, 3n]);
            const cvDep = J.valueCommit(l.value, J.hashToAssetGen(l.asset), rcvDep);
            const leaf = buildLeaf(P, cm, cvDep);
            return {
                cm,
                cvDep,
                leaf,
                leafAsset: l.isDeposit === 1 ? l.asset : 0n,
                leafPublicIn: l.isDeposit === 1 ? l.value : 0n,
                isDeposit: l.isDeposit,
                rcv: rcvDep,
            };
        });

        for (const b of built) tree.insert(b.leaf);
        const newRoot = tree.root();

        const cms = pad(built.map((b) => b.cm), 0n);
        const cvDep = pad(built.map((b) => b.cvDep), [0n, 0n] as Point);
        const leafAsset = pad(built.map((b) => b.leafAsset), 0n);
        const leafPublicIn = pad(built.map((b) => b.leafPublicIn), 0n);
        const isDeposit = pad(built.map((b) => b.isDeposit as number), 0);
        const rcv = pad(built.map((b) => b.rcv), 0n);

        const coeffs = flattenBatch({
            old_root: oldRoot,
            new_root: newRoot,
            start_index: c.prefilled,
            actual_count: built.length,
            cms,
            cv_dep: cvDep,
            leaf_asset: leafAsset,
            leaf_public_in: leafPublicIn,
            is_deposit: isDeposit,
        });
        const z = fiatShamirZ(coeffs);
        const y = hornerEval(coeffs, z);

        const witnessInput = {
            z: s(z),
            old_root: s(oldRoot),
            new_root: s(newRoot),
            start_index: s(c.prefilled),
            actual_count: s(built.length),
            cms: cms.map(s),
            cv_dep: cvDep.map((p) => [s(p[0]), s(p[1])]),
            leaf_asset: leafAsset.map(s),
            leaf_public_in: leafPublicIn.map(s),
            is_deposit: isDeposit.map(s),
            frontier_in: frontier.map((lvl) => lvl.map(s)),
            rcv: rcv.map(s),
        };

        const w = await circuit.calculateWitness(witnessInput, true);
        await circuit.checkConstraints(w);
        const circuitY = witnessY(w);
        if (circuitY !== y) {
            throw new Error(
                `${c.name}: circuit y (${circuitY}) != reference PolyEval y (${y}). ` +
                    `The layout in src/test/ref/compress.ts disagrees with BatchCompress.`,
            );
        }

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
            compression: {
                coeffs: coeffs.map(s),
                abiEncodedCoeffs: hex(abiEncodeCoeffs(coeffs)),
                zDerivation: "fiat-shamir",
                z: s(z),
                y: s(y),
            },
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

// ===================== shared =====================

function sharedConstants(P: Poseidon, J: Jubjub) {
    const tree = new MerkleTree(P, DEPTH);
    return {
        bn254Fr: s(BN254_FR),
        babyjubSubgroupOrder: s(BABYJUB_SUBGROUP_ORDER),
        babyjubBase8: pt(J.base8),
        hBase: pt(H_BASE),
        tags: Object.fromEntries(Object.entries(TAGS).map(([k, v]) => [k, s(v)])),
        // depth+1 entries; also hardcoded as EMPTY_SUBTREE in src/lib/common.circom
        // and as CommitmentTree.EMPTY_ROOT (last entry) in the contracts repo.
        emptySubtree: tree.emptySubtree().map(s),
    };
}

/** Stable stringify: 2-space indent, arrays of scalars one element per line. */
function writeJson(file: string, value: unknown): string {
    const text = JSON.stringify(value, null, 2) + "\n";
    fs.writeFileSync(file, text);
    return createHash("sha256").update(text).digest("hex");
}

async function main() {
    fs.mkdirSync(outDir, { recursive: true });

    const files: Record<string, unknown> = {};
    for (const shape of TRANSACT_SHAPES) {
        files[`transact-${shape.id}.json`] = await buildTransactVectors(shape);
    }
    files[`tree-update-batch-${MAX_L}.json`] = await buildBatchVectors();

    const index: Record<string, { sha256: string; coeffCount: number; layoutDigest: string }> = {};
    for (const [name, value] of Object.entries(files)) {
        const sha256 = writeJson(path.join(outDir, name), value);
        const v = value as any;
        index[name] = {
            sha256,
            coeffCount: v.circuit.coeffCount,
            layoutDigest: v.circuit.layoutDigest,
        };
    }

    // The generator version lives here and NOT in the per-file bodies, so a
    // patch bump does not invalidate every file digest.
    const pkg = JSON.parse(fs.readFileSync(path.join(ROOT, "package.json"), "utf8"));
    writeJson(path.join(outDir, "index.json"), {
        schema: SCHEMA,
        generator: `@lelantos-org/circuits@${pkg.version}`,
        files: index,
    });

    for (const [name, meta] of Object.entries(index)) {
        console.log(`${name}: ${meta.coeffCount} coeffs, layoutDigest ${meta.layoutDigest}`);
    }
    console.log(`wrote ${Object.keys(files).length + 1} files to ${path.relative(ROOT, outDir)}/`);
}

main().catch((e) => {
    console.error(e);
    process.exit(1);
});
