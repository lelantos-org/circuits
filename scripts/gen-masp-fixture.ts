// MASP-level proof fixture for the contracts repo: one small history the pool
// can replay, with a proof for each step.
//
//   flush      one deposit (principal + zero-value fee note) flushed from the
//              empty tree, with a `tree_update_batch` proof
//   transfer   a spend of that deposit's note, with a `4x6` proof and the
//              `tree_update_batch` proof of the six leaves it inserts
//   withdraw   an alternative spend of the same note from the same tree state,
//              with a non-zero public output
//
// The witnesses are deterministic. Groth16 proving is not, so a rerun writes
// different proofs over the same public signals.
//
// Before writing, every proof is verified against the verification key and its
// public signals are compared with the `[y, digest, z]` computed here the way
// `PubInputs.sol` computes them, and each verification key is compared with the
// Solidity verifier the contracts vendor.
//
//   just masp-fixture                     default keys, sibling ../contracts
//   node scripts/gen-masp-fixture.ts --keys <dir> [--wasm <dir>]
//        [--contracts <dir>] [--out <file>]

import * as fs from "node:fs";
import * as path from "node:path";
import { keccak_256 } from "@noble/hashes/sha3";
// snarkjs ships without TS types
// @ts-ignore
import * as snarkjs from "snarkjs";

import {
    BN254_FR,
    Jubjub,
    MerkleTree,
    Poseidon,
    batchCoeffs,
    batchDigest,
    buildInner,
    buildNullifierFromNsk,
    circuitSignals,
    coeffs,
    commitWithInner,
    derivePk,
    fiatShamirZ,
    flattenBatch,
    hornerEval,
    toBeBytes32,
    type Field,
    type Note,
    type SpentNote,
    type TransactWitnessBundle,
} from "../test/ref/index.js";
import { ALICE_NSK, BOB_NSK, DEPTH, MAX_L, N_OUT } from "../test/lib/constants.js";
import { padToSlots, treeUpdateBatchInputJson } from "../test/lib/inputs.js";
import { TxBuilder, bindFiatShamir } from "../test/lib/transact.js";
import { ROOT } from "./vectors/common.js";

// ===== the request the pool is asked to accept =====
//
// Mirrored by the contracts' tests: `TestConstants.sol` for the asset id and
// the addresses, `foundry.toml` for the chain id.

const CHAIN_ID = 31337n;
/** `TestConstants.ASSET_ID`. */
const ASSET = 1n;
/** `TestConstants.RECIPIENT`. */
const RECIPIENT = 0xf00dn;
/** `TestConstants.ESCROW_PAYER`. */
const PAYER = 0xfacen;
/** `TestConstants.RELAYER`: `msg.sender` of the spend. */
const RELAYER = 0xca11n;

const DEPOSIT_VALUE = 100n;
const TRANSFER_TO_BOB = 60n;
const WITHDRAW_OUT = 30n;

/** Domain for the fixture's note randomness and stand-in payload bytes. */
const DOMAIN = 0x6d6173702d666978n; // "masp-fix"

// ===== arguments =====

function arg(name: string, fallback: string): string {
    const i = process.argv.indexOf(`--${name}`);
    if (i < 0) return fallback;
    const v = process.argv[i + 1];
    if (v === undefined) throw new Error(`--${name} needs a value`);
    return path.resolve(v);
}

const KEYS = arg("keys", path.join(ROOT, "build", "prototype-0.17.0"));
const WASM = arg("wasm", "");
const CONTRACTS = arg("contracts", path.join(ROOT, "..", "contracts"));
const OUT = arg("out", path.join(CONTRACTS, "test", "fixtures", "masp_flow_proof.json"));

interface Artifacts {
    wasm: string;
    zkey: string;
    vkey: { vk_delta_2: string[][]; IC: string[][] };
    /** The vendored codegen verifier this key must match. */
    verifierSol: string;
}

/**
 * A release ships the wasm beside the zkey; a local compile writes it to
 * `build/<name>_js/`. `build/<name>.wasm` is not used: it is staged only by
 * `just package-check` and may predate the r1cs the keys were made for.
 */
function artifacts(name: string, verifierSol: string): Artifacts {
    const wasm = [
        ...(WASM ? [path.join(WASM, `${name}.wasm`)] : []),
        path.join(KEYS, `${name}.wasm`),
        path.join(ROOT, "build", `${name}_js`, `${name}.wasm`),
    ].find((p) => fs.existsSync(p));
    const zkey = path.join(KEYS, `${name}_final.zkey`);
    const vkeyPath = path.join(KEYS, `${name}_verification_key.json`);
    const sol = path.join(CONTRACTS, "src", "verifiers", verifierSol);
    for (const f of [wasm, zkey, vkeyPath, sol]) {
        if (!f || !fs.existsSync(f)) throw new Error(`missing artifact for ${name}: ${f ?? "wasm"}`);
    }
    return { wasm: wasm!, zkey, vkey: JSON.parse(fs.readFileSync(vkeyPath, "utf8")), verifierSol: sol };
}

/**
 * The verification key must be the one the Solidity verifier encodes, or the
 * proofs written here verify off-chain and are rejected by the pool.
 */
function assertVkeyMatchesVerifier(a: Artifacts): void {
    const sol = fs.readFileSync(a.verifierSol, "utf8");
    const consts = new Map<string, bigint>();
    for (const m of sol.matchAll(/uint256\s+constant\s+(\w+)\s*=\s*(\d+);/g)) consts.set(m[1], BigInt(m[2]));

    // snarkjs codegen ordering: G2 coordinates are emitted (x1, x0), (y1, y0).
    const d = a.vkey.vk_delta_2;
    const expect: [string, string][] = [
        ["deltax1", d[0][1]],
        ["deltax2", d[0][0]],
        ["deltay1", d[1][1]],
        ["deltay2", d[1][0]],
    ];
    a.vkey.IC.forEach((ic, i) => expect.push([`IC${i}x`, ic[0]], [`IC${i}y`, ic[1]]));
    for (const [k, v] of expect) {
        if (consts.get(k) !== BigInt(v)) {
            throw new Error(`${a.verifierSol}: ${k} is ${consts.get(k)}, verification key says ${v}`);
        }
    }
}

// ===== encoding =====

const word = (x: Field | number): string => "0x" + BigInt(x).toString(16).padStart(64, "0");
const address = (x: Field): string => "0x" + x.toString(16).padStart(40, "0");
const bytesHex = (b: Uint8Array): string => "0x" + Buffer.from(b).toString("hex");

function concat(parts: Uint8Array[]): Uint8Array {
    const out = new Uint8Array(parts.reduce((n, p) => n + p.length, 0));
    let at = 0;
    for (const p of parts) {
        out.set(p, at);
        at += p.length;
    }
    return out;
}

/** One output's `AuxValidation.Output`. */
interface Aux {
    clueRx: Field;
    clueRy: Field;
    ephPubX: Field;
    ephPubY: Field;
    ciphertext: Uint8Array;
}

/**
 * `PubInputs.auxDigest`: `keccak256(abi.encode(Output[])) mod r`, the payloads
 * encoded as a dynamic array of `(uint256, uint256, uint256, uint256, bytes)`.
 *
 * The contract recomputes this word from calldata and hashes it into the
 * transact challenge, so the encoding must match.
 */
function auxDigest(aux: Aux[]): Field {
    const tuples = aux.map((o) => {
        const padded = new Uint8Array(Math.ceil(o.ciphertext.length / 32) * 32);
        padded.set(o.ciphertext);
        return concat([
            toBeBytes32(o.clueRx),
            toBeBytes32(o.clueRy),
            toBeBytes32(o.ephPubX),
            toBeBytes32(o.ephPubY),
            // Offset of the `bytes` tail from the start of the tuple.
            toBeBytes32(0xa0n),
            toBeBytes32(BigInt(o.ciphertext.length)),
            padded,
        ]);
    });
    // Element offsets count from the first offset word.
    const offsets: Uint8Array[] = [];
    let at = 32 * aux.length;
    for (const t of tuples) {
        offsets.push(toBeBytes32(BigInt(at)));
        at += t.length;
    }
    const enc = concat([toBeBytes32(0x20n), toBeBytes32(BigInt(aux.length)), ...offsets, ...tuples]);
    let v = 0n;
    for (const b of keccak_256(enc)) v = (v << 8n) | BigInt(b);
    return v % BN254_FR;
}

// ===== proving =====

interface Proven {
    /** `a`, `b`, `c` as the pairing precompile takes them. */
    proof: { a: string[]; b: string[][]; c: string[] };
    pubSignals: string[];
}

/**
 * Prove `input`, then require that the proof verifies and that its public
 * signals are the `[y, digest, z]` the contract will compute from calldata.
 */
async function prove(
    what: string,
    a: Artifacts,
    input: Record<string, unknown>,
    expected: [Field, Field, Field],
): Promise<Proven> {
    const { proof, publicSignals } = await snarkjs.groth16.fullProve(input, a.wasm, a.zkey);
    if (!(await snarkjs.groth16.verify(a.vkey, publicSignals, proof))) {
        throw new Error(`${what}: proof does not verify against ${a.zkey}'s verification key`);
    }
    ["y", "digest", "z"].forEach((name, i) => {
        if (BigInt(publicSignals[i]) !== expected[i]) {
            throw new Error(`${what}: public signal ${name} is ${publicSignals[i]}, expected ${expected[i]}`);
        }
    });
    // G2 coordinates in the (x1, x0), (y1, y0) order the precompile expects:
    // taken from the calldata export, not from `proof`, which stores them the
    // other way round.
    const words: string[] = (await snarkjs.groth16.exportSolidityCallData(proof, publicSignals)).match(
        /0x[0-9a-fA-F]{64}/g,
    );
    if (words.length !== 11) throw new Error(`${what}: expected 11 calldata words, got ${words.length}`);
    console.log(`${what}: proof verifies, public signals match`);
    return {
        proof: { a: words.slice(0, 2), b: [words.slice(2, 4), words.slice(4, 6)], c: words.slice(6, 8) },
        pubSignals: words.slice(8, 11),
    };
}

/** One `tree_update_batch` step: the calldata struct and its proof. */
async function proveBatch(
    what: string,
    a: Artifacts,
    tree: MerkleTree,
    slots: { word: Field; leaf: Field; asset: Field; publicIn: Field; isDeposit: 0 | 1 }[],
) {
    const startIndex = tree.leaves.length;
    const oldRoot = tree.root();
    const frontier = tree.frontier();
    for (const s of slots) tree.insert(s.leaf);

    const pub = {
        oldRoot,
        newRoot: tree.root(),
        startIndex,
        actualCount: slots.length,
        cms: padToSlots(slots.map((s) => s.word), MAX_L, 0n),
        leafAsset: padToSlots(slots.map((s) => s.asset), MAX_L, 0n),
        leafPublicIn: padToSlots(slots.map((s) => s.publicIn), MAX_L, 0n),
        isDeposit: padToSlots(slots.map((s) => s.isDeposit as number), MAX_L, 0),
    };
    const coeffSlots = {
        old_root: pub.oldRoot,
        new_root: pub.newRoot,
        start_index: pub.startIndex,
        actual_count: pub.actualCount,
        cms: pub.cms,
        leaf_asset: pub.leafAsset,
        leaf_public_in: pub.leafPublicIn,
        is_deposit: pub.isDeposit,
    };
    const digest = batchDigest(coeffSlots);
    const z = fiatShamirZ(flattenBatch({ ...coeffSlots, digest }));
    const y = hornerEval(batchCoeffs(coeffSlots), z);

    const proven = await prove(what, a, treeUpdateBatchInputJson({ ...pub, frontier, digest, z }), [y, digest, z]);
    return { ...pub, digest, ...proven };
}

async function main() {
    const transact = artifacts("4x6", "Verifier.sol");
    const batch = artifacts("tree_update_batch", "TreeUpdateBatchVerifier.sol");
    assertVkeyMatchesVerifier(transact);
    assertVkeyMatchesVerifier(batch);

    const [P, J] = await Promise.all([Poseidon.build(), Jubjub.build()]);
    const tx = new TxBuilder(P, J, DEPTH);
    const rand = (i: number): Field => P.hash([DOMAIN, BigInt(i)]);

    // ----- the deposit: Alice's note and the relayer's zero-value fee note -----
    //
    // A deposit publishes `inner` beside its public amount and the batch
    // circuit builds the leaf from the three, so the leaf is the commitment of
    // the note Alice later opens. A zero-value fee note must name asset 0.
    const principal: Note = {
        asset: ASSET,
        value: DEPOSIT_VALUE,
        pk: derivePk(P, ALICE_NSK),
        rho: rand(0),
        rcm: rand(1),
    };
    const feeNote: Note = { asset: 0n, value: 0n, pk: derivePk(P, BOB_NSK), rho: rand(2), rcm: rand(3) };
    const inner = buildInner(P, principal);
    const feeInner = buildInner(P, feeNote);
    const leaf = commitWithInner(P, principal.asset, principal.value, inner);
    const feeLeaf = commitWithInner(P, feeNote.asset, feeNote.value, feeInner);

    const depositSlots = [
        { word: inner, leaf, asset: principal.asset, publicIn: principal.value, isDeposit: 1 as const },
        { word: feeInner, leaf: feeLeaf, asset: feeNote.asset, publicIn: feeNote.value, isDeposit: 1 as const },
    ];

    // ----- (a) flushBatch: the two deposit leaves, from the empty tree -----
    const flush = await proveBatch("flush", batch, new MerkleTree(P, DEPTH), depositSlots);

    /** The tree the flush leaves, rebuilt per spend: each extends it separately. */
    const flushedTree = (): MerkleTree => {
        const tree = new MerkleTree(P, DEPTH);
        for (const s of depositSlots) tree.insert(s.leaf);
        if (tree.root() !== flush.newRoot) throw new Error("flushed tree does not reproduce the flush's new root");
        return tree;
    };

    /**
     * A spend of the deposit's note against the flushed tree: its transact
     * proof and the tree-update proof of the leaves it inserts.
     */
    async function spend(what: string, outputs: Note[], publicOut: bigint) {
        const tree = flushedTree();
        const input: SpentNote = {
            ...principal,
            nsk: ALICE_NSK,
            cm: leaf,
            nf: buildNullifierFromNsk(P, ALICE_NSK, principal.rho, leaf),
            leafIndex: 0,
            ...tree.proof(0),
            isDummy: false,
        };
        // Pads to four inputs and six outputs, derives the output rhos from
        // `nullifier[0]`, and draws one FMD clue per output.
        const w: TransactWitnessBundle = tx.spend(
            { root: tree.root(), inputs: [input] },
            outputs,
            publicOut === 0n ? {} : { publicOut, publicAssetId: ASSET },
        );

        // The encrypted-note payloads. The clue is the witness's own; the
        // ephemeral key is a subgroup point; the body is stand-in bytes, since
        // nothing on chain decrypts it. `PubInputs.compress` reads the clue
        // bits back out of the ciphertext's two-byte big-endian prefix.
        const aux: Aux[] = Array.from({ length: N_OUT }, (_, j) => {
            const [ephPubX, ephPubY] = J.mulPointEscalar(J.base8, rand(100 + j) % J.order);
            const bits = Number(w.out_clue_bits[j]);
            if (bits >> 14 !== 0) throw new Error("clue bits exceed the 14-bit prefix");
            const body = concat([toBeBytes32(rand(200 + j)), toBeBytes32(rand(300 + j))]);
            return {
                clueRx: BigInt(w.out_clue_Rx[j]),
                clueRy: BigInt(w.out_clue_Ry[j]),
                ephPubX,
                ephPubY,
                ciphertext: concat([Uint8Array.of(bits >> 8, bits & 0xff), body]),
            };
        });

        // The words the circuit has no signal for. They reach the proof through
        // `z` only, so they are set on the calldata view and the challenge is
        // rebound; the coefficients, and so the digest, are unchanged.
        w.recipient_address = RECIPIENT.toString();
        w.chain_id = CHAIN_ID.toString();
        w.payer_address = PAYER.toString();
        w.relayer_address = RELAYER.toString();
        w.intent_hash = "0";
        w.out_aux_digest = auxDigest(aux).toString();
        bindFiatShamir(w, w);

        const z = BigInt(w.z);
        const digest = BigInt(w.digest);
        const txProven = await prove(`${what} (4x6)`, transact, circuitSignals(w), [
            hornerEval(coeffs(w), z),
            digest,
            z,
        ]);

        // The batch `PubInputs.compressSpend` rebuilds: the spend's own `out_cm`
        // as spend leaves at the live root.
        const tub = await proveBatch(
            `${what} (tree_update_batch)`,
            batch,
            tree,
            w.out_cm.map((cm) => ({ word: BigInt(cm), leaf: BigInt(cm), asset: 0n, publicIn: 0n, isDeposit: 0 as const })),
        );

        return {
            pi: {
                merkleRoot: word(BigInt(w.merkle_root)),
                nullifier: w.nullifier.map((n) => word(BigInt(n))),
                outCm: w.out_cm.map((c) => word(BigInt(c))),
                publicAssetId: w.public_asset_id,
                publicOut: w.public_out,
                digest: word(digest),
                recipient: address(RECIPIENT),
                chainId: w.chain_id,
                payer: address(PAYER),
                relayer: address(RELAYER),
                intentHash: word(0n),
            },
            aux: aux.map((o) => ({
                clueRx: word(o.clueRx),
                clueRy: word(o.clueRy),
                ephPubX: word(o.ephPubX),
                ephPubY: word(o.ephPubY),
                ciphertext: bytesHex(o.ciphertext),
            })),
            tpi: { newRoot: word(tub.newRoot), startIndex: tub.startIndex.toString(), digest: word(tub.digest) },
            txProof: txProven.proof,
            txPubSignals: txProven.pubSignals,
            tubProof: tub.proof,
            tubPubSignals: tub.pubSignals,
        };
    }

    const owned = (value: bigint, nsk: Field, i: number): Note => ({
        asset: ASSET,
        value,
        pk: derivePk(P, nsk),
        // Overridden by the builder with the derivation the circuit enforces.
        rho: 0n,
        rcm: rand(i),
    });

    // ----- (b) transfer: 60 to Bob, 40 back to Alice, nothing public -----
    const transfer = await spend(
        "transfer",
        [owned(TRANSFER_TO_BOB, BOB_NSK, 10), owned(DEPOSIT_VALUE - TRANSFER_TO_BOB, ALICE_NSK, 11)],
        0n,
    );

    // ----- (c) withdraw: 30 out to the recipient, 70 back to Alice -----
    const withdraw = await spend("withdraw", [owned(DEPOSIT_VALUE - WITHDRAW_OUT, ALICE_NSK, 20)], WITHDRAW_OUT);

    const pkg = JSON.parse(fs.readFileSync(path.join(ROOT, "package.json"), "utf8"));
    const fixture = {
        schema: "lelantos.contracts.masp-fixture/1",
        source: {
            generator: `@lelantos-org/circuits@${pkg.version} scripts/gen-masp-fixture.ts`,
            keys: path.basename(KEYS),
            transact: `Transact(${DEPTH}, 4, ${N_OUT})`,
            treeUpdateBatch: `TreeUpdateBatch(${DEPTH}, ${MAX_L})`,
        },
        chainId: CHAIN_ID.toString(),
        // The opening of the deposited note: what `flush.tpi.cms[0]` hides and
        // both spends open.
        note: {
            nsk: ALICE_NSK.toString(),
            asset: principal.asset.toString(),
            value: principal.value.toString(),
            pk: word(principal.pk),
            rho: word(principal.rho),
            rcm: word(principal.rcm),
            cm: word(leaf),
            leafIndex: 0,
        },
        flush: {
            tpi: {
                oldRoot: word(flush.oldRoot),
                newRoot: word(flush.newRoot),
                startIndex: flush.startIndex.toString(),
                actualCount: flush.actualCount.toString(),
                cms: flush.cms.map(word),
                leafAsset: flush.leafAsset.map(String),
                leafPublicIn: flush.leafPublicIn.map(String),
                isDeposit: flush.isDeposit.map(String),
                digest: word(flush.digest),
            },
            proof: flush.proof,
            pubSignals: flush.pubSignals,
        },
        transfer,
        withdraw,
    };

    fs.writeFileSync(OUT, JSON.stringify(fixture, null, 2) + "\n");
    console.log(`wrote ${OUT}`);
}

// snarkjs keeps its worker pool alive, so exit explicitly on both paths.
main().then(
    () => process.exit(0),
    (e) => {
        console.error(e);
        process.exit(1);
    },
);
