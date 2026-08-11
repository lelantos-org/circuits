// Transact circuit witness construction.
//
// Values are emitted as decimal strings. circom resolves signals positionally,
// so the key set is part of the interface: an extra key is as significant as a
// missing one.

import type { Field, Point } from "./field.js";
import type { Jubjub } from "./jubjub.js";
import type { Poseidon } from "./poseidon.js";
import { buildNoteCommitment, buildNullifierFromNsk, type Note, type SpentNote } from "./note.js";

/** Per-output FMD clue witness. */
export interface ClueInputs {
    clueBits: Field;
    clueRx: Field;
    clueRy: Field;
}

/** Public-input slots, in PubInputs.compress(Transact) order. */
export interface CircomPublicInputs {
    merkle_root: string;
    nullifier: string[];
    out_cm: string[];
    public_asset_id: string;
    public_in: string;
    public_out: string;
    in_cv: string[][];
    out_cv: string[][];
    recipient_address: string;
    chain_id: string;
    payer_address: string;
    relayer_address: string;
    /** Per-output value commitment anchoring (asset, value) into the Merkle leaf. */
    out_cv_dep: string[][];
    out_clue_Rx: string[];
    out_clue_Ry: string[];
    out_clue_bits: string[];
    /** Digest over the encrypted-note payloads; final slot. */
    out_aux_digest: string;
}

/** Full witness: the public slots above plus the private ones. */
export interface CircomTransactInput extends CircomPublicInputs {
    /** Fiat-Shamir challenge over the logical PIs. */
    z: string;

    in_asset: string[];
    in_value: string[];
    in_pk: string[];
    in_rho: string[];
    in_rcm: string[];
    in_nsk: string[];
    in_rcv: string[];
    in_rcv_dep: string[];
    in_path_elements: string[][][];
    in_path_indices: string[][];
    in_is_dummy: string[];

    out_asset: string[];
    out_value: string[];
    out_pk: string[];
    out_rho: string[];
    out_rcm: string[];
    out_rcv: string[];
    out_rcv_dep: string[];
}

export interface BuildOpts {
    publicAssetId: Field;
    publicIn: Field;
    publicOut: Field;
    inputs: SpentNote[];
    outputs: Note[];
    outputClues: ClueInputs[];
    merkleRoot: Field;
    recipientAddress?: Field;
    chainId?: Field;
    /** Pulled by `transferFrom` on deposit; bound in-SNARK so a relayer cannot redirect sources. */
    payerAddress?: Field;
    /** Must equal `msg.sender` of the on-chain `transact` call; blocks relayer front-running. */
    relayerAddress?: Field;
    /** Fiat-Shamir challenge. Tests default to 1n; production derives it from a transcript. */
    z?: Field;
    /**
     * `auxDigest(aux)` over the outputs' encrypted-note payloads. Required, not
     * defaulted: the contract always recomputes this slot from calldata, so a
     * silent 0 would build a witness the verifier rejects.
     */
    outputAuxDigest: Field;
}

/**
 * Build the circom input object for Transact(DEPTH, N_IN, N_OUT).
 *
 * Arity is taken from the argument lengths rather than hardcoded, so this
 * serves 2x2 and 3x3 alike.
 */
export function toCircomInput(P: Poseidon, J: Jubjub, opts: BuildOpts): CircomTransactInput {
    const { inputs, outputs, publicAssetId, publicIn, publicOut, merkleRoot } = opts;

    if (inputs.length === 0) throw new Error("toCircomInput: need at least one input");
    if (outputs.length === 0) throw new Error("toCircomInput: need at least one output");
    if (opts.outputClues.length !== outputs.length) {
        throw new Error("toCircomInput: outputClues length must equal outputs length");
    }

    const recipientAddress = opts.recipientAddress ?? 0n;
    const chainId = opts.chainId ?? 0n;
    const payerAddress = opts.payerAddress ?? 0n;
    const relayerAddress = opts.relayerAddress ?? 0n;

    const outCm = outputs.map((o) => buildNoteCommitment(P, o));
    const inCv: Point[] = inputs.map((i) =>
        J.valueCommit(i.value, J.hashToAssetGen(i.asset), i.rcv),
    );
    const outCv: Point[] = outputs.map((o) =>
        J.valueCommit(o.value, J.hashToAssetGen(o.asset), o.rcv),
    );
    // cv_dep anchors (asset, value, rcv_dep) into the Merkle leaf:
    //   leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y)
    const outCvDep: Point[] = outputs.map((o) =>
        J.valueCommit(o.value, J.hashToAssetGen(o.asset), o.rcvDep),
    );

    const z = opts.z ?? 1n;

    return {
        z: z.toString(),
        merkle_root: merkleRoot.toString(),
        nullifier: inputs.map((i) => i.nf.toString()),
        out_cm: outCm.map((c) => c.toString()),
        public_asset_id: publicAssetId.toString(),
        public_in: publicIn.toString(),
        public_out: publicOut.toString(),
        in_cv: inCv.map((p) => [p[0].toString(), p[1].toString()]),
        out_cv: outCv.map((p) => [p[0].toString(), p[1].toString()]),
        recipient_address: recipientAddress.toString(),
        chain_id: chainId.toString(),
        payer_address: payerAddress.toString(),
        relayer_address: relayerAddress.toString(),
        out_cv_dep: outCvDep.map((p) => [p[0].toString(), p[1].toString()]),

        in_asset: inputs.map((i) => i.asset.toString()),
        in_value: inputs.map((i) => i.value.toString()),
        in_pk: inputs.map((i) => i.pk.toString()),
        in_rho: inputs.map((i) => i.rho.toString()),
        in_rcm: inputs.map((i) => i.rcm.toString()),
        in_nsk: inputs.map((i) => i.nsk.toString()),
        in_rcv: inputs.map((i) => i.rcv.toString()),
        in_rcv_dep: inputs.map((i) => i.rcvDep.toString()),
        in_path_elements: inputs.map((i) =>
            i.pathElements.map((level) => level.map((e) => e.toString())),
        ),
        in_path_indices: inputs.map((i) => i.pathIndices.map((b) => b.toString())),
        in_is_dummy: inputs.map((i) => (i.isDummy ? "1" : "0")),

        out_asset: outputs.map((o) => o.asset.toString()),
        out_value: outputs.map((o) => o.value.toString()),
        out_pk: outputs.map((o) => o.pk.toString()),
        out_rho: outputs.map((o) => o.rho.toString()),
        out_rcm: outputs.map((o) => o.rcm.toString()),
        out_rcv: outputs.map((o) => o.rcv.toString()),
        out_rcv_dep: outputs.map((o) => o.rcvDep.toString()),

        out_clue_bits: opts.outputClues.map((c) => c.clueBits.toString()),
        out_clue_Rx: opts.outputClues.map((c) => c.clueRx.toString()),
        out_clue_Ry: opts.outputClues.map((c) => c.clueRy.toString()),

        out_aux_digest: opts.outputAuxDigest.toString(),
    };
}

/** Blinders for a dummy input slot. */
export interface DummyBlinders {
    /** Spend-time value-commitment blinder. */
    rcv: Field;
    /** Deposit-anchor blinder. Unconstrained here: the leaf check is skipped. */
    rcvDep: Field;
}

// Domain separators for the blinder derivation. Outside the TAG_* table in
// tags.circom, as these never enter a circuit preimage.
const DUMMY_RCV_DOMAIN = 0x647563n; // "duc"
const DUMMY_RCVDEP_DOMAIN = 0x647564n; // "dud"

// Keep the result under 2^253, the width MulH's Num2Bits enforces on rcv.
const BLINDER_MASK = (1n << 252n) - 1n;

/**
 * Blinders for a dummy input slot, derived from `rho` and distinct per dummy.
 * For tests and vector generation only.
 */
export function deterministicDummyBlinders(P: Poseidon, rho: Field): DummyBlinders {
    return {
        rcv: P.hash([DUMMY_RCV_DOMAIN, rho]) & BLINDER_MASK,
        rcvDep: P.hash([DUMMY_RCVDEP_DOMAIN, rho]) & BLINDER_MASK,
    };
}

/**
 * Dummy spent slot. `is_dummy = 1` bypasses Merkle membership and the pk check.
 *
 * nf = Poseidon(TAG_NF, nk, rho, cm) with nk = Poseidon(TAG_NK, 0); a fresh
 * `rho` keeps nf distinct from prior dummies and from any real spend. `cm` must
 * be the commitment SpentNote actually recomputes from the dummy's zero fields —
 * the circuit feeds it into the nullifier, so a placeholder 0 would fail.
 *
 * `blinders` defaults to a derivation from `rho`. Blinders must differ between
 * dummies, since `cv = 0·gen + rcv·H` with a shared `rcv` is the same point in
 * every transaction and identifies the slot as a dummy; they must also be
 * reproducible, since the published vectors contain them. Deriving from `rho`
 * satisfies both. Not suitable for production key material.
 */
export function dummyInputAt(
    P: Poseidon,
    depth: number,
    rho: Field,
    blinders: DummyBlinders = deterministicDummyBlinders(P, rho),
): SpentNote {
    const nsk = 0n;
    const note: Note = {
        asset: 0n,
        value: 0n,
        pk: 0n,
        rho,
        rcm: 0n,
        rcv: blinders.rcv,
        rcvDep: blinders.rcvDep,
    };
    const cm = buildNoteCommitment(P, note);
    const nf = buildNullifierFromNsk(P, nsk, rho, cm);
    const pathElements: Field[][] = [];
    for (let i = 0; i < depth; i++) pathElements.push([0n, 0n, 0n]);
    return {
        ...note,
        nsk,
        cm,
        nf,
        leafIndex: 0,
        pathElements,
        pathIndices: new Array(depth).fill(0),
        isDummy: true,
    };
}

/** Zero-value output slot. Padding for bundles that produce fewer notes than N_OUT. */
export function dummyOutput(asset: Field = 1n): Note {
    return { asset, value: 0n, pk: 0n, rho: 0n, rcm: 0n, rcv: 0n, rcvDep: 0n };
}
