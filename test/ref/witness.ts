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

// Declared as type aliases rather than interfaces so they carry an implicit
// index signature, and so satisfy `CircuitInput` in lib/circuit.ts without a cast.

/**
 * The public slots the circuit evaluates: `TransactCompressN`'s coefficients,
 * in `PubInputs.compress(Transact)` order.
 *
 * Every one is pinned by a constraint elsewhere in `4x6.circom`. That is the
 * membership rule, not a coincidence of the layout — see `coeffs` in
 * `ref/compress.ts`.
 */
export type CircomCoeffInputs = {
    merkle_root: string;
    nullifier: string[];
    out_cm: string[];
    public_asset_id: string;
    public_in: string;
    public_out: string;
    in_cv: string[][];
    out_cv: string[][];
    /** Per-output value commitment anchoring (asset, value) into the Merkle leaf. */
    out_cv_dep: string[][];
};

/**
 * Logical public inputs that are **not** circuit signals.
 *
 * The circuit constrains none of them, so as PolyEval coefficients they were
 * free variables a prover could solve `y = Σ c_k z^k` with. They are bound
 * instead by being hashed into the Fiat-Shamir challenge: alter one and `z`
 * moves, so `y` moves, so the proof fails. `flatten` includes them; `coeffs`
 * does not; `toCircomInput` carries them alongside the witness but
 * `circuitSignals` drops them before the witness calculator sees them.
 */
export type TransactBinding = {
    recipient_address: string;
    chain_id: string;
    payer_address: string;
    relayer_address: string;
    out_clue_Rx: string[];
    out_clue_Ry: string[];
    out_clue_bits: string[];
    /** Digest over the encrypted-note payloads. */
    out_aux_digest: string;
};

/** Every logical public input: what `flatten` hashes into the challenge. */
export type CircomPublicInputs = CircomCoeffInputs & TransactBinding;

/** Full witness: the coefficient slots above plus the private ones. */
export type CircomTransactInput = CircomCoeffInputs & {
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
};

/**
 * What a builder produces: the circuit's witness plus the binding fields that
 * only reach the challenge. Kept as one object because every consumer needs
 * both — `flatten` to derive `z`, the witness calculator to prove — and
 * splitting them at the source would make it easy to hash one transaction and
 * prove another.
 */
export type TransactWitnessBundle = CircomTransactInput & TransactBinding;

/**
 * Project a bundle onto the circuit's signal set.
 *
 * The wasm witness calculator rejects an unknown key outright ("Too many values
 * for input signal"), so the binding fields must be dropped here rather than
 * left for circom to ignore. Written as an explicit pick, not a delete list: a
 * signal added to the circuit and forgotten here fails to compile.
 */
export function circuitSignals(w: TransactWitnessBundle): CircomTransactInput {
    return {
        z: w.z,
        merkle_root: w.merkle_root,
        nullifier: w.nullifier,
        out_cm: w.out_cm,
        public_asset_id: w.public_asset_id,
        public_in: w.public_in,
        public_out: w.public_out,
        in_cv: w.in_cv,
        out_cv: w.out_cv,
        out_cv_dep: w.out_cv_dep,
        in_asset: w.in_asset,
        in_value: w.in_value,
        in_pk: w.in_pk,
        in_rho: w.in_rho,
        in_rcm: w.in_rcm,
        in_nsk: w.in_nsk,
        in_rcv: w.in_rcv,
        in_rcv_dep: w.in_rcv_dep,
        in_path_elements: w.in_path_elements,
        in_path_indices: w.in_path_indices,
        in_is_dummy: w.in_is_dummy,
        out_asset: w.out_asset,
        out_value: w.out_value,
        out_pk: w.out_pk,
        out_rho: w.out_rho,
        out_rcm: w.out_rcm,
        out_rcv: w.out_rcv,
        out_rcv_dep: w.out_rcv_dep,
    };
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
 * Arity is taken from the argument lengths rather than hardcoded, so `nIn` and
 * `nOut` may differ.
 */
export function toCircomInput(P: Poseidon, J: Jubjub, opts: BuildOpts): TransactWitnessBundle {
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

// Keep the result under 2^252, the width MulH's Num2Bits(RCV_BITS) enforces on rcv.
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
 * be the commitment SpentNote recomputes from the dummy's zero fields: the
 * circuit feeds it into the nullifier, so a placeholder 0 would fail.
 *
 * `blinders` defaults to a derivation from `rho`. Blinders must differ between
 * dummies: `cv = 0·gen + rcv·H` with a shared `rcv` is the same point in every
 * transaction and identifies the slot as a dummy. They must also be
 * reproducible, since the published vectors contain them. Not suitable for
 * production key material.
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

// Domain separator for padding-output blinders, alongside the dummy-input pair
// above. Distinct from both, so a padding output at slot k and a dummy input at
// rho = k never derive the same blinder.
const PAD_OUT_DOMAIN = 0x706f75n; // "pou"

/**
 * Zero-value output slot, padding a bundle that produces fewer notes than N_OUT.
 *
 * `slot` is the output index the note occupies and seeds the blinders, which
 * must be non-zero and pairwise distinct:
 *
 *   - `cv = value·gen + rcv·H` and `cv_dep = value·gen + rcv_dep·H` are both
 *     published, `cv` per spend and `cv_dep` inside the Merkle leaf. At
 *     value = 0 and rcv = 0 both collapse to the Edwards identity (0, 1), the
 *     sentinel `src/4x6.circom` requires a padding slot not to publish; it
 *     reveals the transaction's true output count.
 *   - `rcv == rcv_dep` equates the spend-time `cv` with the leaf's `cv_dep`,
 *     which identifies the spent leaf
 *     (`src/lib/value_commit.circom :: ValueCommitPair`).
 *
 * Deterministic so the published vectors reproduce. Not suitable for production
 * key material; a wallet samples these uniformly.
 *
 * `pk = 0`: a padding output is unspendable by construction, and the value is
 * hashed into `cm` rather than published.
 */
export function dummyOutput(P: Poseidon, slot: number, asset: Field = 1n): Note {
    const seed = P.hash([PAD_OUT_DOMAIN, BigInt(slot)]);
    const { rcv, rcvDep } = deterministicDummyBlinders(P, seed);
    return { asset, value: 0n, pk: 0n, rho: 0n, rcm: 0n, rcv, rcvDep };
}
