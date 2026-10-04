// Transact circuit witness construction. Values are emitted as decimal strings;
// the key set is part of the interface.

import type { Field } from "./field.js";
import type { Poseidon } from "./poseidon.js";
import { transactDigest } from "./compress.js";
import {
    buildNoteCommitment,
    buildNullifierFromNsk,
    derivePk,
    type Note,
    type SpentNote,
} from "./note.js";

/** Per-output FMD clue witness. */
export interface ClueInputs {
    clueBits: Field;
    clueRx: Field;
    clueRy: Field;
}

// Type aliases rather than interfaces: the implicit index signature satisfies
// `CircuitInput` in lib/circuit.ts without a cast.

/**
 * The public slots that are circuit input signals: `TransactCompressN`'s
 * coefficients, in `PubInputs.compress(Transact)` order. The circuit computes
 * the digest from these.
 */
export type CircomCoeffInputs = {
    merkle_root: string;
    nullifier: string[];
    out_cm: string[];
    public_asset_id: string;
    public_out: string;
};

/**
 * Logical public inputs that are not circuit input signals.
 *
 * `digest` is the calldata copy of the coefficient digest; the circuit
 * recomputes its own from the coefficient signals. The circuit constrains none
 * of the others: they are bound by being hashed into the Fiat-Shamir challenge
 * (`flatten` includes them, `coeffs` does not). `circuitSignals` drops all of
 * these before witness calculation.
 */
export type TransactBinding = {
    digest: string;
    recipient_address: string;
    chain_id: string;
    payer_address: string;
    relayer_address: string;
    /** Hash of the swap intent `SwapWrapper` checks; `0` for other spends. */
    intent_hash: string;
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
    in_rho: string[];
    in_rcm: string[];
    in_nsk: string[];
    in_d: string[];
    in_path_elements: string[][][];
    in_path_indices: string[][];
    in_is_dummy: string[];

    out_asset: string[];
    out_value: string[];
    out_pk: string[];
    out_rho: string[];
    out_rcm: string[];
};

/**
 * Builder output: the circuit's witness plus the binding fields that only reach
 * the challenge.
 */
export type TransactWitnessBundle = CircomTransactInput & TransactBinding;

/**
 * Project a bundle onto the circuit's signal set: the wasm witness calculator
 * rejects an unknown key ("Too many values for input signal").
 */
export function circuitSignals(w: TransactWitnessBundle): CircomTransactInput {
    return {
        z: w.z,
        merkle_root: w.merkle_root,
        nullifier: w.nullifier,
        out_cm: w.out_cm,
        public_asset_id: w.public_asset_id,
        public_out: w.public_out,
        in_asset: w.in_asset,
        in_value: w.in_value,
        in_rho: w.in_rho,
        in_rcm: w.in_rcm,
        in_nsk: w.in_nsk,
        in_d: w.in_d,
        in_path_elements: w.in_path_elements,
        in_path_indices: w.in_path_indices,
        in_is_dummy: w.in_is_dummy,
        out_asset: w.out_asset,
        out_value: w.out_value,
        out_pk: w.out_pk,
        out_rho: w.out_rho,
        out_rcm: w.out_rcm,
    };
}

export interface BuildOpts {
    publicAssetId: Field;
    publicOut: Field;
    inputs: SpentNote[];
    outputs: Note[];
    outputClues: ClueInputs[];
    merkleRoot: Field;
    recipientAddress?: Field;
    chainId?: Field;
    /** Who may drive a satellite that consumes the spend; bound through the challenge. */
    payerAddress?: Field;
    /** Must equal `msg.sender` of the on-chain `transact` call; blocks relayer front-running. */
    relayerAddress?: Field;
    /** `SwapWrapper`'s intent hash for a swap's withdraw leg; zero elsewhere. */
    intentHash?: Field;
    /** Fiat-Shamir challenge; defaults to 1n. */
    z?: Field;
    /**
     * `auxDigest(aux)` over the outputs' encrypted-note payloads. The contract
     * recomputes this slot from calldata.
     */
    outputAuxDigest: Field;
}

/**
 * Build the circom input object for Transact(DEPTH, N_IN, N_OUT). Arity is
 * taken from the argument lengths.
 */
export function toCircomInput(P: Poseidon, opts: BuildOpts): TransactWitnessBundle {
    const { inputs, outputs, publicAssetId, publicOut, merkleRoot } = opts;

    if (inputs.length === 0) throw new Error("toCircomInput: need at least one input");
    if (outputs.length === 0) throw new Error("toCircomInput: need at least one output");
    if (opts.outputClues.length !== outputs.length) {
        throw new Error("toCircomInput: outputClues length must equal outputs length");
    }

    const recipientAddress = opts.recipientAddress ?? 0n;
    const chainId = opts.chainId ?? 0n;
    const payerAddress = opts.payerAddress ?? 0n;
    const relayerAddress = opts.relayerAddress ?? 0n;
    const intentHash = opts.intentHash ?? 0n;

    const z = opts.z ?? 1n;

    const coeffSignals: CircomCoeffInputs = {
        merkle_root: merkleRoot.toString(),
        nullifier: inputs.map((i) => i.nf.toString()),
        out_cm: outputs.map((o) => buildNoteCommitment(P, o).toString()),
        public_asset_id: publicAssetId.toString(),
        public_out: publicOut.toString(),
    };

    return {
        z: z.toString(),
        ...coeffSignals,
        digest: transactDigest(coeffSignals).toString(),
        recipient_address: recipientAddress.toString(),
        chain_id: chainId.toString(),
        payer_address: payerAddress.toString(),
        relayer_address: relayerAddress.toString(),
        intent_hash: intentHash.toString(),

        in_asset: inputs.map((i) => i.asset.toString()),
        in_value: inputs.map((i) => i.value.toString()),
        in_rho: inputs.map((i) => i.rho.toString()),
        in_rcm: inputs.map((i) => i.rcm.toString()),
        in_nsk: inputs.map((i) => i.nsk.toString()),
        in_d: inputs.map((i) => i.d.toString()),
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

        out_clue_bits: opts.outputClues.map((c) => c.clueBits.toString()),
        out_clue_Rx: opts.outputClues.map((c) => c.clueRx.toString()),
        out_clue_Ry: opts.outputClues.map((c) => c.clueRy.toString()),

        out_aux_digest: opts.outputAuxDigest.toString(),
    };
}

/**
 * Dummy spent slot. `is_dummy = 1` bypasses Merkle membership and the
 * `asset != 0` check.
 *
 * nf = Poseidon(TAG_NF, nk, rho, cm) with nk = Poseidon(TAG_NK, 0); a fresh
 * `rho` keeps nf distinct from prior dummies and from any real spend. `cm` must
 * be the commitment SpentNote recomputes from the dummy's fields, under the pk
 * it derives from `nsk` and `d`: the circuit feeds it into the nullifier.
 *
 * `nsk`, `d` and `rcm` are zero, so `rho` is what hides the slot: a wallet
 * samples it uniformly. Not suitable for production.
 */
export function dummyInputAt(P: Poseidon, depth: number, rho: Field): SpentNote {
    const nsk = 0n;
    const d = 0n;
    const note: Note = { asset: 0n, value: 0n, pk: derivePk(P, nsk, d), rho, rcm: 0n };
    const cm = buildNoteCommitment(P, note);
    const nf = buildNullifierFromNsk(P, nsk, rho, cm);
    const pathElements: Field[][] = [];
    for (let i = 0; i < depth; i++) pathElements.push([0n, 0n, 0n]);
    return {
        ...note,
        nsk,
        d,
        cm,
        nf,
        leafIndex: 0,
        pathElements,
        pathIndices: new Array(depth).fill(0),
        isDummy: true,
    };
}

// Domain separator for a padding output's `rcm`. Outside the TAG_* table in
// tags.circom, as it never enters a circuit preimage as a tag.
const PAD_OUT_DOMAIN = 0x706f75n; // "pou"

/**
 * Zero-value output slot, padding a bundle that produces fewer notes than N_OUT.
 * `pk = 0` makes it unspendable.
 *
 * `slot` is the output index the note occupies and seeds `rcm`, which must be
 * non-zero and differ between slots. An output's `rho` is publicly derivable
 * (`DeriveRho` over `nullifier[0]`), so `rcm` is the only secret in `cm`: a
 * known `rcm` reveals the transaction's true output count.
 *
 * Deterministic so the published vectors reproduce. Not suitable for
 * production: a wallet samples `rcm` uniformly.
 */
export function dummyOutput(P: Poseidon, slot: number, asset: Field = 1n): Note {
    const rcm = P.hash([PAD_OUT_DOMAIN, BigInt(slot)]);
    return { asset, value: 0n, pk: 0n, rho: 0n, rcm };
}
