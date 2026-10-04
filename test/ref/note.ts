// Note commitment, nullifier, rho derivation, and key derivation.
// Mirrors src/lib/note.circom.

import { POW_2_64, type Field } from "./field.js";
import type { Poseidon } from "./poseidon.js";
import { TAG_CM, TAG_INNER, TAG_IVK, TAG_NF, TAG_NK, TAG_PK, TAG_RHO } from "./tags.js";

export interface Note {
    asset: Field;
    value: Field;
    /** Poseidon(TAG_PK, ivk, d) — the cm-binding pubkey. */
    pk: Field;
    rho: Field;
    /** Hiding randomness; the only secret in a published `inner` or `cm`. */
    rcm: Field;
}

export interface SpentNote extends Note {
    nsk: Field;
    /** Diversifier `pk` is derived under. Unconstrained on a dummy slot. */
    d: Field;
    cm: Field;
    nf: Field;
    leafIndex: number;
    pathElements: Field[][];
    pathIndices: number[];
    isDummy: boolean;
}

export interface NoteCommitInput {
    asset: Field;
    value: Field;
    pk: Field;
    rho: Field;
    rcm: Field;
}

/**
 * inner = Poseidon(TAG_INNER, pk, rho, rcm). Mirrors NoteInner in
 * src/lib/note.circom. A deposit publishes it beside its public (asset, value).
 */
export function buildInner(P: Poseidon, n: { pk: Field; rho: Field; rcm: Field }): Field {
    return P.hash([TAG_INNER, n.pk, n.rho, n.rcm]);
}

/**
 * cm = Poseidon(TAG_CM, asset·2^64 + value, inner): the form tree_update_batch
 * computes for a deposit leaf. Soundness requires asset < 2^64 and
 * value < 2^64; the circuit range-checks both.
 */
export function commitWithInner(P: Poseidon, asset: Field, value: Field, inner: Field): Field {
    if (asset >= POW_2_64) throw new Error("asset must fit in 64 bits");
    if (value >= POW_2_64) throw new Error("value must fit in 64 bits");
    return P.hash([TAG_CM, asset * POW_2_64 + value, inner]);
}

/**
 * cm = Poseidon(TAG_CM, asset·2^64 + value, Poseidon(TAG_INNER, pk, rho, rcm)).
 * Mirrors NoteInner + NoteCommitment in src/lib/note.circom. cm is the
 * commitment-tree leaf.
 */
export function buildNoteCommitment(P: Poseidon, n: NoteCommitInput): Field {
    return commitWithInner(P, n.asset, n.value, buildInner(P, n));
}

/**
 * nf = Poseidon(TAG_NF, nk, rho, cm). Mirrors Nullifier in note.circom.
 *
 * `cm` is in the preimage so that two notes sharing a rho have distinct
 * nullifiers; otherwise spending either locks the other (the faerie-gold
 * attack).
 */
export function buildNullifier(P: Poseidon, nk: Field, rho: Field, cm: Field): Field {
    return P.hash([TAG_NF, nk, rho, cm]);
}

export function buildNullifierFromNsk(P: Poseidon, nsk: Field, rho: Field, cm: Field): Field {
    return buildNullifier(P, deriveNk(P, nsk), rho, cm);
}

/**
 * rho = Poseidon(TAG_RHO, nf0, index). Mirrors DeriveRho in note.circom.
 * nf0 is the first input nullifier (chain-unique) and index the output index,
 * so no two committed output notes share a rho.
 */
export function buildRho(P: Poseidon, nf0: Field, index: number | bigint): Field {
    return P.hash([TAG_RHO, nf0, BigInt(index)]);
}

export function deriveIvk(P: Poseidon, nsk: Field): Field {
    return P.hash([TAG_IVK, nsk]);
}

/**
 * pk = Poseidon(TAG_PK, ivk, d). Mirrors DerivePk in note.circom. `d` is the
 * diversifier: any field element, giving one ivk a distinct pk per value.
 */
export function derivePkFromIvk(P: Poseidon, ivk: Field, d: Field): Field {
    return P.hash([TAG_PK, ivk, d]);
}

export function derivePk(P: Poseidon, nsk: Field, d: Field): Field {
    return derivePkFromIvk(P, deriveIvk(P, nsk), d);
}

/**
 * nk = Poseidon(TAG_NK, nsk). Mirrors DeriveNk in note.circom.
 * FVK component: an nk holder recomputes nf for any known rho without nsk.
 */
export function deriveNk(P: Poseidon, nsk: Field): Field {
    return P.hash([TAG_NK, nsk]);
}
