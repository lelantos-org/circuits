// Note commitment, nullifier, rho derivation, and key derivation.
// Mirrors src/lib/note.circom.

import { POW_2_64, type Field, type Point } from "./field.js";
import type { Poseidon } from "./poseidon.js";
import { TAG_IVK, TAG_LEAF, TAG_NF, TAG_NK, TAG_PK, TAG_RHO } from "./tags.js";

export interface Note {
    asset: Field;
    value: Field;
    /** Poseidon(TAG_PK, ivk) — the cm-binding pubkey. */
    pk: Field;
    rho: Field;
    rcm: Field;
    rcv: Field;
    /** Pedersen blinder for the deposit-anchor commitment cv_dep. */
    rcvDep: Field;
}

export interface SpentNote extends Note {
    nsk: Field;
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
 * cm = Poseidon(asset·2^64 + value, pk, rho, rcm).
 *
 * Arity-4 and untagged: the arity plus the (asset, value) packing provide the
 * domain separation. Mirrors NoteCommitment in src/lib/note.circom. Soundness
 * needs asset < 2^64 and value < 2^64 — the circuit range-checks both, so the
 * throws here keep the off-circuit path honest.
 */
export function buildNoteCommitment(P: Poseidon, n: NoteCommitInput): Field {
    if (n.asset >= POW_2_64) throw new Error("asset must fit in 64 bits");
    if (n.value >= POW_2_64) throw new Error("value must fit in 64 bits");
    const packedAv = n.asset * POW_2_64 + n.value;
    return P.hash([packedAv, n.pk, n.rho, n.rcm]);
}

/**
 * leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y).
 *
 * The commitment-tree leaf, as built by tree_update_batch.circom and
 * recomputed by spent.circom. `cv_dep` is what pins (asset, value) to the
 * leaf, so a spend cannot substitute either later.
 */
export function buildLeaf(P: Poseidon, cm: Field, cvDep: Point): Field {
    return P.hash([TAG_LEAF, cm, cvDep[0], cvDep[1]]);
}

/**
 * nf = Poseidon(TAG_NF, nk, rho, cm). Mirrors Nullifier in note.circom.
 *
 * Takes nk directly so FVK holders (nk without nsk) can recompute nullifiers.
 * `cm` is in the preimage so the nullifier identifies the exact note. Without
 * it, two notes sharing a rho share a nullifier and spending either permanently
 * locks the other: the faerie-gold attack.
 */
export function buildNullifier(P: Poseidon, nk: Field, rho: Field, cm: Field): Field {
    return P.hash([TAG_NF, nk, rho, cm]);
}

/** Convenience wrapper for spend paths holding nsk. */
export function buildNullifierFromNsk(P: Poseidon, nsk: Field, rho: Field, cm: Field): Field {
    return buildNullifier(P, deriveNk(P, nsk), rho, cm);
}

/**
 * rho = Poseidon(TAG_RHO, nf0, index). Mirrors DeriveRho in note.circom.
 *
 * Output rho is bound to the first input nullifier (chain-unique) plus the
 * output index, so no two committed output notes can share a rho.
 */
export function buildRho(P: Poseidon, nf0: Field, index: number | bigint): Field {
    return P.hash([TAG_RHO, nf0, BigInt(index)]);
}

export function deriveIvk(P: Poseidon, nsk: Field): Field {
    return P.hash([TAG_IVK, nsk]);
}

export function derivePkFromIvk(P: Poseidon, ivk: Field): Field {
    return P.hash([TAG_PK, ivk]);
}

export function derivePk(P: Poseidon, nsk: Field): Field {
    return derivePkFromIvk(P, deriveIvk(P, nsk));
}

/**
 * nk = Poseidon(TAG_NK, nsk). Mirrors DeriveNk in note.circom.
 * FVK component: an nk holder recomputes nf for any known rho without nsk.
 */
export function deriveNk(P: Poseidon, nsk: Field): Field {
    return P.hash([TAG_NK, nsk]);
}
