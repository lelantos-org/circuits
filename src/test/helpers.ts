// Helpers for building MASP test inputs that match circuits/2x2.circom.
//
// Crypto primitives + witness builder live in `@lelantos-org/sdk` so circuit
// tests, the wallet, and Foundry fixture generators all see the same
// shapes byte-for-byte. Do NOT re-implement here — that would silently
// divert SDK from circuit and is exactly the bug this layout prevents.

import {
    Poseidon,
    Jubjub,
    H_BASE,
    deriveIvk,
    derivePk,
    derivePkFromIvk,
    deriveNk,
    buildNoteCommitment,
    buildNullifier,
    buildNullifierFromNsk,
    buildRho,
    MerkleTree,
    type Field,
    type Point,
} from "@lelantos-org/sdk/crypto";

export { Poseidon, Jubjub, H_BASE, deriveIvk, derivePk, derivePkFromIvk, deriveNk, buildNullifier, buildRho, MerkleTree };
export type { Field, Point };

export {
    toCircomInput,
    dummyOutput,
    dummyInputAt,
    type BuildOpts,
} from "@lelantos-org/sdk/bundle";
export type { Note, SpentNote } from "@lelantos-org/sdk";

export {
    FMD_DEFAULT_GAMMA,
    fmdGenDetectionKey,
    fmdFlagKeyFromDetection,
    fmdFlag,
    BABYJUB_SUBGROUP_ORDER,
} from "@lelantos-org/sdk";

// Legacy names — circuit tests historically used `commit` / `nullifier`.
// Keep them as aliases over the SDK so existing tests stay green without
// touching their imports.
export function commit(P: Poseidon, n: { asset: Field; value: Field; pk: Field; rho: Field; rcm: Field }): Field {
    return buildNoteCommitment(P, n);
}
// nf = Poseidon(TAG_NF, nk, rho, cm) — cm is in the preimage so a rho
// collision alone cannot brick a note (see Nullifier in lib/note.circom).
export function nullifier(P: Poseidon, nsk: Field, rho: Field, cm: Field): Field {
    return buildNullifierFromNsk(P, nsk, rho, cm);
}

