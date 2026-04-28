// Helpers for building MASP test inputs that match circuits/2x2.circom.
//
// Crypto primitives + witness builder live in `@lelantos/sdk` so circuit
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
    buildNoteCommitment,
    buildNullifier,
    MerkleTree,
    type Field,
    type Point,
} from "../../../sdk/src/crypto/index";

export { Poseidon, Jubjub, H_BASE, deriveIvk, derivePk, derivePkFromIvk, MerkleTree };
export type { Field, Point };

export {
    toCircomInput,
    dummyOutput,
    dummyInputAt,
    type BuildOpts,
} from "../../../sdk/src/witness";
export type { Note, SpentNote } from "../../../sdk/src/notes";

// Legacy names — circuit tests historically used `commit` / `nullifier`.
// Keep them as aliases over the SDK so existing tests stay green without
// touching their imports.
export function commit(P: Poseidon, n: { asset: Field; value: Field; pk: Field; rho: Field; rcm: Field }): Field {
    return buildNoteCommitment(P, n);
}
export function nullifier(P: Poseidon, nsk: Field, rho: Field): Field {
    return buildNullifier(P, nsk, rho);
}

