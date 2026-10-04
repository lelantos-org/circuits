// Single import path for the circuit test suite.
//
// Primitives and witness builders live in `./ref`, transcribed from the circom
// under `src/lib/`. Agreement with `@lelantos-org/sdk` is established through
// the vectors under `vectors/`, which are generated from `./ref`.

export * from "./ref/index.js";

import { buildNoteCommitment, buildNullifierFromNsk, type Field, type Poseidon } from "./ref/index.js";

export function commit(
    P: Poseidon,
    n: { asset: Field; value: Field; pk: Field; rho: Field; rcm: Field },
): Field {
    return buildNoteCommitment(P, n);
}

// nf = Poseidon(TAG_NF, nk, rho, cm). cm is in the preimage so a rho collision
// alone cannot lock a note; see Nullifier in lib/note.circom.
export function nullifier(P: Poseidon, nsk: Field, rho: Field, cm: Field): Field {
    return buildNullifierFromNsk(P, nsk, rho, cm);
}
