// Single import path for the circuit test suite.
//
// Primitives and witness builders live in `./ref`, transcribed from the circom
// under `src/lib/`. This package has no dependency on `@lelantos-org/sdk`;
// agreement with the SDK is established through the vectors under `vectors/`,
// which are generated from `./ref`.
//
// Primitives belong in `./ref` rather than in individual test files, since the
// published vectors are generated from that directory.

export * from "./ref/index.js";

import { buildNoteCommitment, buildNullifierFromNsk, type Field, type Poseidon } from "./ref/index.js";

// Short aliases used throughout the suite.
export function commit(
    P: Poseidon,
    n: { asset: Field; value: Field; pk: Field; rho: Field; rcm: Field },
): Field {
    return buildNoteCommitment(P, n);
}

// nf = Poseidon(TAG_NF, nk, rho, cm) — cm is in the preimage so a rho
// collision alone cannot brick a note (see Nullifier in lib/note.circom).
export function nullifier(P: Poseidon, nsk: Field, rho: Field, cm: Field): Field {
    return buildNullifierFromNsk(P, nsk, rho, cm);
}
