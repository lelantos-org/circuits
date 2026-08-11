// Poseidon over BN254 with the iden3 constants, matching circomlib's
// `Poseidon(n)` template.
//
// poseidon-lite exports one fixed-arity function per width and returns bigints.
// Arities in use: 4 (TAG_LEAF), 5 (TAG_MERKLE nodes), 6 (FMD).

import {
    poseidon1,
    poseidon2,
    poseidon3,
    poseidon4,
    poseidon5,
    poseidon6,
    poseidon7,
    poseidon8,
} from "poseidon-lite";
import type { Field } from "./field.js";

const TABLE: Record<number, (xs: Field[]) => bigint> = {
    1: poseidon1 as (xs: Field[]) => bigint,
    2: poseidon2 as (xs: Field[]) => bigint,
    3: poseidon3 as (xs: Field[]) => bigint,
    4: poseidon4 as (xs: Field[]) => bigint,
    5: poseidon5 as (xs: Field[]) => bigint,
    6: poseidon6 as (xs: Field[]) => bigint,
    7: poseidon7 as (xs: Field[]) => bigint,
    8: poseidon8 as (xs: Field[]) => bigint,
};

export class Poseidon {
    private constructor() {}

    // Async factory kept for API symmetry with `Jubjub.build()`, which really
    // does need to await circomlibjs.
    static async build(): Promise<Poseidon> {
        return new Poseidon();
    }

    hash(xs: Field[]): Field {
        const fn = TABLE[xs.length];
        if (!fn) throw new Error(`Poseidon arity ${xs.length} not supported (1..8)`);
        return fn(xs);
    }
}
