// Merkle path recomputation: the verification counterpart to MerkleTree.proof().
//
// An independent implementation of the same quaternary node hashing as
// merkle.ts. The two are kept separate so one constructs and the other checks;
// merkle.test.ts cross-validates them.

import type { Field } from "./field.js";
import type { Poseidon } from "./poseidon.js";
import { TAG_MERKLE } from "./tags.js";

const ARITY = 4;

/** Recompute the root a `(leaf, path)` pair attests to. */
export function rootFromPath(
    P: Poseidon,
    leaf: Field,
    pathElements: Field[][],
    pathIndices: number[],
): Field {
    let cur: Field = leaf;
    for (let lvl = 0; lvl < pathIndices.length; lvl++) {
        const slot = pathIndices[lvl];
        const sibs = pathElements[lvl];
        const children: Field[] = [];
        let s = 0;
        for (let k = 0; k < ARITY; k++) {
            if (k === slot) children.push(cur);
            else children.push(sibs[s++]);
        }
        cur = P.hash([TAG_MERKLE, children[0], children[1], children[2], children[3]]);
    }
    return cur;
}
