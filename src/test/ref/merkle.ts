// Quaternary sparse Merkle tree, mirroring src/lib/merkle.circom:
//   node = Poseidon(TAG_MERKLE, c0, c1, c2, c3)
//
// Internal nodes are memoised; an insert evicts the O(depth) dirty path.

import type { Field } from "./field.js";
import type { Poseidon } from "./poseidon.js";
import { TAG_MERKLE } from "./tags.js";

const ARITY = 4;

// Beyond this the (level, index) cache key would exceed 2^53.
const MAX_DEPTH = 25;

/**
 * Stride making `level * stride + index` injective over every (level, index)
 * the tree can reach.
 *
 * At level L a cached index is < 4^(depth-L), so the widest level is L=1 with
 * indices < 4^(depth-1) = 2^(2·depth-2). Anything smaller aliases one level
 * into the next.
 *
 * The stride must scale with depth: a fixed 2^18 holds only at depth 10, and
 * at any greater depth a level-1 index runs past it and collides with a
 * level-2 key. `reference.test.ts` checks injectivity across every supported
 * depth, since the circuit tests exercise only depths 2 and 10.
 */
export function cacheKeyStride(depth: number): number {
    return 2 ** (2 * depth - 2);
}

export interface MerkleProof {
    pathElements: Field[][];
    pathIndices: number[];
}

export class MerkleTree {
    leaves: Field[] = [];
    private readonly zeros: Field[] = [];
    private readonly strides: number[];
    private readonly nodeCache = new Map<number, Field>();
    private readonly keyStride: number;

    constructor(
        private readonly P: Poseidon,
        readonly depth: number,
    ) {
        // keyStride · depth must stay within Number.MAX_SAFE_INTEGER:
        // 2·25−2 = 48 bits of index + 5 of level = 53.
        if (depth < 1 || depth > MAX_DEPTH) {
            throw new RangeError(`MerkleTree: depth must be 1..${MAX_DEPTH}, got ${depth}`);
        }
        this.keyStride = cacheKeyStride(depth);
        let z: Field = 0n;
        for (let i = 0; i < depth; i++) {
            this.zeros.push(z);
            z = this.hashNode(z, z, z, z);
        }
        this.zeros.push(z);
        this.strides = Array.from({ length: depth + 1 }, (_, i) => ARITY ** i);
    }

    /** The empty-subtree chain, `depth + 1` entries. Mirrors EMPTY_SUBTREE in common.circom. */
    emptySubtree(): Field[] {
        return [...this.zeros];
    }

    insert(leaf: Field): number {
        const idx = this.leaves.push(leaf) - 1;
        this.invalidatePath(idx);
        return idx;
    }

    /** Insert a contiguous block, evicting only the minimal dirty range. */
    bulkInsert(leaves: Field[]): void {
        if (leaves.length === 0) return;
        const lo = this.leaves.length;
        for (const leaf of leaves) this.leaves.push(leaf);
        this.invalidateRange(lo, this.leaves.length - 1);
    }

    /** Replace the whole leaf array. Safe on a tree that already has inserts. */
    setLeaves(leaves: Field[]): void {
        this.leaves = [...leaves];
        this.nodeCache.clear();
    }

    /**
     * Replace the leaf array with `n` copies of `c`, seeding the node cache so
     * the following `root()` / `frontier()` / handful of `insert`s cost
     * O(depth · ARITY) hashes rather than the ~(4^depth − 1)/3 a distinct-leaf
     * fill of the same size costs. At depth 10 that is ~40 hashes instead of
     * ~350k, which is what makes a production-depth prefill viable inside a
     * property test (see `test/lib/batch.ts::buildHonest`).
     *
     * A full subtree whose every leaf is `c` depends only on its level, so
     * `constChain` here plays the role `zeros` plays for the empty subtree.
     * `nodeAt` descends from the root through exactly one *partial* node per
     * level; the only other nodes it reads are that node's lower-indexed
     * siblings — full, and seeded below — and its higher-indexed ones, which
     * `nodeAt` short-circuits to `zeros`. `frontier()` reads the same seeded
     * siblings, so both agree with a naive fill (`reference.test.ts` checks it).
     *
     * Every filled frontier slot at a given level comes out equal under this
     * fill, so a caller that needs the siblings at one level to differ must use
     * `insert` / `setLeaves` and pay the full cost.
     */
    fillConstant(n: number, c: Field): void {
        if (!Number.isInteger(n) || n < 0 || n > ARITY ** this.depth) {
            throw new RangeError(`fillConstant: n must be an integer in 0..${ARITY ** this.depth}, got ${n}`);
        }
        this.leaves = new Array<Field>(n).fill(c);
        this.nodeCache.clear();
        if (n === 0) return;

        // constChain[lvl] = root of a full level-lvl subtree of `c` leaves.
        const constChain: Field[] = [c];
        for (let lvl = 1; lvl <= this.depth; lvl++) {
            const child = constChain[lvl - 1];
            constChain.push(this.hashNode(child, child, child, child));
        }

        // `partial` is the first level-lvl node not wholly below `n`: index
        // i < partial spans [i·stride, (i+1)·stride) with (i+1)·stride ≤ n, so
        // it is a full subtree of `c`. The root (lvl == depth) is left to
        // `nodeAt`; level 0 is read straight out of `leaves`.
        for (let lvl = 1; lvl < this.depth; lvl++) {
            const partial = Math.floor(n / this.strides[lvl]);
            const firstSibling = Math.floor(partial / ARITY) * ARITY;
            for (let idx = firstSibling; idx < partial; idx++) {
                this.nodeCache.set(this.cacheKey(lvl, idx), constChain[lvl]);
            }
        }
    }

    root(): Field {
        return this.nodeAt(this.depth, 0);
    }

    /**
     * Frontier snapshot for the lazy-root tree-update circuit, `depth × 3` slots.
     * For each level `lvl` and slot `k ∈ {0,1,2}`:
     *   frontier[lvl][k] = nodeAt(lvl, parentIdx * 4 + k)  if k < currentSlot
     *   frontier[lvl][k] = 0                                otherwise
     * with currentSlot = (N / 4^lvl) % 4, parentIdx = N / 4^(lvl+1), N = leaves.length.
     * Slots k ≥ currentSlot are not read by the next insert; zeroed deterministically.
     */
    frontier(): Field[][] {
        const N = this.leaves.length;
        const out: Field[][] = [];
        for (let lvl = 0; lvl < this.depth; lvl++) {
            const stride = this.strides[lvl];
            const slot = Math.floor(N / stride) % ARITY;
            const parentIdx = Math.floor(N / (stride * ARITY));
            const slots: Field[] = [];
            for (let k = 0; k < 3; k++) {
                if (k < slot) {
                    slots.push(this.nodeAt(lvl, parentIdx * ARITY + k));
                } else {
                    slots.push(0n);
                }
            }
            out.push(slots);
        }
        return out;
    }

    proof(leafIndex: number): MerkleProof {
        const pathElements: Field[][] = [];
        const pathIndices: number[] = [];
        let idx = leafIndex;

        for (let level = 0; level < this.depth; level++) {
            const selfPos = idx % ARITY;
            const parentIdx = Math.floor(idx / ARITY);
            const siblings: Field[] = [];
            for (let k = 0; k < ARITY; k++) {
                if (k !== selfPos) siblings.push(this.nodeAt(level, parentIdx * ARITY + k));
            }
            pathElements.push(siblings);
            pathIndices.push(selfPos);
            idx = parentIdx;
        }
        return { pathElements, pathIndices };
    }

    private nodeAt(level: number, index: number): Field {
        if (level === 0) return this.leaves[index] ?? 0n;
        if (index * this.strides[level] >= this.leaves.length) return this.zeros[level];

        const key = this.cacheKey(level, index);
        const cached = this.nodeCache.get(key);
        if (cached !== undefined) return cached;

        const firstChild = index * ARITY;
        const value = this.hashNode(
            this.nodeAt(level - 1, firstChild),
            this.nodeAt(level - 1, firstChild + 1),
            this.nodeAt(level - 1, firstChild + 2),
            this.nodeAt(level - 1, firstChild + 3),
        );
        this.nodeCache.set(key, value);
        return value;
    }

    private invalidatePath(leafIndex: number): void {
        let idx = Math.floor(leafIndex / ARITY);
        for (let level = 1; level <= this.depth; level++) {
            this.nodeCache.delete(this.cacheKey(level, idx));
            idx = Math.floor(idx / ARITY);
        }
    }

    // Evict all internal nodes whose subtrees overlap [lo, hi] at every level.
    private invalidateRange(lo: number, hi: number): void {
        let loIdx = Math.floor(lo / ARITY);
        let hiIdx = Math.floor(hi / ARITY);
        for (let level = 1; level <= this.depth; level++) {
            for (let i = loIdx; i <= hiIdx; i++) {
                this.nodeCache.delete(this.cacheKey(level, i));
            }
            loIdx = Math.floor(loIdx / ARITY);
            hiIdx = Math.floor(hiIdx / ARITY);
        }
    }

    private cacheKey(level: number, index: number): number {
        return level * this.keyStride + index;
    }

    private hashNode(c0: Field, c1: Field, c2: Field, c3: Field): Field {
        return this.P.hash([TAG_MERKLE, c0, c1, c2, c3]);
    }
}
