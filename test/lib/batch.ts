// TreeUpdateBatch witness builders, shared by the spec and fuzz suites.

import {
    Poseidon,
    MerkleTree,
    buildInner,
    commitWithInner,
    fiatShamirZ,
    hornerEval,
    type Field,
} from "../helpers";
import {
    treeUpdateBatchChallenge,
    treeUpdateBatchCoeffs,
    treeUpdateBatchDigest,
    padToSlots,
    type TreeUpdateBatchArgs,
    type TreeUpdateBatchPublicArgs,
} from "./inputs";
import { BATCH_DEPTH, MAX_L } from "./constants";

/** One leaf's contribution to a batch. */
export interface LeafWitness {
    /**
     * What `cms[k]` carries: the note commitment on a spend leaf, the
     * depositor's `inner` on a deposit leaf.
     */
    word: Field;
    /**
     * What the tree holds. On a spend leaf it is `word`. On a deposit leaf it
     * is the commitment the circuit builds from `leafAsset`, `leafPublicIn` and
     * `word`.
     */
    leaf: Field;
    leafAsset: Field;
    leafPublicIn: Field;
    isDeposit: 0 | 1;
}

/**
 * A full batch witness: the circuit inputs, plus the two public signals the
 * contract would hand the verifier beside `z`. `y` is the reference evaluation
 * and `digest` the calldata digest word; the circuit must output both.
 */
export interface BatchWitness extends TreeUpdateBatchArgs {
    startIndex: number;
    actualCount: number;
    isDeposit: number[];
    y: Field;
}

export function buildLeafWitness(opts: {
    P: Poseidon;
    asset: Field;
    val: Field;
    pk: Field;
    rho: Field;
    rcm: Field;
    isDeposit: 0 | 1;
}): LeafWitness {
    const { P, asset, val, pk, rho, rcm, isDeposit } = opts;
    const inner = buildInner(P, { pk, rho, rcm });
    const cm = commitWithInner(P, asset, val, inner);
    // Either way the leaf is the note's commitment. A deposit hands the
    // circuit `inner` and the public amount and lets it build the leaf; a
    // spend hands it the commitment a transact proof already bound.
    return isDeposit === 1
        ? { word: inner, leaf: cm, leafAsset: asset, leafPublicIn: val, isDeposit }
        : { word: cm, leaf: cm, leafAsset: 0n, leafPublicIn: 0n, isDeposit };
}

/** Leaf-witness factory taking only the discriminating fields; the rest are fixed. */
export function simpleLeaf(opts: {
    P: Poseidon;
    val: Field;
    isDeposit: 0 | 1;
    asset?: Field;
    pk?: Field;
}): LeafWitness {
    return buildLeafWitness({
        P: opts.P,
        asset: opts.asset ?? 7n,
        val: opts.val,
        pk: opts.pk ?? 0xabcn,
        rho: 1n, rcm: 3n,
        isDeposit: opts.isDeposit,
    });
}

/**
 * A leaf derived entirely from `seed`, for property tests needing k distinct
 * leaves. `val` and `asset` override the seeded ones where a shape needs
 * specific values.
 */
export function seededLeaf(
    P: Poseidon,
    seed: number,
    isDeposit: 0 | 1,
    val?: Field,
    asset?: Field,
): LeafWitness {
    return buildLeafWitness({
        P,
        asset: asset ?? 7n,
        val: val ?? BigInt(100 + seed),
        pk: BigInt(0xb000 + seed),
        rho: BigInt(1 + 2 * seed),
        rcm: BigInt(3 + 2 * seed),
        isDeposit,
    });
}

/**
 * Filler value for the pre-batch leaves of frontier block `(level, index)`.
 *
 * One of three constants, by the block's slot under its parent, so `fillBlocks`
 * builds a production-depth prefill from three hash chains instead of one hash
 * per leaf. The frontier slot `(level, k)` then holds constant `k` hashed up
 * `level` times: distinct across the slots of a level and across levels, so a
 * misrouted slot changes a root.
 */
export function prefillLeaf(_level: number, index: number): Field {
    return 0xdead0000n + BigInt(index % 4);
}

/**
 * Start positions at both edges of every digit's block at every level, plus the
 * two ends of a depth-`depth` tree: each digit value appears at each level, both
 * adjacent to a carry and not. Tests that need each (level, digit) shape once use
 * these instead of every start.
 */
export function representativeStarts(depth: number): number[] {
    const capacity = 4 ** depth;
    const starts = new Set([0, capacity - 1]);
    for (let d = 0; d < depth; d++) {
        for (let r = 0; r < 4; r++) {
            starts.add(r * 4 ** d);
            starts.add((r + 1) * 4 ** d - 1);
        }
    }
    return [...starts].filter(s => s < capacity).sort((a, b) => a - b);
}

/**
 * An honest batch: `prefilled` filler leaves already in the tree, then
 * `leaves` inserted on top, with the frontier taken at the old root and the
 * Fiat-Shamir pair derived over the resulting coefficients.
 */
export function buildHonest(
    P: Poseidon,
    prefilled: number,
    leaves: LeafWitness[],
): BatchWitness {
    const tree = new MerkleTree(P, BATCH_DEPTH);
    tree.fillBlocks(prefilled, prefillLeaf);
    const oldRoot = tree.root();
    const frontier = tree.frontier();

    for (const l of leaves) tree.insert(l.leaf);
    const newRoot = tree.root();

    const w: BatchWitness = {
        oldRoot,
        newRoot,
        startIndex: prefilled,
        actualCount: leaves.length,
        cms: padToSlots(leaves.map(l => l.word), MAX_L, 0n),
        leafAsset: padToSlots(leaves.map(l => l.leafAsset), MAX_L, 0n),
        leafPublicIn: padToSlots(leaves.map(l => l.leafPublicIn), MAX_L, 0n),
        isDeposit: padToSlots(leaves.map(l => l.isDeposit as number), MAX_L, 0),
        frontier,
        digest: 0n,
        z: 0n,
        y: 0n,
    };
    rebindFiatShamir(w);
    return w;
}

/**
 * Re-derive the calldata digest and Fiat-Shamir `(z, y)` from the witness in
 * its current state: what an honest prover submits for it.
 *
 * Call after mutating any coefficient, so the failure comes from the
 * constraint under test rather than stale calldata. `frontier` is outside the
 * coefficient vector and does not require it.
 *
 * Implemented as `bindFiatShamir` applied to the calldata view that matches the
 * witness, so the derivation has a single definition.
 */
export function rebindFiatShamir(w: BatchWitness): void {
    w.digest = treeUpdateBatchDigest(w);
    bindFiatShamir(w, calldataView(w));
}

/**
 * Snapshot a witness's logical public inputs — the calldata view.
 *
 * A structural clone rather than a field-by-field copy. The copy must be deep:
 * otherwise the two views share arrays, a divergence case mutates both, and
 * `expectNotForgeable` compares a view against itself and passes vacuously. A
 * hand-written projection would lose that property for any field added to
 * `TreeUpdateBatchPublicArgs`.
 *
 * `BatchWitness` extends the public args with `frontier`, `z` and `y`;
 * carrying them along is harmless, since the challenge and coefficient functions
 * read only the public fields. The view's `digest` is the witness's at the time
 * of the snapshot; a divergence case decides whether to leave it or recompute
 * it for the rewritten coefficients (`redigest`).
 */
export function calldataView(w: BatchWitness): TreeUpdateBatchPublicArgs {
    return structuredClone(w);
}

/** Recompute a calldata view's digest word for its current coefficients. */
export function redigest(c: TreeUpdateBatchPublicArgs): void {
    c.digest = treeUpdateBatchDigest(c);
}

/**
 * Bind `(z, y, digest)` to a calldata view that may differ from the witness `w`:
 * the three public signals the contract would hand the verifier for that
 * calldata.
 *
 * `rebindFiatShamir` combines two roles that are separate in deployment:
 * deriving the challenge and choosing the witness. The contract derives `z` and
 * `y` from calldata; the prover then picks any witness satisfying the R1CS at
 * that `z`, and Groth16 does not require the two to describe the same batch.
 * Combining them makes the divergence unrepresentable, so a signal hashed into
 * `z` but pinned by no constraint appears bound when it is free.
 *
 * Use this to test whether the prover can diverge from the contract's calldata,
 * and `rebindFiatShamir` to test whether a specific constraint fires.
 */
export function bindFiatShamir(w: BatchWitness, calldata: TreeUpdateBatchPublicArgs): void {
    w.z = fiatShamirZ(treeUpdateBatchChallenge(calldata));
    w.y = hornerEval(treeUpdateBatchCoeffs(calldata), w.z);
    w.digest = calldata.digest;
}

/**
 * `count` leaves in the layout MASP's deposit path emits: slot 2i is a
 * principal and slot 2i+1 its fee note. The circuit does not require this
 * (every constraint is per-slot), but it is the shape a flush produces.
 *
 * Fee notes carry zero value at asset 0, the zero-fee deposit: a permitted
 * shape (`_validateDeposit`: "The fee note's value may be zero"), and the one
 * a flush of four such deposits fills half its slots with.
 */
export function depositPairs(P: Poseidon, count: number): LeafWitness[] {
    return Array.from({ length: count }, (_, i) =>
        i % 2 === 0
            ? seededLeaf(P, i, 1)
            : seededLeaf(P, i, 1, 0n, 0n));
}

/**
 * The builders above with the hash bound, for suites that hold a `P` for their
 * whole run. Mirrors `lib/transact.ts :: TxBuilder`.
 */
export class BatchBuilder {
    constructor(public readonly P: Poseidon) {}

    /** `simpleLeaf`: only the discriminating fields, the rest fixed. */
    leaf(opts: { val: Field; isDeposit: 0 | 1; asset?: Field; pk?: Field }): LeafWitness {
        return simpleLeaf({ P: this.P, ...opts });
    }

    /** `buildLeafWitness`: every field chosen. */
    leafWith(opts: Omit<Parameters<typeof buildLeafWitness>[0], "P">): LeafWitness {
        return buildLeafWitness({ P: this.P, ...opts });
    }

    /** `seededLeaf`: k distinct leaves from k seeds. */
    seeded(seed: number, isDeposit: 0 | 1, val?: Field, asset?: Field): LeafWitness {
        return seededLeaf(this.P, seed, isDeposit, val, asset);
    }

    /** `count` seeded leaves, seeds `0..count-1`, deposit flag per slot. */
    seededMany(count: number, isDeposit: (i: number) => 0 | 1): LeafWitness[] {
        return Array.from({ length: count }, (_, i) => this.seeded(i, isDeposit(i)));
    }

    /** `buildHonest`: `leaves` inserted after `prefilled` filler leaves. */
    honest(prefilled: number, leaves: LeafWitness[]): BatchWitness {
        return buildHonest(this.P, prefilled, leaves);
    }

    /** One `leaf(opts)` batch at `prefilled` (default 0): the base most single-constraint cases mutate. */
    single(opts: Parameters<BatchBuilder["leaf"]>[0], prefilled = 0): BatchWitness {
        return this.honest(prefilled, [this.leaf(opts)]);
    }

    /** `depositPairs`: principal/fee pairs as a flush emits them. */
    depositPairs(count: number): LeafWitness[] {
        return depositPairs(this.P, count);
    }
}

// ===== divergent-witness coverage =====

/**
 * One field a batch's calldata can declare differently from the witness proved
 * against it.
 *
 * Each is a coefficient, so the circuit's own `y` or `digest` detects the
 * divergence. The cases fail if any of these fields becomes challenge-only,
 * where nothing would detect it.
 */
export interface DivergenceCase {
    /** The per-leaf field, as named in the circom and in the vector. */
    field: string;
    /** Rewrite the calldata view; the witness stays honest and satisfiable. */
    diverge: (c: TreeUpdateBatchPublicArgs) => void;
}

export const DIVERGENCE_CASES: readonly DivergenceCase[] = [
    { field: "leaf_asset",     diverge: c => { c.leafAsset[0] = 42n; } },
    { field: "leaf_public_in", diverge: c => { c.leafPublicIn[0] = 1n; } },
    { field: "is_deposit",     diverge: c => { c.isDeposit[0] = 0; } },
    { field: "cms",            diverge: c => { c.cms[0] = c.cms[0] + 1n; } },
];
