// TreeUpdateBatch witness builders, shared by the spec and fuzz suites.

import {
    Poseidon,
    Jubjub,
    MerkleTree,
    buildLeaf,
    buildNoteCommitment,
    fiatShamirZ,
    hornerEval,
    type Field,
    type Point,
} from "../helpers";
import {
    treeUpdateBatchChallenge,
    treeUpdateBatchCoeffs,
    padToSlots,
    type TreeUpdateBatchArgs,
    type TreeUpdateBatchPublicArgs,
} from "./inputs";
import { BATCH_DEPTH, MAX_L } from "./constants";

/** One leaf's contribution to a batch: the commitment plus its deposit anchor. */
export interface LeafWitness {
    cm: Field;
    cvDep: Point;
    leafAsset: Field;
    leafPublicIn: Field;
    isDeposit: 0 | 1;
    rcv: Field;
}

/** A full batch witness: the circuit inputs plus the reference `y` to check against. */
export interface BatchWitness extends TreeUpdateBatchArgs {
    startIndex: number;
    actualCount: number;
    isDeposit: number[];
    y: Field;
}

export function buildLeafWitness(opts: {
    J: Jubjub;
    P: Poseidon;
    asset: Field;
    val: Field;
    pk: Field;
    rho: Field;
    rcm: Field;
    rcvDep: Field;
    isDeposit: 0 | 1;
}): LeafWitness {
    const { J, P, asset, val, pk, rho, rcm, rcvDep, isDeposit } = opts;
    const cm = buildNoteCommitment(P, { asset, value: val, pk, rho, rcm });
    const assetGen = J.hashToAssetGen(asset);
    const cvDep = J.valueCommit(val, assetGen, rcvDep);
    // A deposit leaf is pinned directly: cv_dep = val·V^asset + rcv·H, so the
    // claimed public_in must be exactly this leaf's value.
    return {
        cm,
        cvDep,
        leafAsset: isDeposit === 1 ? asset : 0n,
        leafPublicIn: isDeposit === 1 ? val : 0n,
        isDeposit,
        rcv: rcvDep,
    };
}

/** Leaf-witness factory taking only the discriminating fields; the rest are fixed. */
export function simpleLeaf(opts: {
    J: Jubjub;
    P: Poseidon;
    val: Field;
    isDeposit: 0 | 1;
    asset?: Field;
    pk?: Field;
}): LeafWitness {
    return buildLeafWitness({
        J: opts.J,
        P: opts.P,
        asset: opts.asset ?? 7n,
        val: opts.val,
        pk: opts.pk ?? 0xabcn,
        rho: 1n, rcm: 3n, rcvDep: 5n,
        isDeposit: opts.isDeposit,
    });
}

/**
 * A leaf derived entirely from `seed`, for property tests needing k distinct
 * leaves. `val` and `asset` override the seeded ones where a shape needs
 * specific values; a zero-value fee note needs both at zero (step 6a).
 */
export function seededLeaf(
    P: Poseidon,
    J: Jubjub,
    seed: number,
    isDeposit: 0 | 1,
    val?: Field,
    asset?: Field,
): LeafWitness {
    return buildLeafWitness({
        P, J,
        asset: asset ?? 7n,
        val: val ?? BigInt(100 + seed),
        pk: BigInt(0xb000 + seed),
        rho: BigInt(1 + 2 * seed),
        rcm: BigInt(3 + 2 * seed),
        rcvDep: BigInt(11 + 7 * seed),
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

    for (const l of leaves) tree.insert(buildLeaf(P, l.cm, l.cvDep));
    const newRoot = tree.root();

    const w: BatchWitness = {
        oldRoot,
        newRoot,
        startIndex: prefilled,
        actualCount: leaves.length,
        cms: padToSlots(leaves.map(l => l.cm), MAX_L, 0n),
        cvDep: padToSlots(leaves.map(l => l.cvDep), MAX_L, [0n, 0n] as Point),
        leafAsset: padToSlots(leaves.map(l => l.leafAsset), MAX_L, 0n),
        leafPublicIn: padToSlots(leaves.map(l => l.leafPublicIn), MAX_L, 0n),
        isDeposit: padToSlots(leaves.map(l => l.isDeposit as number), MAX_L, 0),
        rcv: padToSlots(leaves.map(l => l.rcv), MAX_L, 0n),
        frontier,
        z: 0n,
        y: 0n,
    };
    rebindFiatShamir(w);
    return w;
}

/**
 * Re-derive Fiat-Shamir `(z, y)` from the witness in its current state.
 *
 * Call after mutating any PolyEval-bound field, so the failure comes from the
 * constraint under test rather than a stale challenge. `rcv` and `frontier` are
 * outside the coefficient vector and do not require it.
 *
 * Implemented as `bindFiatShamir` applied to the calldata view that matches the
 * witness, so the derivation has a single definition.
 */
export function rebindFiatShamir(w: BatchWitness): void {
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
 * `BatchWitness` extends the public args with `rcv`, `frontier`, `z` and `y`;
 * carrying them along is harmless, since the challenge and coefficient functions
 * read only the public fields.
 */
export function calldataView(w: BatchWitness): TreeUpdateBatchPublicArgs {
    return structuredClone(w);
}

/**
 * Bind `(z, y)` to a calldata view that may differ from the witness `w`.
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
}

/**
 * `count` leaves in the layout MASP's deposit path emits: slot 2i is a
 * principal and slot 2i+1 its fee note. The circuit does not require this
 * (step 6a is per-slot), but it is the shape a flush produces.
 *
 * Fee notes carry zero value, the fbps = 0 flush: a permitted shape
 * (`_validateDeposit`: "The fee note's value may be zero") and the one where the
 * deposit binding degenerates and leaves 64-bit `leaf_asset` values otherwise
 * unpinned.
 *
 * Fee notes are at asset 0 as well as value 0, as step 6a requires of a leaf
 * the binding does not constrain.
 */
export function depositPairs(P: Poseidon, J: Jubjub, count: number): LeafWitness[] {
    return Array.from({ length: count }, (_, i) =>
        i % 2 === 0
            ? seededLeaf(P, J, i, 1)
            : seededLeaf(P, J, i, 1, 0n, 0n));
}

// ===== divergent-witness coverage =====

/**
 * One field a batch's calldata can declare differently from the witness proved
 * against it.
 *
 * Each is a coefficient, so the circuit's own `y` detects the divergence. The
 * cases fail if any of these fields becomes challenge-only, where nothing would
 * detect it.
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
    { field: "cm",             diverge: c => { c.cms[0] = c.cms[0] + 1n; } },
    { field: "cv_dep_x",       diverge: c => { c.cvDep[0] = [c.cvDep[0][0] + 1n, c.cvDep[0][1]]; } },
];
