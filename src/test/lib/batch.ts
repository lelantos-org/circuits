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
import { treeUpdateBatchCoeffs, padToSlots, type TreeUpdateBatchArgs } from "./inputs";
import { DEPTH, MAX_L } from "./constants";

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

/** A leaf derived entirely from `seed`, for property tests needing k distinct leaves. */
export function seededLeaf(P: Poseidon, J: Jubjub, seed: number, isDeposit: 0 | 1): LeafWitness {
    return buildLeafWitness({
        P, J,
        asset: 7n,
        val: BigInt(100 + seed),
        pk: BigInt(0xb000 + seed),
        rho: BigInt(1 + 2 * seed),
        rcm: BigInt(3 + 2 * seed),
        rcvDep: BigInt(11 + 7 * seed),
        isDeposit,
    });
}

/**
 * Throwaway value for every pre-batch leaf.
 *
 * One constant rather than a distinct leaf per slot, so `fillConstant` can build
 * the prefill in O(depth) hashes. A distinct fill costs ~350k Poseidon calls at
 * depth 10 (~40s), which the frontier fuzz suite pays once per trial over
 * `start_index` values near 4^10 — that is what pushed it past its 900s mocha
 * timeout at FUZZ=heavy.
 *
 * The trade-off: all filled frontier slots at one level come out equal here, so
 * an intra-level permutation of the frontier is invisible to a witness built
 * from this tree. `frontier_root.test.ts` covers permutation at depth 3 over a
 * distinct-leaf tree, where the full fill is cheap.
 */
const PREFILL_LEAF: Field = 0xdeadn;

/**
 * An honest batch: `prefilled` throwaway leaves already in the tree, then
 * `leaves` inserted on top, with the frontier taken at the old root and the
 * Fiat-Shamir pair derived over the resulting coefficients.
 */
export function buildHonest(
    P: Poseidon,
    J: Jubjub,
    prefilled: number,
    leaves: LeafWitness[],
): BatchWitness {
    const tree = new MerkleTree(P, DEPTH);
    tree.fillConstant(prefilled, PREFILL_LEAF);
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
 */
export function rebindFiatShamir(w: BatchWitness): void {
    const coeffs = treeUpdateBatchCoeffs(w);
    w.z = fiatShamirZ(coeffs);
    w.y = hornerEval(coeffs, w.z);
}
