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
 * specific values — a worthless fee note needs both at zero (step 7a).
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
 * Throwaway value for every pre-batch leaf.
 *
 * A single constant rather than a distinct leaf per slot, so `fillConstant`
 * builds the prefill in O(depth) hashes instead of one per leaf; a
 * production-depth prefill is otherwise too slow for the fuzz suites.
 *
 * All filled frontier slots at one level are equal under this fill, so an
 * intra-level permutation of the frontier is invisible to a witness built from
 * this tree. `frontier_root.test.ts` covers permutation at depth 3 over a
 * distinct-leaf tree.
 */
const PREFILL_LEAF: Field = 0xdeadn;

/**
 * An honest batch: `prefilled` throwaway leaves already in the tree, then
 * `leaves` inserted on top, with the frontier taken at the old root and the
 * Fiat-Shamir pair derived over the resulting coefficients.
 */
export function buildHonest(
    P: Poseidon,
    prefilled: number,
    leaves: LeafWitness[],
): BatchWitness {
    const tree = new MerkleTree(P, BATCH_DEPTH);
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
 *
 * Defined in terms of `bindFiatShamir` rather than beside it: this is that
 * function at the one calldata view that cannot disagree with the witness. Two
 * copies of the derivation would need a test that they still agree.
 */
export function rebindFiatShamir(w: BatchWitness): void {
    bindFiatShamir(w, calldataView(w));
}

/**
 * Snapshot a witness's logical public inputs — the calldata view.
 *
 * A structural clone, not a field-by-field copy. The copy must be DEEP or the
 * two views share arrays, a divergence case mutates both, and
 * `expectNotForgeable` compares a view against itself and passes vacuously — so
 * the one property this function must have is the one a hand-written projection
 * silently loses when a field is added to `TreeUpdateBatchPublicArgs`.
 *
 * `BatchWitness` extends the public args with `rcv`, `frontier`, `z` and `y`;
 * carrying them along is harmless, since the challenge and coefficient functions
 * read only the public fields.
 */
export function calldataView(w: BatchWitness): TreeUpdateBatchPublicArgs {
    return structuredClone(w);
}

/**
 * Bind `(z, y)` to a CALLDATA view that may differ from the witness `w`.
 *
 * `rebindFiatShamir` fuses two roles a real deployment keeps apart: deriving the
 * challenge, and choosing the witness. The contract derives `z` and `y` from
 * calldata; the prover then picks any witness satisfying the R1CS at that `z`.
 * Nothing in Groth16 forces the two to describe the same batch. Fusing them
 * makes the divergence unrepresentable, so a signal that is hashed into `z` but
 * pinned by no constraint reads as bound when it is free.
 *
 * Use this wherever the question is "can the prover lie to the contract", and
 * `rebindFiatShamir` where it is "does constraint X fire".
 */
export function bindFiatShamir(w: BatchWitness, calldata: TreeUpdateBatchPublicArgs): void {
    w.z = fiatShamirZ(treeUpdateBatchChallenge(calldata));
    w.y = hornerEval(treeUpdateBatchCoeffs(calldata), w.z);
}

/**
 * `count` leaves in the layout MASP's deposit path emits: slot 2i is a
 * principal and slot 2i+1 its fee note. The circuit does not require this —
 * step 7a is per-slot — but it is the shape a flush actually produces.
 *
 * Fee notes carry zero: that is the fbps = 0 flush, both the permitted shape
 * (`_validateDeposit`: "The fee note's value may be zero") and the one that used
 * to supply the free 64-bit dials, so it is the shape worth generating.
 *
 * Fee notes are at asset 0 as well as value 0, which is what step 7a requires
 * of a leaf the binding cannot see.
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
 * Every one is a coefficient today, so the circuit's own `y` is what catches
 * the divergence. They are kept as tests rather than deleted because three of
 * these fields were once challenge-only, where nothing caught it: the cases
 * fail the moment a demotion reintroduces that state.
 */
export interface DivergenceCase {
    /** The per-leaf field, as it reads in the circom and in the vector. */
    field: string;
    /** Rewrite the CALLDATA view; the witness is left honest and satisfiable. */
    diverge: (c: TreeUpdateBatchPublicArgs) => void;
}

export const DIVERGENCE_CASES: readonly DivergenceCase[] = [
    { field: "leaf_asset",     diverge: c => { c.leafAsset[0] = 42n; } },
    { field: "leaf_public_in", diverge: c => { c.leafPublicIn[0] = 1n; } },
    { field: "is_deposit",     diverge: c => { c.isDeposit[0] = 0; } },
    { field: "cm",             diverge: c => { c.cms[0] = c.cms[0] + 1n; } },
    { field: "cv_dep_x",       diverge: c => { c.cvDep[0] = [c.cvDep[0][0] + 1n, c.cvDep[0][1]]; } },
];
