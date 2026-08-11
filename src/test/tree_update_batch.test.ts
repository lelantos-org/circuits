// Tests for `tree_update_batch.circom`. Covers:
//   - per-leaf format leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y)
//   - per-leaf deposit binding cv_dep = leaf_public_in · V^leaf_asset + rcv · H
//   - C-1 regression: cross-asset / value-inflation rejection
//   - odd leaf counts (1, 3, 15) and leaf-granular multiplexing
//   - Padding zero constraints
//
// MAX_L = 8 leaves max, counted individually: actual_count is a LEAF count,
// so a batch may commit an odd number of leaves. Tests stay at small
// actual_count for runtime; larger cases verify multiplex logic.

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
} from "./helpers";
import { loadCircuit, srcPath } from "./lib/circuit";
import { treeUpdateBatchInputJson, treeUpdateBatchCoeffs, padToSlots } from "./lib/inputs";
import { expectWitnessFails } from "./lib/expect";
import { expect } from "chai";

const DEPTH = 10;
const MAX_L = 8;
const WRAPPER = srcPath("tree_update_batch.circom");

interface LeafWitness {
    cm: Field;
    cvDep: Point;
    leafAsset: Field;
    leafPublicIn: Field;
    isDeposit: 0 | 1;
    rcv: Field;
}

function buildLeafWitness(opts: {
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

/// Compact leaf-witness factory for tests that don't care about specific
/// blinder / pk values. Caller supplies the discriminating fields only.
function simpleLeaf(opts: {
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

/// Re-derive Fiat-Shamir (z, y) after tampering any PolyEval-bound field.
/// Use after mutating oldRoot / newRoot / cms / etc. on `w`.
function rebindFiatShamir(w: ReturnType<typeof buildHonest>) {
    const coeffs = treeUpdateBatchCoeffs({
        oldRoot: w.oldRoot, newRoot: w.newRoot,
        startIndex: w.startIndex, actualCount: w.actualCount,
        cms: w.cms, cvDep: w.cvDep,
        leafAsset: w.leafAsset, leafPublicIn: w.leafPublicIn,
        isDeposit: w.isDeposit,
    });
    w.z = fiatShamirZ(coeffs);
    w.y = hornerEval(coeffs, w.z);
}

/// Generate the witness, check every constraint, and — crucially — assert the
/// circuit's `y` output equals the reference Horner evaluation over the
/// coefficient vector. `z` alone does not pin the layout: a permuted
/// `BatchCompress` would simply produce a different, still-satisfiable
/// challenge. `y` is what binds the slot order to `lib/inputs.ts` (and through
/// it to PubInputs.sol :: compress(TreeUpdateBatch)).
async function expectHonest(circuit: any, w: ReturnType<typeof buildHonest>) {
    const witness = await circuit.calculateWitness(treeUpdateBatchInputJson(w), true);
    await circuit.checkConstraints(witness);
    // witness[0] is the constant 1; witness[1] is the first (only) output, y.
    expect(witness[1].toString()).to.equal(w.y.toString(), "circuit y must match reference PolyEval");
    return witness;
}

function buildHonest(P: Poseidon, J: Jubjub, prefilled: number, leaves: LeafWitness[]) {
    const tree = new MerkleTree(P, DEPTH);
    for (let i = 0; i < prefilled; i++) tree.insert(BigInt(0xdead + i));
    const oldRoot = tree.root();
    const frontier = tree.frontier();

    for (const l of leaves) {
        tree.insert(buildLeaf(P, l.cm, l.cvDep));
    }
    const newRoot = tree.root();

    const startIndex = prefilled;
    const actualCount = leaves.length;

    const cmsPadded = padToSlots(leaves.map(l => l.cm), MAX_L, 0n);
    const cvDepPadded = padToSlots(leaves.map(l => l.cvDep), MAX_L, [0n, 0n] as Point);
    const leafAssetPadded = padToSlots(leaves.map(l => l.leafAsset), MAX_L, 0n);
    const leafPublicInPadded = padToSlots(leaves.map(l => l.leafPublicIn), MAX_L, 0n);
    const isDepositPadded = padToSlots(leaves.map(l => l.isDeposit as number), MAX_L, 0);
    const rcvPadded = padToSlots(leaves.map(l => l.rcv), MAX_L, 0n);

    const coeffs = treeUpdateBatchCoeffs({
        oldRoot,
        newRoot,
        startIndex,
        actualCount,
        cms: cmsPadded,
        cvDep: cvDepPadded,
        leafAsset: leafAssetPadded,
        leafPublicIn: leafPublicInPadded,
        isDeposit: isDepositPadded,
    });
    const z = fiatShamirZ(coeffs);
    const y = hornerEval(coeffs, z);

    return {
        oldRoot,
        newRoot,
        startIndex,
        actualCount,
        cms: cmsPadded,
        cvDep: cvDepPadded,
        leafAsset: leafAssetPadded,
        leafPublicIn: leafPublicInPadded,
        isDeposit: isDepositPadded,
        rcv: rcvPadded,
        frontier,
        z,
        y,
    };
}

describe("tree_update_batch", function () {
    this.timeout(900000);

    let circuit: any;
    let P: Poseidon;
    let J: Jubjub;

    before(async () => {
        P = await Poseidon.build();
        J = await Jubjub.build();
        circuit = await loadCircuit(WRAPPER);
    });

    it("honest deposit: 1 active leaf, isDeposit=1, binding verifies", async () => {
        const leaf = buildLeafWitness({
            J,
            P,
            asset: 7n,
            val: 1000n,
            pk: 0xabcn,
            rho: 1n,
            rcm: 3n,
            rcvDep: 5n,
            isDeposit: 1,
        });
        const w = buildHonest(P, J, 0, [leaf]);
        await expectHonest(circuit, w);
    });

    it("honest spend: 2 active leaves, isDeposit=0, binding skipped", async () => {
        const leaves = [
            buildLeafWitness({ J, P, asset: 7n, val: 100n, pk: 0xdadn, rho: 11n, rcm: 33n, rcvDep: 55n, isDeposit: 0 }),
            buildLeafWitness({ J, P, asset: 7n, val: 50n, pk: 0xdadn, rho: 22n, rcm: 44n, rcvDep: 66n, isDeposit: 0 }),
        ];
        const w = buildHonest(P, J, 0, leaves);
        await expectHonest(circuit, w);
    });

    it("C-1 regression: deposit with mismatched binding (wrong asset) is rejected", async () => {
        // Attacker pays with asset=7 (publicIn=1) but cv_dep commits to a
        // different asset's value. The per-leaf Pedersen binding catches this
        // since V^7 and V^99 are independent generators.
        const honest = simpleLeaf({ J, P, val: 1n, isDeposit: 1, asset: 7n });
        const fakeAssetGen = J.hashToAssetGen(99n);
        const tampered: LeafWitness = {
            ...honest,
            cvDep: J.valueCommit(1_000_000n, fakeAssetGen, honest.rcv),
        };
        const w = buildHonest(P, J, 0, [tampered]);
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    // ===== Frontier-binding regression coverage (H-1 fix) =====
    //
    // FrontierRoot rebinds `frontier_in` to public `old_root` so a malicious
    // relayer cannot pair a real `oldRoot` with a forged frontier. Without
    // this binding any batch corrupts the on-chain root ⇒ permanent DoS.

    it("frontier binding: honest non-zero start_index passes", async () => {
        // start_index = 5 ⇒ digits [1,1,0,...]. Exercises pre/eq branches
        // at low levels.
        const w = buildHonest(P, J, 5, [simpleLeaf({ J, P, val: 42n, isDeposit: 1 })]);
        await expectHonest(circuit, w);
    });

    it("frontier binding: large prefill (start_index=21) honest passes", async () => {
        // 21 = 0b010101 ⇒ digits [1,1,1,0,...]. Non-trivial frontier at
        // the three lowest levels.
        const w = buildHonest(P, J, 21, [simpleLeaf({ J, P, val: 9n, isDeposit: 1 })]);
        await expectHonest(circuit, w);
    });

    it("frontier binding: corrupted frontier entry rejected", async () => {
        // Honest oldRoot + cms but tampered frontier ⇒ FrontierRoot rebuild
        // diverges from old_root ⇒ `old_root === frontier_root.root` fails.
        const w = buildHonest(P, J, 8, [simpleLeaf({ J, P, val: 1000n, isDeposit: 1 })]);
        w.frontier[1][1] = w.frontier[1][1] + 1n;
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    it("frontier binding: empty-tree frontier with wrong oldRoot rejected", async () => {
        // Frontier honest (all-zeros for empty tree) but oldRoot lied about.
        // FrontierRoot rebuilds the genuine empty-tree root; equality check
        // catches the mismatch.
        const w = buildHonest(P, J, 0, [simpleLeaf({ J, P, val: 1n, isDeposit: 1 })]);
        w.oldRoot = w.oldRoot + 1n;
        rebindFiatShamir(w);
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    // ===== Multi-leaf / odd-count / capacity coverage (B) =====
    //
    // actual_count is a leaf count, so odd batches are first-class. These
    // exercise the multiplexed frontier / root threading up to MAX_L = 16.

    it("honest 2-leaf deposit batch passes", async () => {
        const leaves = [
            simpleLeaf({ J, P, val: 33n, isDeposit: 1, asset: 7n, pk: 0xaa1n }),
            simpleLeaf({ J, P, val: 77n, isDeposit: 1, asset: 7n, pk: 0xaa2n }),
        ];
        const w = buildHonest(P, J, 0, leaves);
        await expectHonest(circuit, w);
    });

    it("honest odd batch: 3 leaves (3x3 transact output shape) passes", async () => {
        // A 3-output transact bundle emits three commitments, so the batch must
        // accept an odd leaf count.
        const leaves = [
            simpleLeaf({ J, P, val: 11n, isDeposit: 0, pk: 0xb01n }),
            simpleLeaf({ J, P, val: 22n, isDeposit: 0, pk: 0xb02n }),
            simpleLeaf({ J, P, val: 33n, isDeposit: 0, pk: 0xb03n }),
        ];
        const w = buildHonest(P, J, 0, leaves);
        await expectHonest(circuit, w);
    });

    it("honest odd batch: 7 leaves passes", async () => {
        const leaves: LeafWitness[] = [];
        for (let i = 0; i < 7; i++) {
            leaves.push(simpleLeaf({ J, P, val: BigInt(300 + i), isDeposit: 1, pk: BigInt(0xbe00 + i) }));
        }
        const w = buildHonest(P, J, 0, leaves);
        await expectHonest(circuit, w);
    });

    it("honest full-batch (actual_count = MAX_L = 8) passes", async () => {
        const leaves: LeafWitness[] = [];
        for (let i = 0; i < MAX_L; i++) {
            leaves.push(simpleLeaf({ J, P, val: BigInt(300 + 2 * i), isDeposit: 1, pk: BigInt(0xbf00 + i) }));
        }
        const w = buildHonest(P, J, 0, leaves);
        await expectHonest(circuit, w);
    });

    it("mixed deposit + spend leaves in same batch passes", async () => {
        const leaves = [
            simpleLeaf({ J, P, val: 50n, isDeposit: 1, pk: 0xc01n }),
            simpleLeaf({ J, P, val: 7n, isDeposit: 0, pk: 0xc02n }),
            simpleLeaf({ J, P, val: 100n, isDeposit: 1, pk: 0xc03n }),
        ];
        const w = buildHonest(P, J, 0, leaves);
        await expectHonest(circuit, w);
    });

    it("honest odd batch at non-zero start_index passes", async () => {
        // Exercises FrontierRoot + insert chain at start_index = 13
        // (digits [1, 3, 0, ...]); inserts land at indices 13..15, crossing
        // a level-1 carry.
        const leaves = [
            simpleLeaf({ J, P, val: 3n, isDeposit: 1, pk: 0xd01n }),
            simpleLeaf({ J, P, val: 7n, isDeposit: 1, pk: 0xd02n }),
            simpleLeaf({ J, P, val: 9n, isDeposit: 1, pk: 0xd03n }),
        ];
        const w = buildHonest(P, J, 13, leaves);
        await expectHonest(circuit, w);
    });

    // ===== Padding hole coverage (C) =====
    //
    // Section 3 of tree_update_batch.circom asserts (1 - active[k]) * X === 0
    // for every per-leaf field. Each entry below tampers ONE inactive-slot
    // field and expects rejection. With actual_count = 1, slot 1 is inactive.

    it("padding: non-zero cv_dep_x in inactive slot is rejected", async () => {
        const w = buildHonest(P, J, 0, [simpleLeaf({ J, P, val: 9n, isDeposit: 1 })]);
        w.cvDep[1] = [1n, w.cvDep[1][1]];
        rebindFiatShamir(w);
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    it("padding: non-zero cv_dep_y in inactive slot is rejected", async () => {
        const w = buildHonest(P, J, 0, [simpleLeaf({ J, P, val: 9n, isDeposit: 1 })]);
        w.cvDep[2] = [w.cvDep[2][0], 1n];
        rebindFiatShamir(w);
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    it("padding: non-zero leaf_asset in inactive slot is rejected", async () => {
        const w = buildHonest(P, J, 0, [simpleLeaf({ J, P, val: 9n, isDeposit: 1 })]);
        w.leafAsset[1] = 42n;
        rebindFiatShamir(w);
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    it("padding: non-zero leaf_public_in in inactive slot is rejected", async () => {
        const w = buildHonest(P, J, 0, [simpleLeaf({ J, P, val: 9n, isDeposit: 1 })]);
        w.leafPublicIn[1] = 99n;
        rebindFiatShamir(w);
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    it("padding: non-zero is_deposit in inactive slot is rejected", async () => {
        const w = buildHonest(P, J, 0, [simpleLeaf({ J, P, val: 9n, isDeposit: 1 })]);
        w.isDeposit[1] = 1;
        rebindFiatShamir(w);
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    it("padding: non-zero rcv in inactive slot is rejected", async () => {
        const w = buildHonest(P, J, 0, [simpleLeaf({ J, P, val: 9n, isDeposit: 1 })]);
        w.rcv[1] = 7n;
        // rcv is not in PolyEval ⇒ Fiat-Shamir unchanged.
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    it("padding: non-zero cm in inactive slot is rejected", async () => {
        const w = buildHonest(P, J, 0, [simpleLeaf({ J, P, val: 50n, pk: 0xfn, isDeposit: 1 })]);
        w.cms[1] = 0xbadcafen;
        rebindFiatShamir(w);
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    // ===== Other negative coverage (D) =====

    it("FAILS when actual_count == 0 (Num2Bits(COUNT_BITS) rejects -1)", async () => {
        // Circuit decomposes (actual_count - 1) in COUNT_BITS=3 bits ⇒
        // actual_count=0 yields -1, a 254-bit field element that Num2Bits
        // cannot fit.
        const w = buildHonest(P, J, 0, [simpleLeaf({ J, P, val: 1n, isDeposit: 1 })]);
        w.actualCount = 0;
        // Zero out the would-be-active slot fields so only the count check fires.
        w.cms[0] = 0n;
        w.cvDep[0] = [0n, 0n];
        w.leafAsset[0] = 0n; w.leafPublicIn[0] = 0n;
        w.isDeposit[0] = 0; w.rcv[0] = 0n;
        rebindFiatShamir(w);
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    it("FAILS when actual_count > MAX_L (Num2Bits(COUNT_BITS) rejects 8)", async () => {
        // COUNT_BITS=3 bounds (actual_count - 1) ∈ [0, 7] ⇒ actual_count ≤ 8.
        // Setting actual_count = 9 ⇒ (9-1)=8 ⇒ Num2Bits(3) fails.
        const w = buildHonest(P, J, 0, [simpleLeaf({ J, P, val: 1n, isDeposit: 1 })]);
        w.actualCount = 9;
        rebindFiatShamir(w);
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    it("FAILS when is_deposit is non-boolean (=2)", async () => {
        const w = buildHonest(P, J, 0, [simpleLeaf({ J, P, val: 1n, isDeposit: 1 })]);
        w.isDeposit[0] = 2;
        rebindFiatShamir(w);
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    it("FAILS when leaf_public_in exceeds 2^64 (RangeCheck64)", async () => {
        // Build an honest witness then override leaf_public_in past 2^64;
        // the deposit-side RangeCheck64 fails.
        const w = buildHonest(P, J, 0, [simpleLeaf({ J, P, val: 1n, isDeposit: 1 })]);
        w.leafPublicIn[0] = 1n << 64n;
        rebindFiatShamir(w);
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    it("FAILS on C-1' value inflation: same asset, wrong claimed value", async () => {
        // Honest path: cv_dep = leaf_public_in · V^asset + rcv · H.
        // Tamper: inflate the claim while keeping cv_dep real ⇒ equality fails.
        const w = buildHonest(P, J, 0, [simpleLeaf({ J, P, val: 150n, isDeposit: 1 })]);
        w.leafPublicIn[0] = 200n;
        rebindFiatShamir(w);
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    it("FAILS on C-1'' split: value moved between two deposit leaves", async () => {
        // A binding over an aggregate of leaves would fix only Σvalue mod the
        // subgroup order, letting an attacker claim public_in = 1 while loading
        // leaf 0 with 2^63 and leaving leaf 1 to absorb the negative remainder.
        // Per-leaf binding makes the split unexpressible:
        // leaf 0's own equality already fails.
        const asset = 7n;
        const assetGen = J.hashToAssetGen(asset);
        const honest = simpleLeaf({ J, P, val: 1n, isDeposit: 1, asset });
        const tampered: LeafWitness = {
            ...honest,
            cvDep: J.valueCommit(1n << 63n, assetGen, honest.rcv),
        };
        const w = buildHonest(P, J, 0, [tampered]);
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    it("FAILS when rcv is tampered (deposit binding)", async () => {
        // Honest: cv_dep = leaf_public_in·V + rcv·H. Tamper rcv ⇒ rhs shifts
        // by Δ·H ≠ 0 ⇒ point equality fails. rcv is NOT in PolyEval so
        // Fiat-Shamir is unchanged.
        const w = buildHonest(P, J, 0, [simpleLeaf({ J, P, val: 150n, isDeposit: 1 })]);
        w.rcv[0] = w.rcv[0] + 1n;
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });

    it("FAILS when a deposit leaf's value disagrees with its claimed public_in", async () => {
        // Splitting a deposit across leaves is not expressible: each deposit
        // leaf declares its own public_in and must open to exactly that.
        const honest = simpleLeaf({ J, P, val: 100n, isDeposit: 1 });
        const tampered: LeafWitness = { ...honest, leafPublicIn: 50n };
        const w = buildHonest(P, J, 0, [tampered]);
        await expectWitnessFails(circuit, treeUpdateBatchInputJson(w));
    });
});
