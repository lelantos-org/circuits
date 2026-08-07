// Tests for `tree_update_batch.circom`. Covers:
//   - per-pair leaf format leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y)
//   - per-pair Pedersen aggregate (deposit mode) cv_dep_0 + cv_dep_1
//                                = pair_public_in · V^pair_asset + rcv_total · H
//   - per-leaf pad binding cv_dep_1 == rcv_dep_pad · H (C-1'' closure)
//   - C-1 regression: cross-asset / value-inflation rejection
//   - Padding zero constraints
//
// MAX_N = 8 ⇒ 16 leaves max (halved from prior 16). Tests stay at small
// actual_count for runtime; one larger case verifies multiplex logic.

import { expect } from "chai";
import { Poseidon, Jubjub, MerkleTree, BABYJUB_SUBGROUP_ORDER, type Field, type Point } from "./helpers";
import { fiatShamirZ, hornerEval } from "@lelantos-org/sdk";
import { loadCircuit, srcPath } from "./lib/circuit";
import { treeUpdateBatchInputJson, flattenTreeUpdateBatch } from "./lib/inputs";
import { expectWitnessFails } from "./lib/expect";

const DEPTH = 10;
const MAX_N = 8;
const SLOTS = 2 * MAX_N;
const TAG_LEAF = 10n;
const WRAPPER = srcPath("tree_update_batch.circom");

interface PairWitness {
    cm0: Field;
    cm1: Field;
    cvDep0: Point;
    cvDep1: Point;
    pairAsset: Field;
    pairPublicIn: Field;
    isDeposit: 0 | 1;
    rcvTotal: Field;
    rcvDepPad: Field;
}

function padToSlots<T>(real: T[], total: number, zero: T): T[] {
    const out = real.slice();
    while (out.length < total) out.push(zero);
    return out;
}

function buildPairWitness(opts: {
    J: Jubjub;
    asset: Field;
    val0: Field;
    val1: Field;
    pk: Field;
    rho0: Field;
    rho1: Field;
    rcm0: Field;
    rcm1: Field;
    rcvDep0: Field;
    rcvDep1: Field;
    P: Poseidon;
    isDeposit: 0 | 1;
}): PairWitness {
    const { J, P, asset, val0, val1, pk, rho0, rho1, rcm0, rcm1, rcvDep0, rcvDep1, isDeposit } = opts;
    const cm0 = P.hash([asset * (1n << 64n) + val0, pk, rho0, rcm0]);
    const cm1 = P.hash([asset * (1n << 64n) + val1, pk, rho1, rcm1]);
    const assetGen = J.hashToAssetGen(asset);
    const cvDep0 = J.valueCommit(val0, assetGen, rcvDep0);
    const cvDep1 = J.valueCommit(val1, assetGen, rcvDep1);
    const pairPublicIn = isDeposit === 1 ? val0 + val1 : 0n;
    const pairAsset = isDeposit === 1 ? asset : 0n;
    const rcvTotal = isDeposit === 1 ? rcvDep0 + rcvDep1 : 0n;
    // Deposit pads (leaf 1) must commit to value 0 so cv_dep0 is pinned to
    // pairPublicIn exactly; the circuit checks cv_dep1 == rcvDepPad·H.
    const rcvDepPad = isDeposit === 1 ? rcvDep1 : 0n;
    return {
        cm0,
        cm1,
        cvDep0,
        cvDep1,
        pairAsset,
        pairPublicIn,
        isDeposit,
        rcvTotal,
        rcvDepPad,
    };
}

function leafOf(P: Poseidon, cm: Field, cvDep: Point): Field {
    return P.hash([TAG_LEAF, cm, cvDep[0], cvDep[1]]);
}

/// Compact pair-witness factory for tests that don't care about specific
/// blinder / pk values. Caller supplies the discriminating fields only.
function simplePair(opts: {
    J: Jubjub;
    P: Poseidon;
    val0: Field;
    val1?: Field;
    isDeposit: 0 | 1;
    asset?: Field;
    pk?: Field;
}): PairWitness {
    return buildPairWitness({
        J: opts.J,
        P: opts.P,
        asset: opts.asset ?? 7n,
        val0: opts.val0,
        val1: opts.val1 ?? 0n,
        pk: opts.pk ?? 0xabcn,
        rho0: 1n, rho1: 2n, rcm0: 3n, rcm1: 4n,
        rcvDep0: 5n, rcvDep1: 6n,
        isDeposit: opts.isDeposit,
    });
}

/// Re-derive Fiat-Shamir (z, y) after tampering any PolyEval-bound field.
/// Use after mutating oldRoot / newRoot / cms / etc. on `w`.
function rebindFiatShamir(w: ReturnType<typeof buildHonest>) {
    const coeffs = flattenTreeUpdateBatch({
        oldRoot: w.oldRoot, newRoot: w.newRoot,
        startIndex: w.startIndex, actualCount: w.actualCount,
        cms: w.cms, cvDep: w.cvDep,
        pairAsset: w.pairAsset, pairPublicIn: w.pairPublicIn,
        isDeposit: w.isDeposit,
    });
    w.z = fiatShamirZ(coeffs);
    w.y = hornerEval(coeffs, w.z);
}

function buildHonest(P: Poseidon, J: Jubjub, prefilled: number, pairs: PairWitness[]) {
    const tree = new MerkleTree(P, DEPTH);
    for (let i = 0; i < prefilled; i++) tree.insert(BigInt(0xdead + i));
    const oldRoot = tree.root();
    const frontier = tree.frontier();

    for (const p of pairs) {
        tree.insert(leafOf(P, p.cm0, p.cvDep0));
        tree.insert(leafOf(P, p.cm1, p.cvDep1));
    }
    const newRoot = tree.root();

    const startIndex = prefilled;
    const actualCount = pairs.length;

    const cms: Field[] = [];
    const cvDep: Point[] = [];
    for (const p of pairs) {
        cms.push(p.cm0);
        cms.push(p.cm1);
        cvDep.push(p.cvDep0);
        cvDep.push(p.cvDep1);
    }
    const cmsPadded = padToSlots(cms, SLOTS, 0n);
    const cvDepPadded = padToSlots(cvDep, SLOTS, [0n, 0n] as Point);
    const pairAssetPadded = padToSlots(pairs.map(p => p.pairAsset), MAX_N, 0n);
    const pairPublicInPadded = padToSlots(pairs.map(p => p.pairPublicIn), MAX_N, 0n);
    const isDepositPadded = padToSlots(pairs.map(p => p.isDeposit as number), MAX_N, 0);
    const rcvTotalPadded = padToSlots(pairs.map(p => p.rcvTotal), MAX_N, 0n);
    const rcvDepPadPadded = padToSlots(pairs.map(p => p.rcvDepPad), MAX_N, 0n);

    const coeffs = flattenTreeUpdateBatch({
        oldRoot,
        newRoot,
        startIndex,
        actualCount,
        cms: cmsPadded,
        cvDep: cvDepPadded,
        pairAsset: pairAssetPadded,
        pairPublicIn: pairPublicInPadded,
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
        pairAsset: pairAssetPadded,
        pairPublicIn: pairPublicInPadded,
        isDeposit: isDepositPadded,
        rcvTotal: rcvTotalPadded,
        rcvDepPad: rcvDepPadPadded,
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

    it("honest deposit: 1 active pair, isDeposit=1, aggregate verifies", async () => {
        const asset = 7n;
        const pair = buildPairWitness({
            J,
            P,
            asset,
            val0: 1000n,
            val1: 0n,
            pk: 0xabcn,
            rho0: 1n,
            rho1: 2n,
            rcm0: 3n,
            rcm1: 4n,
            rcvDep0: 5n,
            rcvDep1: 6n,
            isDeposit: 1,
        });
        const w = buildHonest(P, J, 0, [pair]);
        const witness = await circuit.calculateWitness(treeUpdateBatchInputJson(w), true);
        await circuit.checkConstraints(witness);
    });

    it("honest spend: 1 active pair, isDeposit=0, aggregate skipped", async () => {
        const pair = buildPairWitness({
            J,
            P,
            asset: 7n,
            val0: 100n,
            val1: 50n,
            pk: 0xdadn,
            rho0: 11n,
            rho1: 22n,
            rcm0: 33n,
            rcm1: 44n,
            rcvDep0: 55n,
            rcvDep1: 66n,
            isDeposit: 0,
        });
        const w = buildHonest(P, J, 0, [pair]);
        const witness = await circuit.calculateWitness(treeUpdateBatchInputJson(w), true);
        await circuit.checkConstraints(witness);
    });

    it("C-1 regression: deposit with mismatched aggregate (wrong asset) is rejected", async () => {
        // Attacker pays with asset=7 (publicIn=1) but cv_dep_0 commits to a
        // different asset's value. The circuit's per-pair Pedersen aggregate
        // catches this since V^7 and V^99 are independent generators.
        const honest = buildPairWitness({
            J,
            P,
            asset: 7n,
            val0: 1n,
            val1: 0n,
            pk: 0xeen,
            rho0: 1n,
            rho1: 2n,
            rcm0: 3n,
            rcm1: 4n,
            rcvDep0: 100n,
            rcvDep1: 200n,
            isDeposit: 1,
        });
        const fakeAssetGen = J.hashToAssetGen(99n);
        const fakeCvDep0 = J.valueCommit(1_000_000n, fakeAssetGen, honest.rcvTotal);
        const tampered: PairWitness = {
            ...honest,
            cvDep0: fakeCvDep0,
        };
        const w = buildHonest(P, J, 0, [tampered]);
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    // ===== Frontier-binding regression coverage (H-1 fix) =====
    //
    // FrontierRoot rebinds `frontier_in` to public `old_root` so a malicious
    // relayer cannot pair a real `oldRoot` with a forged frontier. Without
    // this binding any batch corrupts the on-chain root ⇒ permanent DoS.

    it("frontier binding: honest non-zero start_index passes", async () => {
        // start_index = 5 ⇒ digits [1,1,0,...]. Exercises pre/eq branches
        // at low levels.
        const w = buildHonest(P, J, 5, [simplePair({ J, P, val0: 42n, isDeposit: 1 })]);
        const witness = await circuit.calculateWitness(treeUpdateBatchInputJson(w), true);
        await circuit.checkConstraints(witness);
    });

    it("frontier binding: large prefill (start_index=21) honest passes", async () => {
        // 21 = 0b010101 ⇒ digits [1,1,1,0,...]. Non-trivial frontier at
        // the three lowest levels.
        const w = buildHonest(P, J, 21, [simplePair({ J, P, val0: 9n, isDeposit: 1 })]);
        const witness = await circuit.calculateWitness(treeUpdateBatchInputJson(w), true);
        await circuit.checkConstraints(witness);
    });

    it("frontier binding: corrupted frontier entry rejected", async () => {
        // Honest oldRoot + cms but tampered frontier ⇒ FrontierRoot rebuild
        // diverges from old_root ⇒ `old_root === frontier_root.root` fails.
        const w = buildHonest(P, J, 8, [simplePair({ J, P, val0: 1000n, isDeposit: 1 })]);
        w.frontier[1][1] = w.frontier[1][1] + 1n;
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    it("frontier binding: empty-tree frontier with wrong oldRoot rejected", async () => {
        // Frontier honest (all-zeros for empty tree) but oldRoot lied about.
        // FrontierRoot rebuilds the genuine empty-tree root; equality check
        // catches the mismatch.
        const w = buildHonest(P, J, 0, [simplePair({ J, P, val0: 1n, isDeposit: 1 })]);
        w.oldRoot = w.oldRoot + 1n;
        rebindFiatShamir(w);
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    // ===== Multi-pair / capacity coverage (B) =====
    //
    // Prior tests use actual_count = 1; these exercise the multiplexed
    // frontier / root threading through up to MAX_N = 8 pairs.

    it("honest 2-pair deposit batch passes", async () => {
        const pairs = [
            simplePair({ J, P, val0: 33n, val1: 0n, isDeposit: 1, asset: 7n, pk: 0xaa1n }),
            simplePair({ J, P, val0: 77n, val1: 0n, isDeposit: 1, asset: 7n, pk: 0xaa2n }),
        ];
        const w = buildHonest(P, J, 0, pairs);
        const witness = await circuit.calculateWitness(treeUpdateBatchInputJson(w), true);
        await circuit.checkConstraints(witness);
    });

    it("honest full-batch (actual_count = MAX_N = 8) passes", async () => {
        const pairs: PairWitness[] = [];
        for (let i = 0; i < MAX_N; i++) {
            pairs.push(simplePair({ J, P, val0: BigInt(300 + 2 * i), val1: 0n, isDeposit: 1, pk: BigInt(0xbe00 + i) }));
        }
        const w = buildHonest(P, J, 0, pairs);
        const witness = await circuit.calculateWitness(treeUpdateBatchInputJson(w), true);
        await circuit.checkConstraints(witness);
    });

    it("mixed deposit + spend pairs in same batch passes", async () => {
        const pairs = [
            simplePair({ J, P, val0: 50n, isDeposit: 1, pk: 0xc01n }),
            simplePair({ J, P, val0: 7n, val1: 3n, isDeposit: 0, pk: 0xc02n }),
            simplePair({ J, P, val0: 100n, isDeposit: 1, pk: 0xc03n }),
        ];
        const w = buildHonest(P, J, 0, pairs);
        const witness = await circuit.calculateWitness(treeUpdateBatchInputJson(w), true);
        await circuit.checkConstraints(witness);
    });

    it("honest 2-pair batch at non-zero start_index passes", async () => {
        // Exercises FrontierRoot + insert chain at start_index = 13
        // (digits [1, 3, 0, ...]); inserts land at indices 13..16, crossing
        // a level-1 carry.
        const pairs = [
            simplePair({ J, P, val0: 3n, val1: 0n, isDeposit: 1, pk: 0xd01n }),
            simplePair({ J, P, val0: 7n, val1: 0n, isDeposit: 1, pk: 0xd02n }),
        ];
        const w = buildHonest(P, J, 13, pairs);
        const witness = await circuit.calculateWitness(treeUpdateBatchInputJson(w), true);
        await circuit.checkConstraints(witness);
    });

    // ===== Padding hole coverage (C) =====
    //
    // Section 3 of tree_update_batch.circom asserts (1 - active[i]) * X === 0
    // for every per-pair field. Each entry below tampers ONE inactive-slot
    // field and expects rejection.

    it("padding: non-zero cv_dep_x in inactive slot is rejected", async () => {
        const w = buildHonest(P, J, 0, [simplePair({ J, P, val0: 9n, isDeposit: 1 })]);
        w.cvDep[2] = [1n, w.cvDep[2][1]];   // slot 2 is inactive (pair 1)
        rebindFiatShamir(w);
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    it("padding: non-zero cv_dep_y in inactive slot is rejected", async () => {
        const w = buildHonest(P, J, 0, [simplePair({ J, P, val0: 9n, isDeposit: 1 })]);
        w.cvDep[3] = [w.cvDep[3][0], 1n];
        rebindFiatShamir(w);
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    it("padding: non-zero pair_asset in inactive slot is rejected", async () => {
        const w = buildHonest(P, J, 0, [simplePair({ J, P, val0: 9n, isDeposit: 1 })]);
        w.pairAsset[1] = 42n;
        rebindFiatShamir(w);
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    it("padding: non-zero pair_public_in in inactive slot is rejected", async () => {
        const w = buildHonest(P, J, 0, [simplePair({ J, P, val0: 9n, isDeposit: 1 })]);
        w.pairPublicIn[1] = 99n;
        rebindFiatShamir(w);
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    it("padding: non-zero is_deposit in inactive slot is rejected", async () => {
        const w = buildHonest(P, J, 0, [simplePair({ J, P, val0: 9n, isDeposit: 1 })]);
        w.isDeposit[1] = 1;
        rebindFiatShamir(w);
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    it("padding: non-zero rcv_total in inactive slot is rejected", async () => {
        const w = buildHonest(P, J, 0, [simplePair({ J, P, val0: 9n, isDeposit: 1 })]);
        w.rcvTotal[1] = 7n;
        // rcv_total is not in PolyEval ⇒ Fiat-Shamir unchanged.
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    it("padding: non-zero cm in inactive slot is rejected", async () => {
        const w = buildHonest(P, J, 0, [simplePair({ J, P, val0: 50n, pk: 0xfn, isDeposit: 1 })]);
        w.cms[2] = 0xbadcafen;
        rebindFiatShamir(w);
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    // ===== Other negative coverage (D) =====

    it("FAILS when actual_count == 0 (Num2Bits(COUNT_BITS) rejects -1)", async () => {
        // Circuit decomposes (actual_count - 1) in COUNT_BITS=3 bits ⇒
        // actual_count=0 yields -1, a 254-bit field element that Num2Bits
        // cannot fit.
        const w = buildHonest(P, J, 0, [simplePair({ J, P, val0: 1n, isDeposit: 1 })]);
        w.actualCount = 0;
        // Zero out the would-be-active slot fields so only the count check fires.
        w.cms[0] = 0n; w.cms[1] = 0n;
        w.cvDep[0] = [0n, 0n]; w.cvDep[1] = [0n, 0n];
        w.pairAsset[0] = 0n; w.pairPublicIn[0] = 0n;
        w.isDeposit[0] = 0; w.rcvTotal[0] = 0n;
        rebindFiatShamir(w);
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    it("FAILS when actual_count > MAX_N (Num2Bits(COUNT_BITS) rejects 8)", async () => {
        // COUNT_BITS=3 bounds (actual_count - 1) ∈ [0, 7] ⇒ actual_count ≤ 8.
        // Setting actual_count = 9 ⇒ (9-1)=8 ⇒ Num2Bits(3) fails.
        const w = buildHonest(P, J, 0, [simplePair({ J, P, val0: 1n, isDeposit: 1 })]);
        w.actualCount = 9;
        rebindFiatShamir(w);
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    it("FAILS when is_deposit is non-boolean (=2)", async () => {
        const w = buildHonest(P, J, 0, [simplePair({ J, P, val0: 1n, isDeposit: 1 })]);
        w.isDeposit[0] = 2;
        rebindFiatShamir(w);
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    it("FAILS when pair_public_in exceeds 2^64 (RangeCheck64)", async () => {
        // Build an honest witness then override pair_public_in past 2^64;
        // the deposit-side RangeCheck64 fails. Must also rebuild aggregate
        // consistency — easiest: keep cv_dep / rcv_total as-is so the
        // RangeCheck fires before the BabyAdd equality.
        const w = buildHonest(P, J, 0, [simplePair({ J, P, val0: 1n, isDeposit: 1 })]);
        w.pairPublicIn[0] = 1n << 64n;
        rebindFiatShamir(w);
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    it("FAILS on C-1' value-inflation: same asset, wrong value sum", async () => {
        // Honest path: cv_dep_0 + cv_dep_1 = pair_public_in · V^asset + rcv_total · H.
        // Tamper: bump pair_public_in to a smaller-than-real value while
        // keeping cv_deps real ⇒ aggregate equality fails.
        const w = buildHonest(P, J, 0, [simplePair({ J, P, val0: 150n, val1: 0n, isDeposit: 1 })]);
        // Honest pair_public_in == 100+50 = 150. Inflate the claim to 200.
        w.pairPublicIn[0] = 200n;
        rebindFiatShamir(w);
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    it("FAILS on C-1'' per-leaf inflation: pair sum honest, split forged", async () => {
        // The pair aggregate alone fixes only Σvalue mod the subgroup order.
        // Attacker deposits pair_public_in = 1 but loads leaf 0 with 2^63 and
        // lets leaf 1 absorb (1 - 2^63) mod l — an unspendable leaf they
        // abandon — walking away with a valid 2^63 note. The pad-leaf
        // constraint (cv_dep1 == rcv_dep_pad·H) rejects this.
        const asset = 7n;
        const assetGen = J.hashToAssetGen(asset);
        const honest = simplePair({ J, P, val0: 1n, isDeposit: 1, asset });

        const stolen = 1n << 63n;
        const r0 = 5n;
        const r1 = honest.rcvTotal - r0;
        // cv_dep0 opens to 2^63 (in range, spendable); cv_dep1 takes the
        // negative remainder so the pair sum is untouched.
        const fakeCvDep0 = J.valueCommit(stolen, assetGen, r0);
        const fakeCvDep1 = J.valueCommit(
            (BABYJUB_SUBGROUP_ORDER + honest.pairPublicIn - stolen) % BABYJUB_SUBGROUP_ORDER,
            assetGen,
            r1,
        );
        const tampered: PairWitness = { ...honest, cvDep0: fakeCvDep0, cvDep1: fakeCvDep1 };

        // Sanity: the old aggregate-only check is still satisfied by this split,
        // i.e. the pad-leaf constraint is what does the rejecting below.
        const sum = J.addPoint(fakeCvDep0, fakeCvDep1);
        const expected = J.valueCommit(honest.pairPublicIn, assetGen, honest.rcvTotal);
        expect(sum[0]).to.equal(expected[0]);
        expect(sum[1]).to.equal(expected[1]);

        const w = buildHonest(P, J, 0, [tampered]);
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    it("FAILS when a deposit pad leaf carries non-zero value", async () => {
        // Splitting a deposit across both leaves is no longer allowed: leaf 1
        // must be a value-0 commitment so leaf 0 is pinned to pair_public_in.
        const w = buildHonest(P, J, 0, [simplePair({ J, P, val0: 100n, val1: 50n, isDeposit: 1 })]);
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    it("FAILS when rcv_dep_pad is tampered (pad-leaf binding)", async () => {
        // rcv_dep_pad is not in PolyEval ⇒ Fiat-Shamir unchanged.
        const w = buildHonest(P, J, 0, [simplePair({ J, P, val0: 9n, isDeposit: 1 })]);
        w.rcvDepPad[0] = w.rcvDepPad[0] + 1n;
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });

    it("FAILS when rcv_total is tampered (deposit aggregate binding)", async () => {
        // Honest: cv_dep_0 + cv_dep_1 = pair_public_in·V + rcv_total·H.
        // Tamper rcv_total ⇒ rhs shifts by Δ·H ≠ 0 ⇒ point equality fails.
        // rcv_total is NOT in PolyEval so Fiat-Shamir is unchanged.
        const w = buildHonest(P, J, 0, [simplePair({ J, P, val0: 150n, val1: 0n, isDeposit: 1 })]);
        w.rcvTotal[0] = w.rcvTotal[0] + 1n;
        await expectWitnessFails(() => circuit.calculateWitness(treeUpdateBatchInputJson(w), true));
    });
});
