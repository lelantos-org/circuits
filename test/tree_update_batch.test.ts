// Tests for `tree_update_batch.circom`. Covers:
//   - per-leaf format leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y)
//   - per-leaf deposit binding cv_dep = leaf_public_in · V^leaf_asset + rcv · H
//   - cross-asset and value-inflation rejection
//   - odd leaf counts (1, 3) and leaf-granular multiplexing
//   - padding zero constraints
//
// actual_count is a leaf count, so a batch may commit an odd number of leaves.
// Most cases use a small actual_count for runtime; the larger ones cover the
// multiplex logic.
//
// The witness builders live in `lib/batch.ts`, shared with the fuzz suite.

import { expect } from "chai";

import { BN254_FR, Jubjub, Poseidon, quatDigit } from "./helpers";
import { loadCircuit, srcPath, type CircuitTester } from "./lib/circuit";
import {
    treeUpdateBatchChallenge,
    treeUpdateBatchInputJson,
    type TreeUpdateBatchPublicArgs,
} from "./lib/inputs";
import {
    assertViewsDiverge,
    expectNotForgeable,
    expectWitnessFails,
    expectWitnessY,
} from "./lib/expect";
import {
    bindFiatShamir,
    buildHonest,
    buildLeafWitness,
    calldataView,
    depositPairs,
    rebindFiatShamir,
    DIVERGENCE_CASES,
    seededLeaf,
    simpleLeaf,
    type BatchWitness,
    type LeafWitness,
} from "./lib/batch";
import { ARITY, BATCH_DEPTH, MAX_L, TIMEOUT_HEAVY, TWO_64, TWO_252 } from "./lib/constants";
import { buildJubjub } from "./lib/harness";

/** Leaf capacity of the batch circuit's tree: 4^11. */
const CAPACITY = ARITY ** BATCH_DEPTH;

const WRAPPER = srcPath("tree_update_batch.circom");

describe("tree_update_batch", function () {
    this.timeout(TIMEOUT_HEAVY);

    let circuit: CircuitTester;
    let P: Poseidon;
    let J: Jubjub;

    before(async () => {
        P = await Poseidon.build();
        J = await buildJubjub();
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
        const w = buildHonest(P, 0, [leaf]);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("honest spend: 2 active leaves, isDeposit=0, binding skipped", async () => {
        const leaves = [
            buildLeafWitness({ J, P, asset: 7n, val: 100n, pk: 0xdadn, rho: 11n, rcm: 33n, rcvDep: 55n, isDeposit: 0 }),
            buildLeafWitness({ J, P, asset: 7n, val: 50n, pk: 0xdadn, rho: 22n, rcm: 44n, rcvDep: 66n, isDeposit: 0 }),
        ];
        const w = buildHonest(P, 0, leaves);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("C-1 regression: deposit with mismatched binding (wrong asset) is rejected", async () => {
        // The depositor pays with asset=7 (publicIn=1) but cv_dep commits to a
        // different asset's value. The per-leaf Pedersen binding rejects this
        // because V^7 and V^99 are independent generators.
        const honest = simpleLeaf({ J, P, val: 1n, isDeposit: 1, asset: 7n });
        const fakeAssetGen = J.hashToAssetGen(99n);
        const tampered: LeafWitness = {
            ...honest,
            cvDep: J.valueCommit(1_000_000n, fakeAssetGen, honest.rcv),
        };
        const w = buildHonest(P, 0, [tampered]);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "the per-leaf Pedersen binding must reject a cross-asset cv_dep",
        );
    });

    // ===== Frontier binding =====
    //
    // BatchAppend rebuilds `old_root` from `frontier_in`, so a relayer cannot
    // pair a real `oldRoot` with a forged frontier, which would permanently
    // corrupt the on-chain root.

    it("frontier binding: honest non-zero start_index passes", async () => {
        // start_index = 5 ⇒ digits [1,1,0,...]; exercises the pre/eq branches
        // at low levels.
        const w = buildHonest(P, 5, [simpleLeaf({ J, P, val: 42n, isDeposit: 1 })]);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("frontier binding: large prefill (start_index=21) honest passes", async () => {
        // 21 = 0b010101 ⇒ digits [1,1,1,0,...]; non-trivial frontier at the
        // three lowest levels.
        const w = buildHonest(P, 21, [simpleLeaf({ J, P, val: 9n, isDeposit: 1 })]);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("frontier binding: corrupted frontier entry rejected", async () => {
        // Honest oldRoot + cms but tampered frontier ⇒ the old-root rebuild
        // diverges from old_root ⇒ `old_root === append.old_root` fails.
        const w = buildHonest(P, 8, [simpleLeaf({ J, P, val: 1000n, isDeposit: 1 })]);
        // Slot 1 at level 1 is read: 8 has digit 2 there.
        expect(quatDigit(8, 1)).to.be.greaterThan(1);
        w.frontier[1][1] = w.frontier[1][1] + 1n;
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "the old-root rebuild must diverge from old_root under a tampered frontier",
        );
    });

    it("frontier binding: empty-tree frontier with wrong oldRoot rejected", async () => {
        // Honest all-zero frontier with a forged oldRoot. BatchAppend rebuilds
        // the empty-tree root and the equality check rejects the mismatch.
        const w = buildHonest(P, 0, [simpleLeaf({ J, P, val: 1n, isDeposit: 1 })]);
        w.oldRoot = w.oldRoot + 1n;
        rebindFiatShamir(w);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "old_root === append.old_root must reject a forged old_root",
        );
    });

    // ===== Multi-leaf / odd-count / capacity coverage =====
    //
    // actual_count is a leaf count, so odd batches are valid. These exercise the
    // padded leaf slots and the insert windows up to MAX_L.

    it("honest 2-leaf deposit batch passes", async () => {
        const leaves = [
            simpleLeaf({ J, P, val: 33n, isDeposit: 1, asset: 7n, pk: 0xaa1n }),
            simpleLeaf({ J, P, val: 77n, isDeposit: 1, asset: 7n, pk: 0xaa2n }),
        ];
        const w = buildHonest(P, 0, leaves);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("honest odd batch: 3 leaves, fewer than a spend's 6 outputs, passes", async () => {
        // A 3-output transact bundle emits three commitments, so the batch must
        // accept an odd leaf count.
        const leaves = [
            simpleLeaf({ J, P, val: 11n, isDeposit: 0, pk: 0xb01n }),
            simpleLeaf({ J, P, val: 22n, isDeposit: 0, pk: 0xb02n }),
            simpleLeaf({ J, P, val: 33n, isDeposit: 0, pk: 0xb03n }),
        ];
        const w = buildHonest(P, 0, leaves);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("honest odd batch: MAX_L - 1 leaves passes", async () => {
        const leaves: LeafWitness[] = [];
        for (let i = 0; i < MAX_L - 1; i++) {
            leaves.push(simpleLeaf({ J, P, val: BigInt(300 + i), isDeposit: 1, pk: BigInt(0xbe00 + i) }));
        }
        const w = buildHonest(P, 0, leaves);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("honest full-batch (actual_count = MAX_L) passes", async () => {
        const leaves: LeafWitness[] = [];
        for (let i = 0; i < MAX_L; i++) {
            leaves.push(simpleLeaf({ J, P, val: BigInt(300 + 2 * i), isDeposit: 1, pk: BigInt(0xbf00 + i) }));
        }
        const w = buildHonest(P, 0, leaves);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("mixed deposit + spend leaves in same batch passes", async () => {
        const leaves = [
            simpleLeaf({ J, P, val: 50n, isDeposit: 1, pk: 0xc01n }),
            simpleLeaf({ J, P, val: 7n, isDeposit: 0, pk: 0xc02n }),
            simpleLeaf({ J, P, val: 100n, isDeposit: 1, pk: 0xc03n }),
        ];
        const w = buildHonest(P, 0, leaves);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("honest odd batch at non-zero start_index passes", async () => {
        // Exercises both roots at start_index = 13 (digits [1, 3, 0, ...]);
        // inserts land at indices 13..15, crossing a level-1 carry.
        const leaves = [
            simpleLeaf({ J, P, val: 3n, isDeposit: 1, pk: 0xd01n }),
            simpleLeaf({ J, P, val: 7n, isDeposit: 1, pk: 0xd02n }),
            simpleLeaf({ J, P, val: 9n, isDeposit: 1, pk: 0xd03n }),
        ];
        const w = buildHonest(P, 13, leaves);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    // ===== Padding coverage =====
    //
    // Section 3 of tree_update_batch.circom asserts (1 - active[k]) * X === 0
    // for every per-leaf field. Each row writes one inactive-slot field and
    // expects rejection. With actual_count = 1, slot 1 is inactive.

    interface PaddingCase {
        /** Names the per-leaf field, as it reads in the circom. */
        field: string;
        /** Write the non-zero value into the inactive slot. */
        poison: (w: BatchWitness) => void;
        /**
         * Whether the field is a PolyEval coefficient. All are except `rcv`, and
         * those rows need Fiat-Shamir re-derived: otherwise a stale `z` rejects
         * the witness before the padding constraint is reached.
         */
        polyEvalBound?: boolean;
    }

    const PADDING_CASES: PaddingCase[] = [
        { field: "cm",             poison: w => { w.cms[1] = 0xbadcafen; } },
        // Step 6 shifts an inactive slot's y by 1 and runs BabyCheck over
        // (x, y + 1), so this row trips that too: no x other than 0 puts (x, 1)
        // on the curve, and the padding constraint cannot be isolated here.
        { field: "cv_dep_x",       poison: w => { w.cvDep[1] = [1n, w.cvDep[1][1]]; } },
        // y = -2 shifts to (0, -1), which is on the curve, so BabyCheck stays
        // satisfied and the rejection is attributable to the padding constraint
        // alone.
        { field: "cv_dep_y",       poison: w => { w.cvDep[1] = [0n, BN254_FR - 2n]; } },
        { field: "leaf_asset",     poison: w => { w.leafAsset[1] = 42n; } },
        { field: "leaf_public_in", poison: w => { w.leafPublicIn[1] = 99n; } },
        { field: "is_deposit",     poison: w => { w.isDeposit[1] = 1; } },
        { field: "rcv",            poison: w => { w.rcv[1] = 7n; }, polyEvalBound: false },
    ];

    for (const { field, poison, polyEvalBound = true } of PADDING_CASES) {
        it(`padding: non-zero ${field} in inactive slot is rejected`, async () => {
            const w = buildHonest(P, 0, [simpleLeaf({ J, P, val: 9n, isDeposit: 1 })]);
            poison(w);
            if (polyEvalBound) rebindFiatShamir(w);
            await expectWitnessFails(
                circuit,
                treeUpdateBatchInputJson(w),
                `(1 - active[1]) * ${field} === 0 did not reject a non-zero inactive slot`,
            );
        });
    }

    // ===== Other negative coverage =====

    it("FAILS when actual_count == 0 (Num2Bits(COUNT_BITS) rejects -1)", async () => {
        // The circuit decomposes (actual_count - 1) in COUNT_BITS bits;
        // actual_count = 0 yields -1, a 254-bit field element that does not fit.
        const w = buildHonest(P, 0, [simpleLeaf({ J, P, val: 1n, isDeposit: 1 })]);
        w.actualCount = 0;
        // Zero out the would-be-active slot fields so only the count check fires.
        w.cms[0] = 0n;
        w.cvDep[0] = [0n, 0n];
        w.leafAsset[0] = 0n; w.leafPublicIn[0] = 0n;
        w.isDeposit[0] = 0; w.rcv[0] = 0n;
        rebindFiatShamir(w);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "Num2Bits(COUNT_BITS) must reject actual_count - 1 = -1",
        );
    });

    it("FAILS when actual_count > MAX_L (Num2Bits(COUNT_BITS) rejects it)", async () => {
        // COUNT_BITS bounds (actual_count - 1) ∈ [0, MAX_L - 1], so
        // actual_count ≤ MAX_L. At MAX_L + 1 the decomposition needs
        // COUNT_BITS + 1 bits. Derived from MAX_L so it tracks the width.
        const w = buildHonest(P, 0, [simpleLeaf({ J, P, val: 1n, isDeposit: 1 })]);
        w.actualCount = MAX_L + 1;
        rebindFiatShamir(w);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "Num2Bits(COUNT_BITS) must reject a count above MAX_L",
        );
    });

    it("FAILS when is_deposit is non-boolean (=2)", async () => {
        const w = buildHonest(P, 0, [simpleLeaf({ J, P, val: 1n, isDeposit: 1 })]);
        w.isDeposit[0] = 2;
        rebindFiatShamir(w);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "is_deposit must be constrained boolean",
        );
    });

    it("FAILS when leaf_public_in exceeds 2^64 (RangeCheck64)", async () => {
        // leaf_public_in at 2^64 fails the deposit-side RangeCheck64.
        const w = buildHonest(P, 0, [simpleLeaf({ J, P, val: 1n, isDeposit: 1 })]);
        w.leafPublicIn[0] = TWO_64;
        rebindFiatShamir(w);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "RangeCheck64 must reject leaf_public_in at 2^64",
        );
    });

    it("FAILS on C-1' value inflation: same asset, wrong claimed value", async () => {
        // cv_dep = leaf_public_in · V^asset + rcv · H. Inflating the claim while
        // keeping cv_dep honest breaks the equality.
        const w = buildHonest(P, 0, [simpleLeaf({ J, P, val: 150n, isDeposit: 1 })]);
        w.leafPublicIn[0] = 200n;
        rebindFiatShamir(w);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "cv_dep equality must reject an inflated claimed value",
        );
    });

    it("FAILS on C-1'' split: value moved between two deposit leaves", async () => {
        // A binding over an aggregate of leaves fixes only Σvalue mod the
        // subgroup order, admitting public_in = 1 with leaf 0 loaded with 2^63
        // and leaf 1 absorbing the remainder. The per-leaf binding rejects at
        // leaf 0's own equality.
        const asset = 7n;
        const assetGen = J.hashToAssetGen(asset);
        const honest = simpleLeaf({ J, P, val: 1n, isDeposit: 1, asset });
        const tampered: LeafWitness = {
            ...honest,
            cvDep: J.valueCommit(1n << 63n, assetGen, honest.rcv),
        };
        const w = buildHonest(P, 0, [tampered]);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "leaf 0's own deposit equality must reject the split",
        );
    });

    it("FAILS when rcv is tampered (deposit binding)", async () => {
        // cv_dep = leaf_public_in·V + rcv·H. Shifting rcv moves the rhs by
        // Δ·H ≠ 0, so the point equality fails. rcv is not a PolyEval
        // coefficient, so the Fiat-Shamir challenge is unchanged.
        const w = buildHonest(P, 0, [simpleLeaf({ J, P, val: 150n, isDeposit: 1 })]);
        w.rcv[0] = w.rcv[0] + 1n;
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "the deposit binding must reject a shifted rcv",
        );
    });

    it("FAILS when a deposit leaf's value disagrees with its claimed public_in", async () => {
        // Splitting a deposit across leaves is not expressible: each deposit
        // leaf declares its own public_in and must open to exactly that.
        const honest = simpleLeaf({ J, P, val: 100n, isDeposit: 1 });
        const tampered: LeafWitness = { ...honest, leafPublicIn: 50n };
        const w = buildHonest(P, 0, [tampered]);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "a deposit leaf must open to exactly its declared public_in",
        );
    });

    // ===== Spend-leaf field zeroing (section 4) =====
    //
    // Section 3 zeroes every field of an inactive slot; section 4 also zeroes
    // the two deposit-only fields on an active spend leaf, so a relayer cannot
    // push a nonzero leaf_asset or leaf_public_in into the public inputs of a
    // batch that carries no deposit. The padding rows above do not reach these
    // constraints because section 3 rejects inactive slots first.

    it("FAILS on a nonzero leaf_asset in an active spend leaf", async () => {
        const w = buildHonest(P, 0, [simpleLeaf({ J, P, val: 100n, isDeposit: 0 })]);
        w.leafAsset[0] = 42n;
        rebindFiatShamir(w);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "(1 - is_deposit[0]) * leaf_asset[0] === 0 did not reject a spend leaf",
        );
    });

    it("FAILS on a nonzero leaf_public_in in an active spend leaf", async () => {
        const w = buildHonest(P, 0, [simpleLeaf({ J, P, val: 100n, isDeposit: 0 })]);
        w.leafPublicIn[0] = 99n;
        rebindFiatShamir(w);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "(1 - is_deposit[0]) * leaf_public_in[0] === 0 did not reject a spend leaf",
        );
    });

    // ===== Remaining single-constraint negatives =====

    it("FAILS when an active cv_dep is off the curve (BabyCheck)", async () => {
        // (1, 1) is off Baby-Jubjub: a + 1 = 168701 while 1 + d = 168697. It is
        // set on the leaf witness before the tree is built, so the inserted leaf
        // hashes the same point and new_root matches, leaving BabyCheck as the
        // only rejecting constraint. A spend leaf skips the deposit binding,
        // which would otherwise also reject it.
        const honest = simpleLeaf({ J, P, val: 100n, isDeposit: 0 });
        const offCurve: LeafWitness = { ...honest, cvDep: [1n, 1n] };
        const w = buildHonest(P, 0, [offCurve]);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "BabyCheck must reject an off-curve cv_dep on an active slot",
        );
    });

    it("FAILS when new_root does not match the batched insert", async () => {
        // Counterpart of the old_root frontier test: old_root binds the input
        // frontier and `new_root === append.new_root` binds the resulting root,
        // so a relayer cannot name an arbitrary root for the advanced tree.
        const w = buildHonest(P, 4, [simpleLeaf({ J, P, val: 100n, isDeposit: 1 })]);
        w.newRoot = w.newRoot + 1n;
        rebindFiatShamir(w);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "new_root === append.new_root must reject a forged new_root",
        );
    });

    // ===== Batched insert at production depth =====
    //
    // BatchAppend sizes each level's window for the worst case, a run that
    // straddles a boundary at that level. `batch_append.test.ts` sweeps every
    // start at depth 4 with distinct leaves; these place the straddle at every
    // level of the deployed shape, through the full circuit.

    let straddleLeaves: LeafWitness[];
    before(() => {
        straddleLeaves = Array.from({ length: MAX_L }, (_, i) => seededLeaf(P, J, i, 1));
    });

    for (let level = 1; level < BATCH_DEPTH; level++) {
        it(`honest full batch straddling a level-${level} boundary passes`, async () => {
            const start = ARITY ** level - 3;
            const w = buildHonest(P, start, straddleLeaves);
            await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
        });
    }

    it("honest full batch ending on the last index of the tree passes", async () => {
        const leaves = Array.from({ length: MAX_L }, (_, i) => seededLeaf(P, J, i, 0));
        const w = buildHonest(P, CAPACITY - MAX_L, leaves);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("FAILS on a non-zero frontier slot nothing reads", async () => {
        // The slot at the digit is the lowest unread slot. Checked at level 0,
        // where the digit is non-zero, and at the first level where it is 0;
        // both slots are pinned to zero.
        const start = 21;
        const honest = buildHonest(P, start, [simpleLeaf({ J, P, val: 9n, isDeposit: 1 })]);
        const emptyLevel = [...Array(BATCH_DEPTH).keys()].find(d => quatDigit(start, d) === 0)!;
        for (const d of [0, emptyLevel]) {
            const k = quatDigit(start, d);
            const w = { ...honest, frontier: honest.frontier.map(lvl => lvl.slice()) };
            w.frontier[d][k] = 1n;
            await expectWitnessFails(
                circuit,
                treeUpdateBatchInputJson(w),
                `(1 - read) * frontier_in[${d}][${k}] === 0 must reject a non-zero unread slot`,
            );
        }
    });

    it("FAILS when rcv reaches 2^252 (MulH's Num2Bits(RCV_BITS))", async () => {
        // rcv feeds MulH on every slot, so the width bound holds for a spend
        // leaf, where the deposit binding is skipped and Num2Bits(252) is the
        // only rejecting constraint. rcv is not a PolyEval coefficient, so the
        // challenge is unchanged.
        const w = buildHonest(P, 0, [simpleLeaf({ J, P, val: 100n, isDeposit: 0 })]);
        w.rcv[0] = TWO_252;
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "Num2Bits(RCV_BITS) must reject rcv at 2^252",
        );
    });


    // ===== Degenerate deposit binding (step 6a) =====
    //
    // The deposit binding pins `leaf_asset[k]` only while the V^leaf_asset term
    // is present. `ValueTimesGen(0, gen)` is the curve identity for every `gen`,
    // so at `leaf_public_in[k] == 0` the equality reduces to
    // `cv_dep[k] == rcv[k]·H` and the asset drops out of the system, leaving a
    // coefficient bounded only by a 64-bit range check. Four such leaves give
    // 4 × 64 = 256 free bits against a 254-bit modulus.
    //
    // Step 6a splits per slot: a leaf carrying value must declare a non-zero
    // asset (the binding pins it), and a zero-value leaf must declare asset 0
    // (nothing reads it, so it is canonicalised rather than left free).

    it("a zero-value fee note is accepted at asset 0", async () => {
        // Liveness: a flush at fbps = 0 mints a zero-value fee note, which
        // `_validateDeposit` permits ("The fee note's value may be zero").
        const leaves = [
            simpleLeaf({ J, P, val: 1000n, isDeposit: 1, asset: 7n, pk: 0xf01n }),
            simpleLeaf({ J, P, val: 0n, isDeposit: 1, asset: 0n, pk: 0xf02n }),
        ];
        const w = buildHonest(P, 0, leaves);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("6a: FAILS on a zero-value deposit leaf declaring a non-zero asset", async () => {
        // With zero value the binding does not constrain the asset, so a
        // non-canonical asset here is a free 64-bit coefficient. cv_dep opens
        // correctly at asset 7, so 6a rejects rather than the Pedersen equality.
        const leaves = [
            simpleLeaf({ J, P, val: 1000n, isDeposit: 1, asset: 7n, pk: 0xf03n }),
            simpleLeaf({ J, P, val: 0n, isDeposit: 1, asset: 7n, pk: 0xf04n }),
        ];
        const w = buildHonest(P, 0, leaves);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "zero_value[1] * leaf_asset[1] === 0 must reject a worthless leaf with an asset",
        );
    });

    it("6a: a valued leaf still requires a non-zero asset", async () => {
        // SpentNote rejects asset id 0 on every real note, so a valued leaf at
        // asset 0 would be committed but unspendable.
        const w = buildHonest(P, 0, [simpleLeaf({ J, P, val: 100n, isDeposit: 1, asset: 0n })]);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "(active_dep[0] - zero_value[0]) * IsZero(leaf_asset[0]) === 0 must reject asset 0",
        );
    });

    it("a full flush of four principal/fee pairs, every fee note worthless, passes", async () => {
        // The configuration that yields four zero-value leaves; 6a removes their
        // asset freedom while keeping the batch provable.
        const w = buildHonest(P, 0, depositPairs(P, J, MAX_L));
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("a deposit leaf at an odd slot needs no relation to its neighbour", async () => {
        // The circuit is layout-agnostic: no constraint ties slot k to slot k-1.
        // A cross-asset pair of valued leaves passes here and is rejected
        // on-chain by the escrow digest in MASP._drainDeposit.
        const leaves = [
            simpleLeaf({ J, P, val: 100n, isDeposit: 1, asset: 7n, pk: 0xf05n }),
            simpleLeaf({ J, P, val: 25n, isDeposit: 1, asset: 99n, pk: 0xf06n }),
        ];
        const w = buildHonest(P, 0, leaves);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("6a is vacuous on a spend batch", async () => {
        // 6a is gated on active_dep. In an all-spend batch `leaf_asset` and
        // `leaf_public_in` are forced to zero by steps 3 and 4, a stronger pin
        // than either arm.
        const leaves = Array.from({ length: 6 }, (_, i) =>
            simpleLeaf({ J, P, val: BigInt(10 + i), isDeposit: 0, pk: BigInt(0xf20 + i) }));
        const w = buildHonest(P, 0, leaves);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    // ===== Divergent witness (soundness) =====
    //
    // The other blocks in this file derive `(z, y)` from the object passed to
    // the circuit, via `rebindFiatShamir`. That checks whether a constraint
    // fires, but witness and calldata are the same batch by construction, so a
    // signal the circuit never pins still appears bound.
    //
    // In deployment they are separate: `MASP` hashes its calldata into `z` and
    // compares its `y`, and the prover picks any witness satisfying the R1CS at
    // that `z`. `z` is a circuit input read before the witness is chosen, so
    // Schwartz-Zippel does not apply and hashing a word into the challenge binds
    // it only if a constraint already pins it (src/README.md § 2a).
    //
    // These tests build the two views separately with `calldataView` +
    // `bindFiatShamir` and assert the circuit cannot attest to a batch the
    // contract did not validate.

    /** The base each divergence is applied to: one honest single-leaf deposit. */
    function honestDeposit(val = 1000n, isDeposit: 0 | 1 = 1): BatchWitness {
        return buildHonest(P, 0, [simpleLeaf({ J, P, val, isDeposit, asset: 7n })]);
    }

    /** The shared harness guard, over this circuit's challenge preimage. */
    function assertDiverged(w: BatchWitness, calldata: TreeUpdateBatchPublicArgs, field: string) {
        assertViewsDiverge(treeUpdateBatchChallenge(w), treeUpdateBatchChallenge(calldata), field);
    }

    for (const { field, diverge } of DIVERGENCE_CASES) {
        it(`divergent witness: ${field} declared differently in calldata cannot be forged`, async () => {
            const w = honestDeposit();
            const calldata = calldataView(w);
            diverge(calldata);
            assertDiverged(w, calldata, field);
            bindFiatShamir(w, calldata);
            await expectNotForgeable(circuit, treeUpdateBatchInputJson(w), w.y, field);
        });
    }

    // The two cases below stage complete mint attempts rather than one-field
    // divergences. Both are reachable by a single party: `MASP.flushBatch` is
    // unpermissioned and `deposit` is external, so the depositor can also be the
    // flusher.

    it("divergent witness: is_deposit cleared in the witness cannot mint an unbound leaf", async () => {
        // The contract sees a 1-unit deposit of asset 7 and escrows accordingly.
        // The witness declares the same leaf a spend, so `active_dep` is 0, the
        // only constraint tying `cv_dep` to an asset and amount is gated off, and
        // the committed leaf holds 2^63 units instead of 1.
        //
        // `is_deposit` gates that constraint and is a private witness signal;
        // the circuit header lists it as a contract obligation (item 4).
        const w = buildHonest(P, 0, [simpleLeaf({ J, P, val: 1n << 63n, isDeposit: 0, asset: 7n })]);
        const calldata = calldataView(w);
        calldata.isDeposit[0] = 1;
        calldata.leafAsset[0] = 7n;
        calldata.leafPublicIn[0] = 1n;
        assertDiverged(w, calldata, "is_deposit");
        bindFiatShamir(w, calldata);
        await expectNotForgeable(circuit, treeUpdateBatchInputJson(w), w.y, "is_deposit");
    });

    it("divergent witness: leaf_public_in inflated in the witness cannot mint value", async () => {
        // The gate is honestly 1 and the deposit binding holds against the
        // witness operands: `cv_dep` opens to 2^63 units of asset 7, while the
        // calldata the contract escrowed against declares 1. Pinning
        // `is_deposit` alone does not prevent this.
        const w = honestDeposit(1n << 63n);
        const calldata = calldataView(w);
        calldata.leafPublicIn[0] = 1n;
        assertDiverged(w, calldata, "leaf_public_in");
        bindFiatShamir(w, calldata);
        await expectNotForgeable(circuit, treeUpdateBatchInputJson(w), w.y, "leaf_public_in");
    });

    it("divergent witness: a fully honest witness still matches its own calldata", async () => {
        // Harness guard. Every divergence above perturbs this unmodified
        // snapshot; if the circuit's `y` disagreed here, those cases would be
        // rejected for the wrong reason and pass vacuously.
        //
        // `rebindFiatShamir` is defined as this call, so this checks the circuit
        // against the reference, not one binder against the other.
        const w = honestDeposit();
        bindFiatShamir(w, calldataView(w));
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    // ===== Tree capacity =====
    //
    // The last inserted index, start_index + actual_count - 1, is range-checked
    // to 2·DEPTH bits. Bounding start_index + k for every slot would make the top
    // MAX_L - 1 leaves unreachable and an honest one-leaf batch at the last free
    // index unsatisfiable.

    it("accepts a single leaf at the last index in the tree", async () => {
        const w = buildHonest(P, CAPACITY - 1, [simpleLeaf({ J, P, val: 1n, isDeposit: 1 })]);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("FAILS when a batch runs past the end of the tree", async () => {
        // One free slot, two leaves: the last index is CAPACITY = 2^(2·DEPTH),
        // one past what Num2Bits(2·DEPTH) holds. The reference tree does not
        // bound-check, so the witness builds and the circuit must reject it.
        const leaves = [
            simpleLeaf({ J, P, val: 1n, isDeposit: 1, pk: 0xe01n }),
            simpleLeaf({ J, P, val: 2n, isDeposit: 1, pk: 0xe02n }),
        ];
        const w = buildHonest(P, CAPACITY - 1, leaves);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "Num2Bits(2·DEPTH) must reject an active insertion index at capacity",
        );
    });
});
