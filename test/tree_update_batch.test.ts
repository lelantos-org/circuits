// Tests for `tree_update_batch.circom`. Covers:
//   - per-leaf format leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y)
//   - per-leaf deposit binding cv_dep = leaf_public_in · V^leaf_asset + rcv · H
//   - C-1: cross-asset and value-inflation rejection
//   - odd leaf counts (1, 3) and leaf-granular multiplexing
//   - padding zero constraints
//
// actual_count is a leaf count, so a batch may commit an odd number of leaves.
// Most cases use a small actual_count for runtime; the larger ones cover the
// multiplex logic.
//
// The witness builders live in `lib/batch.ts`, shared with the fuzz suite.

import { BN254_FR, Jubjub, Poseidon } from "./helpers";
import { loadCircuit, srcPath, type CircuitTester } from "./lib/circuit";
import { treeUpdateBatchInputJson } from "./lib/inputs";
import { expectWitnessFails, expectWitnessY } from "./lib/expect";
import {
    buildHonest,
    buildLeafWitness,
    rebindFiatShamir,
    simpleLeaf,
    type BatchWitness,
    type LeafWitness,
} from "./lib/batch";
import { ARITY, BATCH_DEPTH, MAX_L, TIMEOUT_HEAVY, TWO_64, TWO_252 } from "./lib/constants";

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
        // Attacker pays with asset=7 (publicIn=1) but cv_dep commits to a
        // different asset's value. The per-leaf Pedersen binding catches this
        // since V^7 and V^99 are independent generators.
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

    // ===== Frontier binding (H-1) =====
    //
    // FrontierRoot rebinds `frontier_in` to public `old_root`, so a relayer
    // cannot pair a real `oldRoot` with a forged frontier. Without the binding,
    // a batch can corrupt the on-chain root permanently.

    it("frontier binding: honest non-zero start_index passes", async () => {
        // start_index = 5 ⇒ digits [1,1,0,...]. Exercises pre/eq branches
        // at low levels.
        const w = buildHonest(P, 5, [simpleLeaf({ J, P, val: 42n, isDeposit: 1 })]);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("frontier binding: large prefill (start_index=21) honest passes", async () => {
        // 21 = 0b010101 ⇒ digits [1,1,1,0,...]. Non-trivial frontier at
        // the three lowest levels.
        const w = buildHonest(P, 21, [simpleLeaf({ J, P, val: 9n, isDeposit: 1 })]);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("frontier binding: corrupted frontier entry rejected", async () => {
        // Honest oldRoot + cms but tampered frontier ⇒ FrontierRoot rebuild
        // diverges from old_root ⇒ `old_root === frontier_root.root` fails.
        const w = buildHonest(P, 8, [simpleLeaf({ J, P, val: 1000n, isDeposit: 1 })]);
        w.frontier[1][1] = w.frontier[1][1] + 1n;
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "FrontierRoot's rebuild must diverge from old_root under a tampered frontier",
        );
    });

    it("frontier binding: empty-tree frontier with wrong oldRoot rejected", async () => {
        // Frontier honest (all-zeros for empty tree) but oldRoot lied about.
        // FrontierRoot rebuilds the genuine empty-tree root; equality check
        // catches the mismatch.
        const w = buildHonest(P, 0, [simpleLeaf({ J, P, val: 1n, isDeposit: 1 })]);
        w.oldRoot = w.oldRoot + 1n;
        rebindFiatShamir(w);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "old_root === frontier_root.root must reject a forged old_root",
        );
    });

    // ===== Multi-leaf / odd-count / capacity coverage (B) =====
    //
    // actual_count is a leaf count, so odd batches are valid. These exercise the
    // multiplexed frontier / root threading up to MAX_L.

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
        // Exercises FrontierRoot + insert chain at start_index = 13
        // (digits [1, 3, 0, ...]); inserts land at indices 13..15, crossing
        // a level-1 carry.
        const leaves = [
            simpleLeaf({ J, P, val: 3n, isDeposit: 1, pk: 0xd01n }),
            simpleLeaf({ J, P, val: 7n, isDeposit: 1, pk: 0xd02n }),
            simpleLeaf({ J, P, val: 9n, isDeposit: 1, pk: 0xd03n }),
        ];
        const w = buildHonest(P, 13, leaves);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    // ===== Padding hole coverage (C) =====
    //
    // Section 3 of tree_update_batch.circom asserts (1 - active[k]) * X === 0
    // for every per-leaf field. Each row below writes ONE inactive-slot field
    // and expects rejection. With actual_count = 1, slot 1 is inactive.

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

    // ===== Other negative coverage (D) =====

    it("FAILS when actual_count == 0 (Num2Bits(COUNT_BITS) rejects -1)", async () => {
        // Circuit decomposes (actual_count - 1) in COUNT_BITS bits ⇒
        // actual_count=0 yields -1, a 254-bit field element that Num2Bits
        // cannot fit.
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
        // COUNT_BITS + 1 bits and Num2Bits(COUNT_BITS) rejects it. Derived from
        // MAX_L rather than written as a literal so it tracks the width.
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
        // Build an honest witness then override leaf_public_in past 2^64;
        // the deposit-side RangeCheck64 fails.
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
        // Honest path: cv_dep = leaf_public_in · V^asset + rcv · H.
        // Tamper: inflate the claim while keeping cv_dep real ⇒ equality fails.
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
        // A binding over an aggregate of leaves would fix only Σvalue mod the
        // subgroup order, letting an attacker claim public_in = 1 while loading
        // leaf 0 with 2^63 and leaving leaf 1 to absorb the remainder. Per-leaf
        // binding rejects at leaf 0's own equality.
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
        // Honest: cv_dep = leaf_public_in·V + rcv·H. Tamper rcv ⇒ rhs shifts
        // by Δ·H ≠ 0 ⇒ point equality fails. rcv is NOT in PolyEval so
        // Fiat-Shamir is unchanged.
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
    // Section 3 zeroes every field of an INACTIVE slot; section 4 additionally
    // zeroes the two deposit-only fields on an ACTIVE spend leaf, so a relayer
    // cannot push a nonzero leaf_asset or leaf_public_in into the public inputs
    // of a batch that carries no deposit. The padding rows above never reach
    // these: they poison inactive slots, which section 3 rejects first.

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
        // (1, 1) is off Baby-Jubjub: a + 1 = 168701 while 1 + d = 168697. Set on
        // the leaf witness BEFORE the tree is built, so the inserted leaf hashes
        // this same point and new_root still matches — BabyCheck is then the only
        // constraint left to reject it. A spend leaf, so the deposit binding
        // (which would also catch it) is skipped.
        const honest = simpleLeaf({ J, P, val: 100n, isDeposit: 0 });
        const offCurve: LeafWitness = { ...honest, cvDep: [1n, 1n] };
        const w = buildHonest(P, 0, [offCurve]);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "BabyCheck must reject an off-curve cv_dep on an active slot",
        );
    });

    it("FAILS when new_root does not match the computed insert chain", async () => {
        // The mirror of the old_root frontier test: old_root binds the frontier
        // in, new_root binds the result out. Without `new_root === running_root`
        // a relayer names any root it likes for the advanced tree.
        const w = buildHonest(P, 4, [simpleLeaf({ J, P, val: 100n, isDeposit: 1 })]);
        w.newRoot = w.newRoot + 1n;
        rebindFiatShamir(w);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "new_root === running_root[MAX_L] must reject a forged new_root",
        );
    });

    it("FAILS when rcv reaches 2^252 (MulH's Num2Bits(RCV_BITS))", async () => {
        // rcv feeds MulH on every slot, deposit or not, so the width bound holds
        // for a spend leaf too — and there the deposit binding is skipped, so
        // Num2Bits(252) is the only constraint that can reject. rcv is not a
        // PolyEval coefficient, so the challenge is unchanged.
        const w = buildHonest(P, 0, [simpleLeaf({ J, P, val: 100n, isDeposit: 0 })]);
        w.rcv[0] = TWO_252;
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "Num2Bits(RCV_BITS) must reject rcv at 2^252",
        );
    });

    it("FAILS on a deposit leaf claiming asset id 0", async () => {
        // asset 0 is reserved: SpentNote rejects it on every real note, so a leaf
        // minted at asset 0 is committed and then unspendable. Built honestly at
        // asset 0 — cv_dep opens correctly to leaf_public_in units of V^0 — so
        // the deposit equality holds and the IsZero guard is what rejects.
        const w = buildHonest(P, 0, [simpleLeaf({ J, P, val: 100n, isDeposit: 1, asset: 0n })]);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson(w),
            "active_dep[0] * IsZero(leaf_asset[0]) === 0 must reject a deposit at asset 0",
        );
    });

    // ===== Tree capacity =====
    //
    // Every slot's insertion index is range-checked to 2·DEPTH bits, gated on
    // active[k]. Ungated, a Num2Bits over start_index + k for every k would make
    // the top MAX_L - 1 leaves unreachable, leaving an honest one-leaf batch at
    // the last free index unsatisfiable.

    it("accepts a single leaf at the last index in the tree", async () => {
        const w = buildHonest(P, CAPACITY - 1, [simpleLeaf({ J, P, val: 1n, isDeposit: 1 })]);
        await expectWitnessY(circuit, treeUpdateBatchInputJson(w), w.y);
    });

    it("FAILS when a batch runs past the end of the tree", async () => {
        // One free slot left, two leaves offered: slot 1's index is exactly
        // CAPACITY = 2^(2·DEPTH), one past what Num2Bits(2·DEPTH) can hold. The
        // reference tree does not bound-check, so it builds the witness and the
        // circuit is what must refuse it.
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
