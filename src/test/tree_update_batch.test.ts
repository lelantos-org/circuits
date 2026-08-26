// Tests for `tree_update_batch.circom`. Covers:
//   - per-leaf format leaf = Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y)
//   - per-leaf deposit binding cv_dep = leaf_public_in · V^leaf_asset + rcv · H
//   - C-1 regression: cross-asset / value-inflation rejection
//   - odd leaf counts (1, 3) and leaf-granular multiplexing
//   - padding zero constraints
//
// actual_count is a leaf count, so a batch may commit an odd number of leaves.
// Most cases use a small actual_count for runtime; the larger ones cover the
// multiplex logic.
//
// The witness builders live in `lib/batch.ts`, shared with the fuzz suite.

import { Jubjub, Poseidon } from "./helpers";
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
import { MAX_L, TIMEOUT_HEAVY, TWO_64 } from "./lib/constants";

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

    // ===== Frontier-binding regression coverage (H-1 fix) =====
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

    it("honest odd batch: 3 leaves (3x3 transact output shape) passes", async () => {
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
        { field: "cv_dep_x",       poison: w => { w.cvDep[1] = [1n, w.cvDep[1][1]]; } },
        { field: "cv_dep_y",       poison: w => { w.cvDep[2] = [w.cvDep[2][0], 1n]; } },
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
});
