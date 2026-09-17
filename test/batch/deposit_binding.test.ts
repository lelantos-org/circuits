// The per-leaf deposit binding
//
//     cv_dep = leaf_public_in · V^leaf_asset + rcv · H
//
// its operands' range checks, BabyCheck on cv_dep, and step 6a, which pins
// `leaf_asset` where the binding degenerates. Covers cross-asset and
// value-inflation rejection.

import { rebindFiatShamir, type LeafWitness } from "../lib/batch";
import { MAX_L, TIMEOUT_HEAVY, TWO_64, TWO_252 } from "../lib/constants";
import { expectBatchAccepts, expectBatchRejects, useBatchCircuit } from "./setup";

describe("tree_update_batch / deposit binding", function () {
    this.timeout(TIMEOUT_HEAVY);

    const ctx = useBatchCircuit();

    it("C-1 regression: deposit with mismatched binding (wrong asset) is rejected", async () => {
        // The depositor pays with asset=7 (publicIn=1) but cv_dep commits to a
        // different asset's value. The per-leaf Pedersen binding rejects this
        // because V^7 and V^99 are independent generators.
        const { batch, circuit, J } = ctx;
        const honest = batch.leaf({ val: 1n, isDeposit: 1, asset: 7n });
        const tampered: LeafWitness = {
            ...honest,
            cvDep: J.valueCommit(1_000_000n, J.hashToAssetGen(99n), honest.rcv),
        };
        await expectBatchRejects(
            circuit,
            batch.honest(0, [tampered]),
            "the per-leaf Pedersen binding must reject a cross-asset cv_dep",
        );
    });

    it("FAILS when leaf_public_in exceeds 2^64 (RangeCheck64)", async () => {
        // leaf_public_in at 2^64 fails the deposit-side RangeCheck64.
        const { batch, circuit } = ctx;
        const w = batch.single({ val: 1n, isDeposit: 1 });
        w.leafPublicIn[0] = TWO_64;
        rebindFiatShamir(w);
        await expectBatchRejects(circuit, w, "RangeCheck64 must reject leaf_public_in at 2^64");
    });

    it("FAILS on C-1' value inflation: same asset, wrong claimed value", async () => {
        // cv_dep = leaf_public_in · V^asset + rcv · H. Inflating the claim while
        // keeping cv_dep honest breaks the equality.
        const { batch, circuit } = ctx;
        const w = batch.single({ val: 150n, isDeposit: 1 });
        w.leafPublicIn[0] = 200n;
        rebindFiatShamir(w);
        await expectBatchRejects(circuit, w, "cv_dep equality must reject an inflated claimed value");
    });

    it("FAILS on C-1'' split: value moved between two deposit leaves", async () => {
        // A binding over an aggregate of leaves fixes only Σvalue mod the
        // subgroup order, admitting public_in = 1 with leaf 0 loaded with 2^63
        // and leaf 1 absorbing the remainder. The per-leaf binding rejects at
        // leaf 0's own equality.
        const { batch, circuit, J } = ctx;
        const asset = 7n;
        const honest = batch.leaf({ val: 1n, isDeposit: 1, asset });
        const tampered: LeafWitness = {
            ...honest,
            cvDep: J.valueCommit(1n << 63n, J.hashToAssetGen(asset), honest.rcv),
        };
        await expectBatchRejects(
            circuit,
            batch.honest(0, [tampered]),
            "leaf 0's own deposit equality must reject the split",
        );
    });

    it("FAILS when rcv is tampered (deposit binding)", async () => {
        // cv_dep = leaf_public_in·V + rcv·H. Shifting rcv moves the rhs by
        // Δ·H ≠ 0, so the point equality fails. rcv is not a PolyEval
        // coefficient, so the Fiat-Shamir challenge is unchanged.
        const { batch, circuit } = ctx;
        const w = batch.single({ val: 150n, isDeposit: 1 });
        w.rcv[0] = w.rcv[0] + 1n;
        await expectBatchRejects(circuit, w, "the deposit binding must reject a shifted rcv");
    });

    it("FAILS when a deposit leaf's value disagrees with its claimed public_in", async () => {
        // Splitting a deposit across leaves is not expressible: each deposit
        // leaf declares its own public_in and must open to exactly that.
        const { batch, circuit } = ctx;
        const tampered: LeafWitness = { ...batch.leaf({ val: 100n, isDeposit: 1 }), leafPublicIn: 50n };
        await expectBatchRejects(
            circuit,
            batch.honest(0, [tampered]),
            "a deposit leaf must open to exactly its declared public_in",
        );
    });

    it("FAILS when an active cv_dep is off the curve (BabyCheck)", async () => {
        // (1, 1) is off Baby-Jubjub: a + 1 = 168701 while 1 + d = 168697. It is
        // set on the leaf witness before the tree is built, so the inserted leaf
        // hashes the same point and new_root matches, leaving BabyCheck as the
        // only rejecting constraint. A spend leaf skips the deposit binding,
        // which would otherwise also reject it.
        const { batch, circuit } = ctx;
        const offCurve: LeafWitness = { ...batch.leaf({ val: 100n, isDeposit: 0 }), cvDep: [1n, 1n] };
        await expectBatchRejects(
            circuit,
            batch.honest(0, [offCurve]),
            "BabyCheck must reject an off-curve cv_dep on an active slot",
        );
    });

    it("FAILS when rcv reaches 2^252 (MulH's Num2Bits(RCV_BITS))", async () => {
        // rcv feeds MulH on every slot, so the width bound holds for a spend
        // leaf, where the deposit binding is skipped and Num2Bits(252) is the
        // only rejecting constraint. rcv is not a PolyEval coefficient, so the
        // challenge is unchanged.
        const { batch, circuit } = ctx;
        const w = batch.single({ val: 100n, isDeposit: 0 });
        w.rcv[0] = TWO_252;
        await expectBatchRejects(circuit, w, "Num2Bits(RCV_BITS) must reject rcv at 2^252");
    });

    // ===== degenerate deposit binding (step 6a) =====
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
        const { batch, circuit } = ctx;
        const leaves = [
            batch.leaf({ val: 1000n, isDeposit: 1, asset: 7n, pk: 0xf01n }),
            batch.leaf({ val: 0n, isDeposit: 1, asset: 0n, pk: 0xf02n }),
        ];
        await expectBatchAccepts(circuit, batch.honest(0, leaves));
    });

    it("6a: FAILS on a zero-value deposit leaf declaring a non-zero asset", async () => {
        // With zero value the binding does not constrain the asset, so a
        // non-canonical asset here is a free 64-bit coefficient. cv_dep opens
        // correctly at asset 7, so 6a rejects rather than the Pedersen equality.
        const { batch, circuit } = ctx;
        const leaves = [
            batch.leaf({ val: 1000n, isDeposit: 1, asset: 7n, pk: 0xf03n }),
            batch.leaf({ val: 0n, isDeposit: 1, asset: 7n, pk: 0xf04n }),
        ];
        await expectBatchRejects(
            circuit,
            batch.honest(0, leaves),
            "zero_value[1] * leaf_asset[1] === 0 must reject a worthless leaf with an asset",
        );
    });

    it("6a: a valued leaf still requires a non-zero asset", async () => {
        // SpentNote rejects asset id 0 on every real note, so a valued leaf at
        // asset 0 would be committed but unspendable.
        const { batch, circuit } = ctx;
        await expectBatchRejects(
            circuit,
            batch.single({ val: 100n, isDeposit: 1, asset: 0n }),
            "(active_dep[0] - zero_value[0]) * IsZero(leaf_asset[0]) === 0 must reject asset 0",
        );
    });

    it("a full flush of four principal/fee pairs, every fee note worthless, passes", async () => {
        // The configuration that yields four zero-value leaves; 6a removes their
        // asset freedom while keeping the batch provable.
        const { batch, circuit } = ctx;
        await expectBatchAccepts(circuit, batch.honest(0, batch.depositPairs(MAX_L)));
    });

    it("a deposit leaf at an odd slot needs no relation to its neighbour", async () => {
        // The circuit is layout-agnostic: no constraint ties slot k to slot k-1.
        // A cross-asset pair of valued leaves passes here and is rejected
        // on-chain by the escrow digest in MASP._drainDeposit.
        const { batch, circuit } = ctx;
        const leaves = [
            batch.leaf({ val: 100n, isDeposit: 1, asset: 7n, pk: 0xf05n }),
            batch.leaf({ val: 25n, isDeposit: 1, asset: 99n, pk: 0xf06n }),
        ];
        await expectBatchAccepts(circuit, batch.honest(0, leaves));
    });

    it("6a is vacuous on a spend batch", async () => {
        // 6a is gated on active_dep. In an all-spend batch `leaf_asset` and
        // `leaf_public_in` are forced to zero by steps 3 and 4, a stronger pin
        // than either arm.
        const { batch, circuit } = ctx;
        const leaves = Array.from({ length: 6 }, (_, i) =>
            batch.leaf({ val: BigInt(10 + i), isDeposit: 0, pk: BigInt(0xf20 + i) }));
        await expectBatchAccepts(circuit, batch.honest(0, leaves));
    });
});
