// The per-leaf deposit binding. On a deposit slot the circuit builds
//
//     leaf = Poseidon(TAG_CM, leaf_asset · 2^64 + leaf_public_in, cms[k])
//
// with `cms[k]` the depositor's `inner = Poseidon(TAG_INNER, pk, rho, rcm)`:
// the note commitment SpentNote recomputes.
//
// Most rejections set the tampered leaf before the tree is built, so `new_root`
// agrees with it and only the constraint under test can reject.

import { expect } from "chai";
import { TAG_CM, buildInner, commit, commitWithInner, type Field } from "../helpers";
import { rebindFiatShamir, type LeafWitness } from "../lib/batch";
import { MAX_L, TIMEOUT_HEAVY, TWO_64 } from "../lib/constants";
import { expectBatchAccepts, expectBatchRejects, useBatchCircuit } from "./setup";

describe("tree_update_batch / deposit binding", function () {
    this.timeout(TIMEOUT_HEAVY);

    const ctx = useBatchCircuit();

    const OWNER = { pk: 0xabcn, rho: 1n, rcm: 3n };

    /** The `inner` every hand-built leaf below shares. */
    function inner(): Field {
        return buildInner(ctx.P, OWNER);
    }

    /** A deposit slot declaring `(asset, value)` whose tree leaf is `leaf`. */
    function declared(asset: Field, value: Field, leaf: Field): LeafWitness {
        return { word: inner(), leaf, leafAsset: asset, leafPublicIn: value, isDeposit: 1 };
    }

    /** The leaf hash over a packed word the reference refuses to build. */
    function leafOverPacked(packed: Field): Field {
        return ctx.P.hash([TAG_CM, packed, inner()]);
    }

    // ===== what an honest deposit inserts =====

    it("a deposit leaf is the commitment of the note it declares", async () => {
        // The leaf must equal the `commit(asset, value, pk, rho, rcm)` the
        // transact circuit opens, or a deposited note could never be spent.
        const { batch, circuit, P } = ctx;
        const leaf = batch.leafWith({ asset: 7n, val: 150n, ...OWNER, isDeposit: 1 });
        expect(leaf.leaf).to.equal(commit(P, { asset: 7n, value: 150n, ...OWNER }));
        expect(leaf.word, "calldata carries inner, not the commitment").to.equal(inner());
        expect(leaf.word).to.not.equal(leaf.leaf);
        await expectBatchAccepts(circuit, batch.honest(0, [leaf]));
    });

    it("a spend leaf is the word it carries", async () => {
        const { batch, circuit, P } = ctx;
        const leaf = batch.leafWith({ asset: 7n, val: 150n, ...OWNER, isDeposit: 0 });
        expect(leaf.word).to.equal(commit(P, { asset: 7n, value: 150n, ...OWNER }));
        expect(leaf.leaf).to.equal(leaf.word);
        await expectBatchAccepts(circuit, batch.honest(0, [leaf]));
    });

    // ===== the leaf is pinned to the declared pair =====

    it("FAILS on a cross-asset leaf: 1 unit of A declared, 1,000,000 of B inserted", async () => {
        const { batch, circuit, P } = ctx;
        await expectBatchRejects(
            circuit,
            batch.honest(0, [declared(7n, 1n, commitWithInner(P, 99n, 1_000_000n, inner()))]),
            "the leaf must be the commitment over the declared asset and amount",
        );
    });

    it("FAILS on value inflation: 1 unit declared, 2^63 inserted, same asset", async () => {
        const { batch, circuit, P } = ctx;
        await expectBatchRejects(
            circuit,
            batch.honest(0, [declared(7n, 1n, commitWithInner(P, 7n, 1n << 63n, inner()))]),
            "the leaf must be the commitment over the declared amount",
        );
    });

    for (const [field, tamper] of [
        ["leaf_public_in", (l: LeafWitness): LeafWitness => ({ ...l, leafPublicIn: l.leafPublicIn + 1n })],
        ["leaf_asset", (l: LeafWitness): LeafWitness => ({ ...l, leafAsset: l.leafAsset + 1n })],
        ["cms (the depositor's inner)", (l: LeafWitness): LeafWitness => ({ ...l, word: l.word + 1n })],
    ] as const) {
        it(`FAILS when ${field} disagrees with the inserted leaf`, async () => {
            const { batch, circuit } = ctx;
            const honest = batch.leafWith({ asset: 7n, val: 100n, ...OWNER, isDeposit: 1 });
            await expectBatchRejects(
                circuit,
                batch.honest(0, [tamper(honest)]),
                `every input of the leaf hash is bound: ${field}`,
            );
        });
    }

    // ===== packing injectivity: the two range checks =====
    //
    // `asset · 2^64 + value` is injective only while both are below 2^64:
    // (7, 2^64) packs to the same word as (8, 0). Each rejection uses the leaf
    // the circuit would compute for the out-of-range pair, so the hash and
    // `new_root` agree and only the range check can reject.

    it("accepts the in-range reading (asset 8, value 0) of the colliding leaf", async () => {
        const { batch, circuit, P } = ctx;
        const leaf = commitWithInner(P, 8n, 0n, inner());
        expect(leaf).to.equal(leafOverPacked(7n * TWO_64 + TWO_64));
        await expectBatchAccepts(circuit, batch.honest(0, [declared(8n, 0n, leaf)]));
    });

    it("FAILS on leaf_public_in = 2^64, the out-of-range reading of the same leaf", async () => {
        const { batch, circuit } = ctx;
        await expectBatchRejects(
            circuit,
            batch.honest(0, [declared(7n, TWO_64, leafOverPacked(7n * TWO_64 + TWO_64))]),
            "RangeCheck64 on leaf_public_in is what makes the packing injective",
        );
    });

    it("accepts leaf_asset = 2^64 - 1 on a zero-value leaf", async () => {
        const { batch, circuit, P } = ctx;
        const asset = TWO_64 - 1n;
        await expectBatchAccepts(circuit, batch.honest(0, [declared(asset, 0n, commitWithInner(P, asset, 0n, inner()))]));
    });

    it("FAILS on leaf_asset = 2^64, leaf consistent", async () => {
        const { batch, circuit } = ctx;
        await expectBatchRejects(
            circuit,
            batch.honest(0, [declared(TWO_64, 0n, leafOverPacked(TWO_64 * TWO_64))]),
            "RangeCheck64 on leaf_asset must reject an id the contract's uint64 cannot hold",
        );
    });

    it("accepts leaf_public_in = 2^64 - 1", async () => {
        const { batch, circuit } = ctx;
        await expectBatchAccepts(circuit, batch.single({ val: TWO_64 - 1n, isDeposit: 1, asset: 7n }));
    });

    // ===== no value under asset id 0 (step 5) =====
    //
    // SpentNote refuses id 0 on a real note, so a valued leaf there would be
    // committed and unspendable. A zero-value leaf may name any id.

    it("FAILS on a valued deposit leaf at asset 0, leaf consistent", async () => {
        const { batch, circuit } = ctx;
        await expectBatchRejects(
            circuit,
            batch.single({ val: 100n, isDeposit: 1, asset: 0n }),
            "IsZero(leaf_asset) * leaf_public_in === 0 must reject value under id 0",
        );
    });

    it("a zero-value fee note is accepted at asset 0", async () => {
        // Liveness: a zero-fee deposit mints a zero-value fee note under id 0,
        // which `_validateDeposit` permits.
        const { batch, circuit } = ctx;
        const leaves = [
            batch.leaf({ val: 1000n, isDeposit: 1, asset: 7n, pk: 0xf01n }),
            batch.leaf({ val: 0n, isDeposit: 1, asset: 0n, pk: 0xf02n }),
        ];
        await expectBatchAccepts(circuit, batch.honest(0, leaves));
    });

    it("a zero-value deposit leaf is accepted at a non-zero asset", async () => {
        const { batch, circuit } = ctx;
        const leaves = [
            batch.leaf({ val: 1000n, isDeposit: 1, asset: 7n, pk: 0xf03n }),
            batch.leaf({ val: 0n, isDeposit: 1, asset: 7n, pk: 0xf04n }),
        ];
        await expectBatchAccepts(circuit, batch.honest(0, leaves));
    });

    it("FAILS when a zero-value leaf's asset is relabelled after the tree is built", async () => {
        // Relabelling the asset moves the leaf and so `new_root`.
        const { batch, circuit } = ctx;
        const w = batch.honest(0, [
            batch.leaf({ val: 1000n, isDeposit: 1, asset: 7n, pk: 0xf03n }),
            batch.leaf({ val: 0n, isDeposit: 1, asset: 7n, pk: 0xf04n }),
        ]);
        w.leafAsset[1] = 8n;
        rebindFiatShamir(w);
        await expectBatchRejects(circuit, w, "a zero-value leaf's asset still reaches the leaf hash");
    });

    // ===== is_deposit selects how the word becomes a leaf =====
    //
    // The circuit constrains `is_deposit` only to be boolean; which value a slot
    // carries is a contract obligation (header, item 4).

    it("FAILS when a deposit slot's leaf is the raw word", async () => {
        const { batch, circuit } = ctx;
        const honest = batch.leafWith({ asset: 7n, val: 100n, ...OWNER, isDeposit: 1 });
        await expectBatchRejects(
            circuit,
            batch.honest(0, [{ ...honest, leaf: honest.word }]),
            "is_deposit = 1 must insert the hash over the public amount, not the word",
        );
    });

    it("FAILS when a spend slot's leaf is the deposit hash of its word", async () => {
        const { batch, circuit, P } = ctx;
        const honest = batch.leafWith({ asset: 7n, val: 100n, ...OWNER, isDeposit: 0 });
        await expectBatchRejects(
            circuit,
            batch.honest(0, [{ ...honest, leaf: commitWithInner(P, 0n, 0n, honest.word) }]),
            "is_deposit = 0 must insert the word as it stands",
        );
    });

    it("is_deposit set on a spend's cm verifies, and inserts a leaf that is not that cm", async () => {
        // Why the contract must pin is_deposit = 0 on a spend batch: the leaf is
        // the hash of out_cm under (0, 0), which has no opening, so the spend's
        // outputs would be burned.
        const { batch, circuit, P } = ctx;
        const spend = batch.leafWith({ asset: 7n, val: 100n, ...OWNER, isDeposit: 0 });
        const burned: LeafWitness = {
            word: spend.word,
            leaf: commitWithInner(P, 0n, 0n, spend.word),
            leafAsset: 0n,
            leafPublicIn: 0n,
            isDeposit: 1,
        };
        expect(burned.leaf).to.not.equal(spend.leaf);
        await expectBatchAccepts(circuit, batch.honest(0, [burned]));
    });

    it("is_deposit cleared on a deposit's word verifies, and inserts that word unbound", async () => {
        // Why the contract must pin is_deposit = 1 on a deposit batch: with the
        // flag clear the word is the leaf, and a word that is itself a commitment
        // is a note of whatever value it was built for.
        const { batch, circuit, P } = ctx;
        const minted: LeafWitness = {
            word: commitWithInner(P, 7n, 1n << 63n, inner()),
            leaf: commitWithInner(P, 7n, 1n << 63n, inner()),
            leafAsset: 0n,
            leafPublicIn: 0n,
            isDeposit: 0,
        };
        await expectBatchAccepts(circuit, batch.honest(0, [minted]));
    });

    // ===== layout =====

    it("a full flush of four principal/fee pairs, every fee note worthless, passes", async () => {
        const { batch, circuit } = ctx;
        await expectBatchAccepts(circuit, batch.honest(0, batch.depositPairs(MAX_L)));
    });

    it("a deposit leaf at an odd slot needs no relation to its neighbour", async () => {
        // No constraint ties slot k to slot k-1. A cross-asset pair of valued
        // leaves is rejected on-chain by the escrow digest in MASP._drainDeposit.
        const { batch, circuit } = ctx;
        const leaves = [
            batch.leaf({ val: 100n, isDeposit: 1, asset: 7n, pk: 0xf05n }),
            batch.leaf({ val: 25n, isDeposit: 1, asset: 99n, pk: 0xf06n }),
        ];
        await expectBatchAccepts(circuit, batch.honest(0, leaves));
    });

    it("a spend batch carries no deposit field", async () => {
        // In an all-spend batch `leaf_asset` and `leaf_public_in` are forced to
        // zero by steps 1 and 4, so step 5 holds trivially.
        const { batch, circuit } = ctx;
        const leaves = Array.from({ length: 6 }, (_, i) =>
            batch.leaf({ val: BigInt(10 + i), isDeposit: 0, pk: BigInt(0xf20 + i) }));
        await expectBatchAccepts(circuit, batch.honest(0, leaves));
    });
});
