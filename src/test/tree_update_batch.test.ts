// Tests for `tree_update_batch.circom`. Mirrors the contract's
// _compressTreeUpdateBatchPI flatten order:
//   [old_root, new_root, start_index, actual_count, cms[0..2*MAX_N-1]]
//
// MAX_N = 16 ⇒ 32 leaves max. Each pair = 2 QuaternaryInsert(10) so a full
// batch is heavy. Tests stay at small actual_count for runtime; one larger
// case verifies the multiplex logic across several active pairs.

import { Poseidon, MerkleTree, type Field } from "./helpers";
import { fiatShamirZ, hornerEval } from "@lelantos-org/sdk";
import { loadCircuit, srcPath } from "./lib/circuit";
import { treeUpdateBatchInputJson, flattenTreeUpdateBatch } from "./lib/inputs";
import { expectWitnessFails } from "./lib/expect";

const DEPTH = 10;
const MAX_N = 16;
const SLOTS = 2 * MAX_N;
const WRAPPER = srcPath("tree_update_batch.circom");

function padCms(real: Field[]): Field[] {
    if (real.length > SLOTS) throw new Error("too many leaves");
    const out = real.slice();
    while (out.length < SLOTS) out.push(0n);
    return out;
}

function buildHonest(P: Poseidon, prefilled: number, real: Field[]) {
    if (real.length % 2 !== 0) throw new Error("real leaves must come in pairs");
    const tree = new MerkleTree(P, DEPTH);
    for (let i = 0; i < prefilled; i++) tree.insert(BigInt(0xdead + i));
    const oldRoot = tree.root();
    const frontier = tree.frontier();

    for (const cm of real) tree.insert(cm);
    const newRoot = tree.root();

    const startIndex = prefilled;
    const actualCount = real.length / 2;
    const cms = padCms(real);
    const coeffs = flattenTreeUpdateBatch({ oldRoot, newRoot, startIndex, actualCount, cms });
    const z = fiatShamirZ(coeffs);
    const y = hornerEval(coeffs, z);

    return { oldRoot, newRoot, startIndex, actualCount, cms, frontier, z, y };
}

describe("tree_update_batch", function () {
    this.timeout(900000);

    let circuit: any;
    let P: Poseidon;

    before(async () => {
        P = await Poseidon.build();
        circuit = await loadCircuit(WRAPPER);
    });

    it("single active pair (actual_count=1) at start_index=0 proves", async () => {
        const w = buildHonest(P, 0, [0x11n, 0x22n]);
        const witness = await circuit.calculateWitness(treeUpdateBatchInputJson(w), true);
        await circuit.checkConstraints(witness);
        await circuit.assertOut(witness, { y: w.y.toString() });
    });

    it("single active pair at non-zero start_index (mid-tree) proves", async () => {
        const w = buildHonest(P, 17, [0xaaa1n, 0xaaa2n]);
        const witness = await circuit.calculateWitness(treeUpdateBatchInputJson(w), true);
        await circuit.checkConstraints(witness);
        await circuit.assertOut(witness, { y: w.y.toString() });
    });

    it("4 active pairs (8 leaves) proves and yields correct y", async () => {
        const real: Field[] = [];
        for (let i = 0; i < 8; i++) real.push(BigInt(0xc0de + i));
        const w = buildHonest(P, 5, real);
        const witness = await circuit.calculateWitness(treeUpdateBatchInputJson(w), true);
        await circuit.checkConstraints(witness);
        await circuit.assertOut(witness, { y: w.y.toString() });
    });

    it("full batch (actual_count = MAX_N) proves", async () => {
        const real: Field[] = [];
        for (let i = 0; i < 2 * MAX_N; i++) real.push(BigInt(0xbeef00 + i));
        const w = buildHonest(P, 3, real);
        const witness = await circuit.calculateWitness(treeUpdateBatchInputJson(w), true);
        await circuit.checkConstraints(witness);
        await circuit.assertOut(witness, { y: w.y.toString() });
    });

    it("FAILS on wrong new_root (binding check)", async () => {
        const w = buildHonest(P, 0, [0x11n, 0x22n]);
        const tampered = { ...w, newRoot: w.newRoot ^ 1n };
        // Recompute z/y over tampered coeffs so PolyEval still binds; failure
        // must come from running_root === new_root, not the y check.
        const coeffs = flattenTreeUpdateBatch(tampered);
        const z = fiatShamirZ(coeffs);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson({ ...tampered, z }),
            "expected wrong new_root to fail",
        );
    });

    it("FAILS when padding slot has non-zero cm", async () => {
        const w = buildHonest(P, 0, [0x11n, 0x22n]);   // actual_count=1 ⇒ slots [2..] must be 0
        const cms = w.cms.slice();
        cms[2] = 0x999n;                                 // poison padding
        const coeffs = flattenTreeUpdateBatch({ ...w, cms });
        const z = fiatShamirZ(coeffs);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson({ ...w, cms, z }),
            "expected non-zero padding to fail",
        );
    });

    it("FAILS when actual_count = 0 (range check, lower bound)", async () => {
        const w = buildHonest(P, 0, [0x11n, 0x22n]);
        // actual_count=0 ⇒ Num2Bits(4) on (0-1) = -1 = p-1 → fails range check.
        // To stay self-consistent on the y-side, pretend the batch was empty:
        // newRoot == oldRoot, all cms = 0.
        const empty = {
            oldRoot: w.oldRoot,
            newRoot: w.oldRoot,
            startIndex: w.startIndex,
            actualCount: 0n,
            cms: padCms([]),
            frontier: w.frontier,
        };
        const coeffs = flattenTreeUpdateBatch(empty);
        const z = fiatShamirZ(coeffs);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson({ ...empty, z }),
            "expected actual_count=0 to fail range check",
        );
    });

    it("FAILS when actual_count > MAX_N (range check, upper bound)", async () => {
        const w = buildHonest(P, 0, [0x11n, 0x22n]);
        const bad = { ...w, actualCount: BigInt(MAX_N + 1) };
        const coeffs = flattenTreeUpdateBatch(bad);
        const z = fiatShamirZ(coeffs);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson({ ...bad, z }),
            "expected actual_count > MAX_N to fail",
        );
    });

    it("FAILS when start_index + 2*MAX_N - 1 overflows 2*DEPTH bits", async () => {
        // 4^DEPTH = 1048576 leaves total. Pick start_index near the top so
        // the last index doesn't fit in 2*DEPTH bits.
        const startIndex = (4 ** DEPTH) - 5;             // last idx = startIndex + 31 > 4^DEPTH
        const tree = new MerkleTree(P, DEPTH);
        const oldRoot = tree.root();
        const frontier = tree.frontier();
        const cms = padCms([0x1n, 0x2n]);
        const args = {
            oldRoot, newRoot: oldRoot,
            startIndex, actualCount: 1n, cms, frontier,
        };
        const coeffs = flattenTreeUpdateBatch(args);
        const z = fiatShamirZ(coeffs);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson({ ...args, z }),
            "expected oob start_index to fail Num2Bits(2*DEPTH)",
        );
    });

    it("FAILS on tampered frontier (running_root ≠ new_root)", async () => {
        const w = buildHonest(P, 17, [0xaaa1n, 0xaaa2n]);
        const frontier = w.frontier.map(lvl => lvl.slice());
        frontier[0][0] = (frontier[0][0] + 1n);
        await expectWitnessFails(
            circuit,
            treeUpdateBatchInputJson({ ...w, frontier }),
            "expected tampered frontier to fail",
        );
    });

    it("FAILS when y output doesn't match coeffs", async () => {
        const w = buildHonest(P, 0, [0x11n, 0x22n]);
        const witness = await circuit.calculateWitness(treeUpdateBatchInputJson(w), true);
        let threw = false;
        try {
            await circuit.assertOut(witness, { y: (w.y + 1n).toString() });
        } catch {
            threw = true;
        }
        if (!threw) throw new Error("expected wrong y to be rejected");
    });

    it("padding-only trailing pair (active=1 then non-active) carries root unchanged for inactive slots", async () => {
        // Build an honest 2-pair batch, then re-build expected y with the same
        // coeffs to confirm: inactive[i] mux must keep running_root constant.
        const real: Field[] = [0x10n, 0x20n, 0x30n, 0x40n];
        const w = buildHonest(P, 0, real);
        const witness = await circuit.calculateWitness(treeUpdateBatchInputJson(w), true);
        await circuit.checkConstraints(witness);
        await circuit.assertOut(witness, { y: w.y.toString() });
    });
});
