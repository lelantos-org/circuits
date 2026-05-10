// Unit tests for `lib/frontier_root.circom` — the H-1 fix template that
// binds `frontier_in` to `old_root` inside `tree_update_batch`.
//
// Uses a depth-3 wrapper (4^3 = 64 leaves) so every per-level digit slot
// (0..3) at every level (0..2) can be exercised cheaply. Soundness
// extends to depth 10 by induction.

import { expect } from "chai";

import { Poseidon, MerkleTree, type Field } from "./helpers";
import { fixturePath, loadCircuit } from "./lib/circuit";
import { expectWitnessFails } from "./lib/expect";

const DEPTH = 3;
const CAPACITY = 4 ** DEPTH;   // 64
const WRAPPER = fixturePath("test_frontier_root_d3.circom");

function frontierInputJson(startIndex: number | bigint, frontier: Field[][]) {
    return {
        start_index: startIndex.toString(),
        frontier_in: frontier.map(lvl => lvl.map(s => s.toString())),
    };
}

/// Build a tree with `n` deterministic leaves and return (root, frontier).
function honestState(P: Poseidon, n: number): { root: Field; frontier: Field[][] } {
    const tree = new MerkleTree(P, DEPTH);
    for (let i = 0; i < n; i++) tree.insert(BigInt(0xc0de + i));
    return { root: tree.root(), frontier: tree.frontier() };
}

describe("FrontierRoot (depth 3, lazy-root rebuild)", function () {
    this.timeout(180000);

    let circuit: any;
    let P: Poseidon;

    before(async () => {
        P = await Poseidon.build();
        circuit = await loadCircuit(WRAPPER);
    });

    // ===== Happy-path equivalence with SDK MerkleTree =====

    it("empty tree: start_index=0 with zero frontier reproduces empty root", async () => {
        const { root, frontier } = honestState(P, 0);
        const w = await circuit.calculateWitness(frontierInputJson(0, frontier), true);
        await circuit.checkConstraints(w);
        await circuit.assertOut(w, { root: root.toString() });
    });

    /// Every digit slot at every level: N spans 1, 4, 16 (single-slot at
    /// each level), plus 5, 9, 22, 63 (multi-level partials) and 64
    /// (full — handled separately since start_index=64 overflows 2*DEPTH=6
    /// bits). The selector spread guarantees pre/eq/post are each touched
    /// at every level across the table.
    const checkpoints = [0, 1, 2, 3, 4, 5, 7, 13, 16, 17, 22, 33, 47, 60, 63];
    for (const n of checkpoints) {
        it(`honest N=${n} (digits ${digitsOf(n, DEPTH)}) matches SDK root`, async () => {
            const { root, frontier } = honestState(P, n);
            const w = await circuit.calculateWitness(frontierInputJson(n, frontier), true);
            await circuit.checkConstraints(w);
            await circuit.assertOut(w, { root: root.toString() });
        });
    }

    it("fuzz: 20 random N ∈ [0, 64) match SDK root", async () => {
        for (let trial = 0; trial < 20; trial++) {
            const n = Math.floor(Math.random() * CAPACITY);
            const { root, frontier } = honestState(P, n);
            const w = await circuit.calculateWitness(frontierInputJson(n, frontier), true);
            await circuit.assertOut(w, { root: root.toString() });
        }
    });

    // ===== Negative coverage =====

    it("rejects tampered frontier sibling (mid-level)", async () => {
        const { frontier } = honestState(P, 22);
        // 22 ⇒ digits [2,1,1]; frontier[0][0] and [0][1] are real filled
        // siblings. Bump one ⇒ rebuild root diverges.
        frontier[0][1] = frontier[0][1] + 1n;
        const { root } = honestState(P, 22);  // honest expected root
        const w = await circuit.calculateWitness(frontierInputJson(22, frontier), true);
        const out = await readRoot(circuit, w);
        expect(out).to.not.equal(root, "rebuild should diverge under tamper");
    });

    it("blank frontier with non-zero N diverges from real root", async () => {
        // Forge attempt: relayer claims start_index = 16 but supplies an
        // all-zero frontier. Rebuild yields a root unrelated to the real
        // 16-leaf state, so the downstream `old_root === frontier_root.root`
        // equality in tree_update_batch rejects the proof.
        const blank: Field[][] = [];
        for (let d = 0; d < DEPTH; d++) blank.push([0n, 0n, 0n]);
        const { root: realRoot } = honestState(P, 16);
        const w = await circuit.calculateWitness(frontierInputJson(16, blank), true);
        const out = await readRoot(circuit, w);
        expect(out).to.not.equal(realRoot, "rebuild from blank frontier ≠ real root");
    });

    it("FAILS when start_index ≥ 2^(2·DEPTH) (Num2Bits range check)", async () => {
        // start_index = 64 ⇒ 7-bit value; wrapper Num2Bits(6) rejects.
        const { frontier } = honestState(P, 0);
        await expectWitnessFails(() => circuit.calculateWitness(frontierInputJson(64, frontier), true));
    });

    it("swapping two frontier slots at the same level perturbs the root", async () => {
        const { frontier, root } = honestState(P, 47);  // digits [3,2,2]
        // Swap frontier[0][0] and frontier[0][1] (both real fills at lvl 0).
        const tampered = frontier.map(lvl => [...lvl]);
        [tampered[0][0], tampered[0][1]] = [tampered[0][1], tampered[0][0]];
        const w = await circuit.calculateWitness(frontierInputJson(47, tampered), true);
        const out = await readRoot(circuit, w);
        expect(out).to.not.equal(root, "permuted siblings change Poseidon image");
    });
});

// ---- helpers --------------------------------------------------------------

function digitsOf(n: number, depth: number): number[] {
    const out: number[] = [];
    let x = n;
    for (let i = 0; i < depth; i++) {
        out.push(x % 4);
        x = Math.floor(x / 4);
    }
    return out;
}

/// circom_tester stores outputs in the witness vector. Output `root` is
/// signal index 1 (after the constant 1 at index 0).
async function readRoot(circuit: any, witness: bigint[]): Promise<Field> {
    // circom_tester sets witness[1] = first output for `component main` with
    // no public inputs (output `root`).
    return witness[1];
}
