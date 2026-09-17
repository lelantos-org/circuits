// Unit tests for `lib/batch_append.circom`: both roots, the activity prefix and
// the range checks of the tree inside `tree_update_batch`.
//
// Every leaf is distinct, so a child wired from the wrong frontier slot or the
// wrong window node changes a root. Depth 4 has window widths 8, 3, 2, 2, 1 —
// every width class the DEPTH = 11 shape uses — and is small enough to sweep
// every start_index against every count. Depth 2 adds the case where the tree,
// not MAX_L, caps the top window. The straddle cases in
// `batch/shapes.test.ts` check the full circuit at production depth.

import { expect } from "chai";

import { MerkleTree, quatDigit, type Field, type Poseidon } from "../helpers";
import { representativeStarts } from "../lib/batch";
import { generatedFixture } from "../lib/circuit";
import { expectWitnessFails, readOutput } from "../lib/expect";
import { ARITY, MAX_L, TIMEOUT_HEAVY } from "../lib/constants";
import { useCircuit } from "../lib/harness";

/** Honest roots and frontiers after every prefix of one distinct-leaf sequence. */
interface Timeline {
    leaves: Field[];
    roots: Field[];
    frontiers: Field[][][];
}

function timeline(P: Poseidon, depth: number): Timeline {
    const capacity = ARITY ** depth;
    const tree = new MerkleTree(P, depth);
    const leaves: Field[] = [];
    const roots: Field[] = [tree.root()];
    const frontiers: Field[][][] = [tree.frontier()];
    for (let i = 0; i < capacity; i++) {
        const leaf = BigInt(0x1eaf00 + i);
        leaves.push(leaf);
        tree.insert(leaf);
        roots.push(tree.root());
        frontiers.push(tree.frontier());
    }
    return { leaves, roots, frontiers };
}

/**
 * Circuit input for `count` leaves at `start`. Slots past `count` carry distinct
 * non-zero junk, so a slot the gadget fails to zero would move the root.
 */
function batchInput(t: Timeline, start: number, count: number, frontier = t.frontiers[start]) {
    const slots = Array.from({ length: MAX_L }, (_, k) =>
        k < count ? t.leaves[start + k] : BigInt(0xbad000 + k));
    return {
        start_index: start.toString(),
        actual_count: count.toString(),
        leaves: slots.map(String),
        frontier_in: frontier.map(lvl => lvl.map(String)),
    };
}

/** A copy of `frontier` with slot `[d][k]` replaced by `f` of its value. */
function withSlot(frontier: Field[][], d: number, k: number, f: (v: Field) => Field): Field[][] {
    const out = frontier.map(lvl => lvl.slice());
    out[d][k] = f(out[d][k]);
    return out;
}

for (const depth of [2, 4]) {
    const capacity = ARITY ** depth;

    describe(`BatchAppend (depth ${depth}, MAX_L ${MAX_L}, distinct leaves)`, function () {
        this.timeout(TIMEOUT_HEAVY);

        const ctx = useCircuit(generatedFixture("lib/batch_append.circom", "BatchAppend", [depth, MAX_L]));
        const representative = new Set(representativeStarts(depth));
        let t: Timeline;

        before(() => {
            t = timeline(ctx.P, depth);
        });

        it("every start_index and every count reproduces both reference roots and the prefix", async () => {
            for (let start = 0; start < capacity; start++) {
                const full = Math.min(MAX_L, capacity - start);
                for (let count = 1; count <= full; count++) {
                    const w = await ctx.circuit.calculateWitness(batchInput(t, start, count), true);
                    // The witness calculator already evaluates every constraint; the R1CS
                    // check guards the compiled system itself, so a sample is enough.
                    if (count === full && representative.has(start)) {
                        await ctx.circuit.checkConstraints(w);
                    }
                    const at = `start=${start} count=${count}`;
                    expect(readOutput(w, 0), `${at}: old_root`).to.equal(t.roots[start]);
                    expect(readOutput(w, 1), `${at}: new_root`).to.equal(t.roots[start + count]);
                    for (let k = 0; k < MAX_L; k++) {
                        expect(readOutput(w, 2 + k), `${at}: active[${k}]`)
                            .to.equal(k < count ? 1n : 0n);
                    }
                }
            }
        });

        it("a frontier slot below the digit moves both roots", async () => {
            // Both roots read every filled slot: moving only one would mean a
            // slot is wired into one root and not the other.
            let checked = 0;
            for (const start of representative) {
                const count = Math.min(MAX_L, capacity - start);
                for (let d = 0; d < depth; d++) {
                    for (let k = 0; k < quatDigit(start, d); k++) {
                        const tampered = withSlot(t.frontiers[start], d, k, v => v + 1n);
                        const w = await ctx.circuit.calculateWitness(
                            batchInput(t, start, count, tampered), true);
                        const at = `start=${start} frontier[${d}][${k}]`;
                        expect(readOutput(w, 0), `${at}: old_root`).to.not.equal(t.roots[start]);
                        expect(readOutput(w, 1), `${at}: new_root`).to.not.equal(t.roots[start + count]);
                        checked++;
                    }
                }
            }
            expect(checked).to.be.greaterThan(0);
        });

        it("FAILS on a non-zero frontier slot at or above the digit", async () => {
            // Slots neither root reads are pinned to zero, so the witness has no
            // free frontier signal. The pin depends only on each level's digit,
            // not on the count.
            let checked = 0;
            for (const start of representative) {
                for (let d = 0; d < depth; d++) {
                    for (let k = quatDigit(start, d); k < 3; k++) {
                        const tampered = withSlot(t.frontiers[start], d, k, () => 1n);
                        await expectWitnessFails(
                            ctx.circuit,
                            batchInput(t, start, 1, tampered),
                            `start=${start}: unread frontier[${d}][${k}] must be pinned to zero`,
                        );
                        checked++;
                    }
                }
            }
            expect(checked).to.be.greaterThan(0);
        });

        it("swapping two filled frontier slots moves both roots", async () => {
            // The last index of the tree has digit 3 at every level, so all three
            // slots at level 0 are filled and distinct.
            const start = capacity - 1;
            const swapped = t.frontiers[start].map(lvl => lvl.slice());
            [swapped[0][0], swapped[0][1]] = [swapped[0][1], swapped[0][0]];
            const w = await ctx.circuit.calculateWitness(batchInput(t, start, 1, swapped), true);
            expect(readOutput(w, 0)).to.not.equal(t.roots[start]);
            expect(readOutput(w, 1)).to.not.equal(t.roots[start + 1]);
        });

        for (const count of [0, MAX_L + 1]) {
            it(`FAILS when actual_count = ${count} (Num2Bits(COUNT_BITS) on actual_count - 1)`, async () => {
                const input = batchInput(t, 0, 1);
                input.actual_count = count.toString();
                await expectWitnessFails(ctx.circuit, input, `actual_count = ${count} must reject`);
            });
        }

        it("FAILS when start_index is outside the tree (Num2Bits(2·DEPTH))", async () => {
            const input = batchInput(t, 0, 1);
            input.start_index = capacity.toString();
            await expectWitnessFails(ctx.circuit, input, "start_index = 4^DEPTH must reject");
        });

        it("FAILS when the batch runs past the end of the tree", async () => {
            const input = batchInput(t, capacity - 1, 1);
            input.actual_count = "2";
            input.leaves[1] = "7";
            await expectWitnessFails(
                ctx.circuit,
                input,
                "Num2Bits(2·DEPTH) on start_index + actual_count - 1 must reject",
            );
        });
    });
}
