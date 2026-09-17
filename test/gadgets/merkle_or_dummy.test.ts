// Unit tests for the two merkle helpers the full circuit only exercises
// indirectly: `MerkleProofOrDummy` (lib/merkle.circom) and
// `PathIndexSelectors` (lib/common.circom).
//
// `MerkleProofOrDummy` is the dummy-slot bypass: `is_dummy = 1` drops the
// membership equality so a padding input needs no real note. In `transact_4x6`
// every case that reaches it also carries the pk, asset and value constraints
// `SpentNote` layers on top, so a bypass that leaked — or one that fired on a
// real slot — would be attributed to one of those instead. Depth 2 isolates it.
//
// `PathIndexSelectors` turns a quaternary digit into the one-hot selector
// `MerkleLevel4` routes with. `gadgets/merkle.test.ts` covers the routing it
// feeds; the selector algebra itself (one-hot, sums to one, rejects 4) is here.

import { expect } from "chai";

import { MerkleTree, type Field } from "../helpers";
import { generatedFixture, readOutput } from "../lib/circuit";
import { expectAccepts, expectWitnessFails } from "../lib/expect";
import { merkleInputJson } from "../lib/inputs";
import { ARITY, TIMEOUT_CIRCUIT } from "../lib/constants";
import { useCircuit } from "../lib/harness";

const DEPTH = 2;

describe("MerkleProofOrDummy (dummy-slot bypass)", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useCircuit(generatedFixture("lib/merkle.circom", "MerkleProofOrDummy", [DEPTH]));

    interface Honest {
        leaf: Field;
        pathElements: Field[][];
        pathIndices: number[];
        root: Field;
    }

    let honest: Honest;
    /** A path of the right shape that authenticates nothing. */
    let garbage: Pick<Honest, "pathElements" | "pathIndices">;

    before(() => {
        const tree = new MerkleTree(ctx.P, DEPTH);
        const leaves = Array.from({ length: 16 }, (_, i) => BigInt(0x100 + i));
        for (const leaf of leaves) tree.insert(leaf);
        const { pathElements, pathIndices } = tree.proof(5);
        honest = { leaf: leaves[5], pathElements, pathIndices, root: tree.root() };
        garbage = {
            pathElements: Array.from({ length: DEPTH }, (_, d) =>
                Array.from({ length: ARITY - 1 }, (_, k) => BigInt(0xbad0000 + d * 16 + k))),
            pathIndices: [1, 2],
        };
    });

    function input(o: {
        leaf?: Field;
        path?: Pick<Honest, "pathElements" | "pathIndices">;
        root?: Field;
        isDummy: bigint;
    }) {
        const path = o.path ?? honest;
        return {
            ...merkleInputJson(o.leaf ?? honest.leaf, path.pathElements, path.pathIndices),
            root: (o.root ?? honest.root).toString(),
            is_dummy: o.isDummy.toString(),
        };
    }

    it("accepts a real membership proof", async () => {
        await expectAccepts(ctx.circuit, input({ isDummy: 0n }));
    });

    it("FAILS on a path that does not recompute the declared root", async () => {
        await expectWitnessFails(
            ctx.circuit,
            input({ path: garbage, isDummy: 0n }),
            "a real slot must prove membership",
        );
    });

    it("FAILS on a perturbed sibling", async () => {
        const perturbed = {
            pathElements: honest.pathElements.map(lvl => lvl.slice()),
            pathIndices: honest.pathIndices,
        };
        perturbed.pathElements[0][0] += 1n;
        await expectWitnessFails(
            ctx.circuit,
            input({ path: perturbed, isDummy: 0n }),
            "one wrong sibling must break the recomputation",
        );
    });

    it("FAILS when the declared root is not the tree's", async () => {
        await expectWitnessFails(
            ctx.circuit,
            input({ root: honest.root + 1n, isDummy: 0n }),
            "the recomputed root must equal the declared one",
        );
    });

    it("bypasses the check entirely at is_dummy = 1", async () => {
        // Garbage path, garbage leaf, garbage root: a padding slot carries no
        // note, so nothing about it is authenticated. `DummyZeroValue` is what
        // keeps such a slot from contributing value, and `SpentNote` still
        // emits a real nullifier for it.
        await expectAccepts(ctx.circuit, input({
            leaf: 0xdead_beefn,
            path: garbage,
            root: 0xfeedn,
            isDummy: 1n,
        }));
    });

    it("accepts a real proof marked dummy", async () => {
        await expectAccepts(ctx.circuit, input({ isDummy: 1n }));
    });

    for (const bad of [2n, 3n]) {
        it(`FAILS when is_dummy is ${bad}`, async () => {
            // Without the booleanity constraint, is_dummy = k scales `diff` by
            // (1 - k), which a prover could solve for any diff.
            await expectWitnessFails(
                ctx.circuit,
                input({ path: garbage, isDummy: bad }),
                "is_dummy * (is_dummy - 1) === 0 must reject a non-boolean flag",
            );
        });
    }
});

describe("PathIndexSelectors (quaternary digit to one-hot)", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ctx = useCircuit(generatedFixture("lib/common.circom", "PathIndexSelectors", []));

    /** Outputs are `bits[2]` then `s[4]`, in declaration order. */
    async function selectors(index: number): Promise<{ bits: bigint[]; s: bigint[] }> {
        const w = await ctx.circuit.calculateWitness({ path_index: index.toString() }, true);
        await ctx.circuit.checkConstraints(w);
        return {
            bits: [readOutput(w, 0), readOutput(w, 1)],
            s: [readOutput(w, 2), readOutput(w, 3), readOutput(w, 4), readOutput(w, 5)],
        };
    }

    it("is one-hot at the digit, for every digit", async () => {
        for (let index = 0; index < ARITY; index++) {
            const { bits, s } = await selectors(index);
            expect(bits, `bits at ${index}`).to.deep.equal([
                BigInt(index & 1),
                BigInt((index >> 1) & 1),
            ]);
            expect(s, `selectors at ${index}`).to.deep.equal(
                Array.from({ length: ARITY }, (_, k) => (k === index ? 1n : 0n)),
            );
        }
    });

    it("sums to one, so exactly one child slot is selected", async () => {
        for (let index = 0; index < ARITY; index++) {
            const { s } = await selectors(index);
            expect(s.reduce((a, b) => a + b, 0n), `Σs at ${index}`).to.equal(1n);
        }
    });

    for (const bad of [4n, 5n, 1n << 32n]) {
        it(`FAILS at path_index = ${bad}`, async () => {
            await expectWitnessFails(
                ctx.circuit,
                { path_index: bad.toString() },
                "Num2Bits(2) must reject a digit outside 0..3",
                { template: "Num2Bits" },
            );
        });
    }
});
