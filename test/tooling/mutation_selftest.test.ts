// Self-test for the mutation fuzzer (`scripts/mutate.ts`). An operator that
// matches nothing, or a gate that runs no spec, yields a campaign with nothing
// to report, so each is checked here against input it must act on.

import { execFileSync } from "child_process";
import * as fs from "fs";
import * as path from "path";

import { expect } from "chai";

import { srcPath } from "../lib/circuit";
import { TIMEOUT_CIRCUIT, TIMEOUT_FAST } from "../lib/constants";
import { repoPath } from "../lib/files";
import { DYNAMIC, specsFor } from "../mutation/campaign";
import { Tier, orderSpecs, orderStages, prioritized, tierOf, type History, type Past } from "../mutation/history";
import { isomorphic } from "../mutation/isomorphic";
import { OPERATORS, calculatorPreserving, splitComments, type Operator } from "../mutation/operators";
import { ROOTS, apply, enumerate, keyOf, readAccepted, shuffled, sourceFiles } from "../mutation/mutants";

function operator(name: string): Operator {
    const op = OPERATORS.find(o => o.name === name);
    if (op === undefined) throw new Error(`no operator "${name}"`);
    return op;
}

/** The mutated text of every variant of `lines[at]`, edits joined by ` | `. */
function variants(name: string, lines: string[], at = 0): string[] {
    return operator(name).mutate(lines, at).map(edits => edits.map(e => e.text.trim()).join(" | "));
}

describe("mutation fuzzer self-test", function () {
    this.timeout(TIMEOUT_FAST);

    describe("operators", () => {
        it("drop-assert deletes a `===` statement and nothing else", () => {
            expect(variants("drop-assert", ["    a * b === 0;"])).to.deep.equal([""]);
            expect(variants("drop-assert", ["    x <== a * b;"])).to.deep.equal([]);
        });

        it("unconstrain turns `<==` into `<--`", () => {
            expect(variants("unconstrain", ["n2b.in <== v;"])).to.deep.equal(["n2b.in <-- v;"]);
        });

        it("const-rhs ties a wire to 0 and to 1, skipping the value it already has", () => {
            expect(variants("const-rhs", ["mp.is_dummy <== is_dummy;"]))
                .to.deep.equal(["mp.is_dummy <== 0;", "mp.is_dummy <== 1;"]);
            expect(variants("const-rhs", ["acc[0] <== 0;"])).to.deep.equal(["acc[0] <== 1;"]);
        });

        it("swap-index moves one index, on the right of `<==` only", () => {
            expect(variants("swap-index", ["a[i].x <== b[i][2];"]))
                .to.deep.equal(["a[i].x <== b[0][2];", "a[i].x <== b[i][3];"]);
            expect(variants("swap-index", ["d[i] * v[i] === 0;"]))
                .to.deep.equal(["d[0] * v[i] === 0;", "d[i] * v[0] === 0;"]);
        });

        it("loop-bound drops the last and the first iteration", () => {
            expect(variants("loop-bound", ["for (var i = 0; i < N; i++) {"])).to.deep.equal([
                "for (var i = 0; i < N - 1; i++) {",
                "for (var i = 0 + 1; i < N; i++) {",
            ]);
        });

        it("flip-gate inverts a `(1 - s)` selector", () => {
            expect(variants("flip-gate", ["(1 - is_dummy) * diff === 0;"]))
                .to.deep.equal(["(is_dummy) * diff === 0;"]);
        });

        it("arith-flip flips one operator and leaves index expressions alone", () => {
            expect(variants("arith-flip", ["lhs[i + 1] <== lhs[i] + t[i];"]))
                .to.deep.equal(["lhs[i + 1] <== lhs[i] - t[i];"]);
        });

        it("const-tweak increments a template argument and a returned constant", () => {
            expect(variants("const-tweak", ["component n2b = Num2Bits(64);"]))
                .to.deep.equal(["component n2b = Num2Bits(65);"]);
            expect(variants("const-tweak", ["function TAG_CM() { return 1; }"]))
                .to.deep.equal(["function TAG_CM() { return 2; }"]);
            expect(variants("const-tweak", ["} = Transact(11, 4, 6);"]), "the shipped shape is not a mutation target")
                .to.deep.equal([]);
        });

        it("cross-wire exchanges the right sides of two adjacent wires", () => {
            expect(variants("cross-wire", ["inner.rho <== rho;", "inner.rcm <== rcm;"]))
                .to.deep.equal(["inner.rho <== rcm; | inner.rcm <== rho;"]);
            expect(variants("cross-wire", ["a <== x;", "b <== x;"])).to.deep.equal([]);
        });
    });

    describe("source handling", () => {
        it("a commented-out statement is not a mutation site", () => {
            const { code, comment } = splitComments("a === b; // why\n// c === d;\n/* e === f;\n g === h; */\ni === j;");
            expect(code.map(c => c.trim())).to.deep.equal(["a === b;", "", "", "", "i === j;"]);
            expect(comment[0]).to.equal("// why");
        });

        it("applying a mutant keeps the line count and the comments", () => {
            const src = srcPath();
            for (const mutant of enumerate(src)) {
                const original = fs.readFileSync(srcPath(mutant.file), "utf8");
                const mutated = apply(original, mutant);
                const before = original.split("\n");
                const after = mutated.split("\n");
                expect(after.length, mutant.id).to.equal(before.length);
                const touched = new Set(mutant.edits.map(e => e.line - 1));
                const changed = after.flatMap((line, i) => (line === before[i] ? [] : [i]));
                expect(changed.length, `${mutant.id} changes nothing`).to.be.greaterThan(0);
                for (const i of changed) expect(touched.has(i), `${mutant.id} changed line ${i + 1}`).to.equal(true);
                expect(splitComments(mutated).comment, mutant.id).to.deep.equal(splitComments(original).comment);
            }
        });
    });

    describe("census over src/", () => {
        const mutants = enumerate(srcPath());

        it("every operator finds statements to mutate", () => {
            for (const op of OPERATORS) {
                expect(mutants.filter(m => m.op === op.name).length, op.name).to.be.greaterThan(0);
            }
        });

        it("every `===` statement has a drop-assert mutant", () => {
            let asserts = 0;
            for (const file of sourceFiles(srcPath()).keys()) {
                const { code } = splitComments(fs.readFileSync(srcPath(file), "utf8"));
                asserts += code.filter(c => c.includes("===")).length;
            }
            expect(asserts, "no `===` found: the scan is reading the wrong tree").to.be.greaterThan(0);
            expect(mutants.filter(m => m.op === "drop-assert").length).to.equal(asserts);
        });

        it("ids and accepted-list keys are unique", () => {
            expect(new Set(mutants.map(m => m.id)).size).to.equal(mutants.length);
            expect(new Set(mutants.map(keyOf)).size).to.equal(mutants.length);
        });

        it("a seed fixes the sample order", () => {
            const ids = (seed: number) => shuffled(mutants, seed).map(m => m.id);
            expect(ids(7)).to.deep.equal(ids(7));
            expect(ids(7)).to.not.deep.equal(ids(8));
            expect([...ids(7)].sort()).to.deep.equal(mutants.map(m => m.id).sort());
        });
    });

    describe("accepted survivors", () => {
        const accepted = readAccepted(repoPath("test", "mutation", "survivors.json"));
        const keys = new Set(enumerate(srcPath()).map(keyOf));

        it("every entry names a mutant src/ still has", () => {
            const gone = accepted.filter(a => !keys.has(keyOf(a)));
            expect(gone.map(a => `${a.file}  ${a.op}:${a.variant}  ${a.source}`), "the statement changed; " +
                "re-run the mutant and drop or re-accept the entry (`just mutate --update --only <id>`)")
                .to.be.empty;
        });

        it("every entry says why no gate can reject it", () => {
            const bare = accepted.filter(a => a.reason.trim() === "");
            expect(bare.map(a => `${a.file}  ${a.op}:${a.variant}  ${a.source}`)).to.be.empty;
        });
    });

    describe("gates", () => {
        it("every dynamic gate has specs for each shipped circuit", () => {
            for (const stage of DYNAMIC) {
                for (const root of ROOTS) {
                    expect(specsFor(stage, [root]), `${stage} for ${root}`).to.not.be.empty;
                }
            }
        });

        it("a spec runs under at most one gate", () => {
            const specs = DYNAMIC.flatMap(stage => specsFor(stage, ROOTS));
            expect(new Set(specs).size).to.equal(specs.length);
        });

        it("the second-witness search runs against each circuit separately", () => {
            const transact = specsFor("sweep", ["4x6"]);
            const batch = specsFor("sweep", ["tree_update_batch"]);
            expect(transact.filter(s => batch.includes(s)), "a sweep spec is shared, so a mutant of one " +
                "circuit pays for the other's search").to.be.empty;
        });
    });

    describe("history", () => {
        const mutants = enumerate(srcPath());
        const [a, b, c] = mutants.filter(m => m.op === "drop-assert");
        const past = (m: typeof a, over: Partial<Past>): Past => ({
            fingerprint: "old", file: m.file, op: m.op, status: "killed", stages: [], matrix: false, outcome: {}, ...over,
        });
        const history = (entries: [typeof a, Partial<Past>][], specMs: Record<string, number> = {}): History => ({
            specMs,
            mutants: Object.fromEntries(entries.map(([m, over]) => [keyOf(m), past(m, over)])),
        });

        it("the spec that rejected a mutant before runs first, then its neighbours', then the cheapest", () => {
            const h = history(
                [[a, { spec: "test/own.test.ts" }], [b, { file: a.file, spec: "test/near.test.ts" }]],
                { "test/slow.test.ts": 900, "test/fast.test.ts": 5 },
            );
            const specs = ["test/slow.test.ts", "test/near.test.ts", "test/fast.test.ts", "test/own.test.ts"];
            expect(orderSpecs(specs, a, h)).to.deep.equal(
                ["test/own.test.ts", "test/near.test.ts", "test/fast.test.ts", "test/slow.test.ts"],
            );
            expect([...orderSpecs(specs, a, h)].sort(), "ordering must not drop a spec").to.deep.equal([...specs].sort());
        });

        it("the gate that rejected a mutant before runs first", () => {
            const h = history([[a, { stage: "sweep" }]]);
            expect(orderStages(["unit", "fuzz", "sweep"], a, h)).to.deep.equal(["sweep", "unit", "fuzz"]);
            expect(orderStages(["unit", "fuzz", "sweep"], b, h)).to.deep.equal(["unit", "fuzz", "sweep"]);
        });

        it("a sample takes weak mutants, then untested ones, then repeats", () => {
            const h = history([
                [a, { status: "survived" }],
                [b, { status: "killed" }],
                [c, { status: "survived", fingerprint: "now" }],
            ]);
            expect(tierOf(a, h, "now")).to.equal(Tier.Weak);
            expect(tierOf(b, h, "now")).to.equal(Tier.Old);
            expect(tierOf(c, h, "now")).to.equal(Tier.Current);
            const order = prioritized(mutants, h, "now", 1).map(m => m.id);
            expect(order[0]).to.equal(a.id);
            expect(order.indexOf(b.id)).to.equal(mutants.length - 2);
            expect(order[mutants.length - 1]).to.equal(c.id);
            expect([...order].sort()).to.deep.equal(mutants.map(m => m.id).sort());
        });

        it("a freed signal that only lint rejects is expected, not a weak spot", () => {
            const freed = mutants.find(m => calculatorPreserving(m.op))!;
            const h = history([[freed, { status: "static" }], [a, { status: "static" }]]);
            expect(tierOf(freed, h, "now")).to.equal(Tier.Old);
            expect(tierOf(a, h, "now")).to.equal(Tier.Weak);
        });
    });

    describe("equivalence proof", function () {
        this.timeout(TIMEOUT_CIRCUIT);

        const dir = repoPath("build", ".mutation-selftest");

        /** Compile a one-template circuit over inputs a, b, c and return its R1CS path. */
        function compile(name: string, body: string[]): string {
            const file = path.join(dir, `${name}.circom`);
            fs.writeFileSync(file, [
                "pragma circom 2.2.3;",
                "template T() {",
                "    signal input a; signal input b; signal input c;",
                "    signal output out;",
                "    signal p; signal q;",
                ...body.map(line => `    ${line}`),
                "}",
                "component main = T();",
                "",
            ].join("\n"));
            execFileSync("circom", [file, "--r1cs", "-o", dir], { stdio: "ignore" });
            return path.join(dir, `${name}.r1cs`);
        }

        before(() => {
            fs.rmSync(dir, { recursive: true, force: true });
            fs.mkdirSync(dir, { recursive: true });
        });

        it("proves a circuit equivalent to itself with two signals renamed", async () => {
            const original = compile("original", ["p <== a * b;", "q <== b * c;", "out <== p * q + p;"]);
            const renamed = compile("renamed", ["q <== a * b;", "p <== b * c;", "out <== q * p + q;"]);
            expect(fs.readFileSync(original).equals(fs.readFileSync(renamed)),
                "the two files are identical, so the renaming is not being tested").to.equal(false);
            expect((await isomorphic(original, renamed)).isomorphic).to.equal(true);
        });

        it("refuses a circuit that differs in one term", async () => {
            const original = compile("original", ["p <== a * b;", "q <== b * c;", "out <== p * q + p;"]);
            const changed = compile("changed", ["p <== a * b;", "q <== b * c;", "out <== p * q + q;"]);
            expect((await isomorphic(original, changed)).isomorphic).to.equal(false);
        });

        it("refuses a renaming that would move an input", async () => {
            const original = compile("original", ["p <== a * b;", "q <== b * c;", "out <== p * q + p;"]);
            const moved = compile("moved", ["p <== c * b;", "q <== b * a;", "out <== p * q + p;"]);
            expect((await isomorphic(original, moved)).isomorphic).to.equal(false);
        });

        it("identifies an input by label when another input has no wire", async () => {
            // `c` is unread in both; in `shifted` so is `a`, which moves `b` down a wire.
            const original = compile("unread", ["p <== a * b;", "q <== b * b;", "out <== p * q;"]);
            const shifted = compile("shifted", ["p <== b * b;", "q <== b * b;", "out <== p * q;"]);
            expect((await isomorphic(original, shifted)).isomorphic).to.equal(false);
        });

        it("pairs signals refinement cannot tell apart", async () => {
            const twins = compile("twins", ["p <== a * b;", "q <== a * b;", "out <== p + q + c;"]);
            const verdict = await isomorphic(twins, twins);
            expect(verdict.isomorphic).to.equal(true);
            expect(verdict.reason, "p and q are interchangeable; if no choice was needed the " +
                "fixture no longer exercises that path").to.match(/[1-9]\d* choice/);
        });
    });
});
