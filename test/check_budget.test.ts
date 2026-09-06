import { execFileSync } from "child_process";
import * as fs from "fs";
import * as path from "path";
import { fileURLToPath } from "url";

import { expect } from "chai";

import { TIMEOUT_CIRCUIT } from "./lib/constants";
// @ts-ignore - snarkjs ships without types
import * as snarkjs from "snarkjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const CIRCUITS = path.join(__dirname, "..");
const SCRIPT = path.join(CIRCUITS, "scripts", "check-budget.mjs");

// Coverage for the constraint-budget gate, which keeps a per-slot gadget change
// from pushing tree_update_batch out of its 2^17 FFT domain.
//
// Each case builds a throwaway root laid out the way the script expects
// (<root>/scripts, <root>/build, <root>/src, <root>/budget.json) and runs the
// real script against it. The root lives under build/ rather than /tmp so that
// Node's upward module resolution still finds circuits/node_modules for snarkjs.
describe("check-budget.mjs", function () {
    this.timeout(TIMEOUT_CIRCUIT);

    const ROOT = path.join(CIRCUITS, "build", ".budget-test");
    const SCRATCH = path.join(CIRCUITS, "build", ".budget-test-fixture");
    const R1CS = path.join(SCRATCH, "tiny.r1cs");
    let actualConstraints: number;
    /** nConstraints + nPubInputs + nOutputs — what snarkjs sizes the domain from. */
    let sizedSignals: number;

    // Compiles a throwaway circuit rather than reading a production artifact:
    // the test job never runs the production compile, so depending on one would
    // make these cases skip in CI.
    before(async function () {
        fs.rmSync(SCRATCH, { recursive: true, force: true });
        fs.mkdirSync(SCRATCH, { recursive: true });
        const src = path.join(SCRATCH, "tiny.circom");
        fs.writeFileSync(
            src,
            [
                "pragma circom 2.2.3;",
                "template Tiny() {",
                "    signal input a;",
                "    signal output c;",
                "    signal b;",
                "    b <== a * a;",
                "    c <== b * a;",
                "}",
                "component main = Tiny();",
                "",
            ].join("\n"),
        );
        execFileSync("circom", [src, "--r1cs", "-o", SCRATCH, "-l", path.join(CIRCUITS, "node_modules")], {
            stdio: "ignore",
        });
        const info = await snarkjs.r1cs.info(R1CS);
        actualConstraints = info.nConstraints;
        sizedSignals = info.nConstraints + info.nPubInputs + info.nOutputs;
    });

    after(() => {
        fs.rmSync(SCRATCH, { recursive: true, force: true });
    });

    afterEach(() => {
        fs.rmSync(ROOT, { recursive: true, force: true });
    });

    /**
     * Lay out a fake circuits root. `sourceOffsetMs` shifts the .circom mtime
     * relative to the r1cs, which is what the staleness check reads: positive
     * means sources are newer, i.e. the artifact is stale.
     */
    function scaffold(budget: unknown, opts: { sourceOffsetMs?: number; withR1cs?: boolean; testFixture?: boolean } = {}) {
        const { sourceOffsetMs = -1000, withR1cs = true, testFixture = false } = opts;

        fs.mkdirSync(path.join(ROOT, "scripts"), { recursive: true });
        fs.mkdirSync(path.join(ROOT, "build"), { recursive: true });
        fs.mkdirSync(path.join(ROOT, "src", "lib"), { recursive: true });
        fs.copyFileSync(SCRIPT, path.join(ROOT, "scripts", "check-budget.mjs"));
        fs.writeFileSync(path.join(ROOT, "budget.json"), JSON.stringify(budget, null, 2) + "\n");

        if (withR1cs) fs.copyFileSync(R1CS, path.join(ROOT, "build", "2x2.r1cs"));

        const r1csMtime = withR1cs ? fs.statSync(path.join(ROOT, "build", "2x2.r1cs")).mtimeMs : Date.now();
        const stamp = (file: string) => {
            fs.writeFileSync(file, "pragma circom 2.2.3;\n");
            const t = (r1csMtime + sourceOffsetMs) / 1000;
            fs.utimesSync(file, t, t);
        };
        stamp(path.join(ROOT, "src", "lib", "thing.circom"));
        if (testFixture) {
            fs.mkdirSync(path.join(ROOT, "src", "test", "fixtures"), { recursive: true });
            const fixture = path.join(ROOT, "src", "test", "fixtures", "fix.circom");
            fs.writeFileSync(fixture, "pragma circom 2.2.3;\n");
            const t = (r1csMtime + 60_000) / 1000; // newer than the artifact
            fs.utimesSync(fixture, t, t);
        }
    }

    function run(...args: string[]): { code: number; out: string } {
        try {
            const out = execFileSync("node", [path.join(ROOT, "scripts", "check-budget.mjs"), ...args], {
                encoding: "utf8",
                stdio: ["ignore", "pipe", "pipe"],
            });
            return { code: 0, out };
        } catch (e: any) {
            return { code: e.status ?? 1, out: `${e.stdout ?? ""}${e.stderr ?? ""}` };
        }
    }

    const budgetWith = (constraints: number, domain: number) => ({
        circuits: { "2x2": { constraints, domain } },
    });

    it("passes when the count matches and fits the domain", () => {
        scaffold(budgetWith(actualConstraints, 65536));
        const { code, out } = run();
        expect(out).to.contain("constraint budget ok");
        expect(code).to.equal(0);
    });

    it("FAILS when the count drifts from the budget", () => {
        scaffold(budgetWith(actualConstraints - 1, 65536));
        const { code, out } = run();
        expect(out).to.contain("budget says");
        expect(out).to.contain("just budget-update");
        expect(code).to.equal(1);
    });

    // The failure this gate exists for: crossing the FFT domain.
    it("FAILS when the circuit exceeds its FFT domain", () => {
        scaffold(budgetWith(actualConstraints, 1));
        const { code, out } = run();
        expect(out).to.contain("EXCEEDS");
        expect(code).to.equal(1);
    });

    // snarkjs sizes the FFT from nConstraints + nPubInputs + nOutputs and
    // requires that sum to be at most domain - 1, so the gate must count public
    // signals as well. The domain: 1 case above is far enough over to miss the
    // boundary; this case and the next pin both sides of it.
    it("counts public signals against the FFT domain", () => {
        // sized == domain is one too large: snarkjs needs sized <= domain - 1.
        scaffold(budgetWith(actualConstraints, sizedSignals));
        const tight = run();
        expect(tight.out, "sized == domain must not fit").to.contain("EXCEEDS");
        expect(tight.code).to.equal(1);
    });

    it("accepts the largest count that still fits the domain", () => {
        fs.rmSync(ROOT, { recursive: true, force: true });
        scaffold(budgetWith(actualConstraints, sizedSignals + 1));
        const ok = run();
        expect(ok.out, "sized == domain - 1 is the last count that fits").to.contain(
            "constraint budget ok",
        );
        expect(ok.code).to.equal(0);
    });

    it("FAILS when the artifact is missing", () => {
        scaffold(budgetWith(actualConstraints, 65536), { withR1cs: false });
        const { code, out } = run();
        expect(out).to.contain("missing");
        expect(code).to.equal(1);
    });

    // An artifact older than its sources would report stale counts as a pass.
    it("FAILS when the artifact is older than the sources", () => {
        scaffold(budgetWith(actualConstraints, 65536), { sourceOffsetMs: 60_000 });
        const { code, out } = run();
        expect(out).to.contain("stale");
        expect(code).to.equal(1);
    });

    // Staleness is decided from production sources only, so adding a test
    // fixture does not require recompiling the production circuits.
    it("ignores src/test when deciding staleness", () => {
        scaffold(budgetWith(actualConstraints, 65536), { testFixture: true });
        const { code, out } = run();
        expect(out, "a test fixture must not invalidate production artifacts").to.contain("ok");
        expect(code).to.equal(0);
    });

    it("--update rewrites the budget to the measured count", () => {
        scaffold(budgetWith(1, 65536));
        const { code } = run("--update");
        expect(code).to.equal(0);

        const written = JSON.parse(fs.readFileSync(path.join(ROOT, "budget.json"), "utf8"));
        expect(written.circuits["2x2"].constraints).to.equal(actualConstraints);
        expect(written.circuits["2x2"].domain, "domain must survive --update").to.equal(65536);
        expect(run().code, "the rewritten budget must then pass").to.equal(0);
    });

    it("--update refuses to record a missing artifact", () => {
        scaffold(budgetWith(1, 65536), { withR1cs: false });
        const { code, out } = run("--update");
        expect(out).to.contain("missing");
        expect(code).to.equal(1);
    });
});
