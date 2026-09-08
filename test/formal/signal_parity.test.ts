import { expect } from "chai";
import { existsSync, readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import { loadSymbols, type SymbolTable } from "../lib/r1cs";

// Model-to-circuit signal parity.
//
// `lean/` proves things about `TransactSat`, a hand-written structure over a
// hand-written `TxWitness`. Every field of that witness claims to BE a signal of
// `4x6.circom`, and nothing checked the claim: `lake build` sees Lean, and the
// circuit tests see circom, and the sentence tying them together lived in a doc
// comment. A renamed signal, or a field naming one that never existed, was
// invisible to both.
//
// `lean/expected/signal-map.json` is that sentence, written down. This file checks
// the circom half — that each named signal exists in the compiled `.sym`.
// `lean/scripts/check-names.py` checks the Lean half, that each key resolves as a
// declaration. Neither side can drift without one of them failing.
//
// WHAT THIS IS NOT. It does not check that a field mirrors the RIGHT signal, only
// that the signal it names is real. A field pointed at a real but wrong signal
// passes here. That is the next rung — evaluating the model on a real witness — and
// this is its prerequisite, since such a harness needs exactly this map to read a
// witness vector into a `TxWitness`.
//
// ARITY COMES FREE. A template is checked at every index below its bound AND at the
// bound itself, where it must be absent. So `Transact(11, 4, 6)` is read off the
// circuit rather than asserted in `constants.ts`: widen `N_OUT` in the circom and
// this fails until the map agrees.
//
// ON `absent`. The circom optimizer deletes a signal that a constraint pins to a
// constant, and those deletions are informative rather than inconvenient.
// `main.all_dummy.out` is gone because `all_dummy.out === 0` holds it at zero — the
// constraint `TransactSat.not_all_dummy` models and `TxWellFormed.someRealInput`
// rests on. Asserting it STAYS gone turns the optimizer into a witness: if that
// constraint is ever removed, the signal comes back and this fails.

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(HERE, "../..");
const MAP_FILE = resolve(ROOT, "lean/expected/signal-map.json");

interface CircuitMap {
    sym: string;
    shape: Record<string, number>;
    present: Record<string, string>;
    absent: Record<string, { was: string; why: string }>;
    aliases?: Record<string, string>;
}

const raw = JSON.parse(readFileSync(MAP_FILE, "utf8")) as Record<string, unknown>;
const circuits = Object.entries(raw).filter(([key]) => !key.startsWith("_")) as [
    string,
    CircuitMap,
][];

/** `{i<N_IN}` — one placeholder, its variable and the shape entry bounding it. */
const PLACEHOLDER = /\{([a-z]+)<([A-Z_0-9]+)\}/g;

interface Expansion {
    /** Names that must exist: every in-range index of every placeholder. */
    present: string[];
    /** Names that must not: each placeholder one past its bound. */
    absent: string[];
}

/**
 * Expand a template into the names that must exist, plus the names that must not.
 *
 * Every placeholder is swept independently with the others held at 0, rather than
 * over the full product: the product is millions of names for a three-placeholder
 * template and buys nothing, since a `.sym` entry missing at `[2][3]` but present at
 * `[2][0]` and `[0][3]` is not a failure mode circom has. The out-of-range name for
 * each placeholder is what pins the arity.
 */
function expand(template: string, shape: Record<string, number>): Expansion {
    const vars = [...template.matchAll(PLACEHOLDER)].map(match => {
        const bound = shape[match[2]];
        if (bound === undefined) {
            throw new Error(`${template}: no shape entry named ${match[2]}`);
        }
        return { token: match[0], bound };
    });

    if (vars.length === 0) return { present: [template], absent: [] };

    const at = (values: number[]): string =>
        vars.reduce((out, v, k) => out.replace(v.token, String(values[k])), template);

    const present: string[] = [];
    const absent: string[] = [];
    vars.forEach((v, k) => {
        const others = vars.map(() => 0);
        for (let index = 0; index < v.bound; index++) {
            present.push(at(others.map((zero, n) => (n === k ? index : zero))));
        }
        absent.push(at(others.map((zero, n) => (n === k ? v.bound : zero))));
    });
    return { present: [...new Set(present)], absent: [...new Set(absent)] };
}

for (const [circuit, map] of circuits) {
    const symPath = resolve(ROOT, map.sym);

    describe(`formal model / signal parity (${circuit})`, function () {
        this.timeout(120_000);

        let symbols: SymbolTable;

        before(async function () {
            if (!existsSync(symPath)) {
                // `build/` is gitignored and the mocha suite compiles through
                // circom_tester, which writes its own artifacts elsewhere — so a
                // local run, and the `test` workflow, legitimately have no
                // `build/*.sym`. Skipping there is right; silently skipping in the
                // job that exists to run this is not, so `REQUIRE_ARTIFACTS=1` turns
                // the skip into a failure. The `build` workflow compiles both
                // circuits and sets it.
                if (process.env.REQUIRE_ARTIFACTS === "1") {
                    throw new Error(
                        `${map.sym} is missing and REQUIRE_ARTIFACTS=1. ` +
                            `Run \`just compile-4x6 compile-batch\` first.`,
                    );
                }
                this.skip();
            }
            symbols = await loadSymbols(symPath);
        });

        it("every modelled signal exists, at every index the shape declares", () => {
            const missing: string[] = [];
            for (const [field, template] of Object.entries(map.present)) {
                for (const name of expand(template, map.shape).present) {
                    if (symbols.indexOf(name) === undefined) {
                        missing.push(`${field} -> ${name}`);
                    }
                }
            }
            expect(missing).to.deep.equal(
                [],
                `these model fields name signals the compiled circuit does not have:\n  ` +
                    `${missing.join("\n  ")}`,
            );
        });

        it("no modelled signal exists past the declared shape", () => {
            // The arity pin. `main.spent[4]` existing would mean `N_IN` grew and the
            // Lean instantiation `Transact(11, 4, 6)` is describing a smaller circuit
            // than the one being compiled.
            const overrun: string[] = [];
            for (const [field, template] of Object.entries(map.present)) {
                for (const name of expand(template, map.shape).absent) {
                    if (symbols.indexOf(name) !== undefined) {
                        overrun.push(`${field} -> ${name}`);
                    }
                }
            }
            expect(overrun).to.deep.equal(
                [],
                `the circuit has signals past the shape the model is proved at:\n  ` +
                    `${overrun.join("\n  ")}`,
            );
        });

        it("the signals a constraint folds away stay folded", () => {
            const reappeared: string[] = [];
            for (const [field, entry] of Object.entries(map.absent)) {
                if (symbols.indexOf(entry.was) !== undefined) {
                    reappeared.push(`${field} -> ${entry.was}: ${entry.why}`);
                }
            }
            expect(reappeared).to.deep.equal(
                [],
                `a signal the optimizer used to fold away is back, which means the ` +
                    `constraint that pinned it is gone:\n  ${reappeared.join("\n  ")}`,
            );
        });

        it("every folded signal has a surviving alias to read it from", () => {
            // A model field whose signal was optimized away still has to be readable,
            // or the witness harness this map exists for cannot populate it.
            const aliases = map.aliases ?? {};
            const unreadable: string[] = [];
            for (const field of Object.keys(map.absent)) {
                const alias = aliases[field];
                if (alias === undefined) continue;
                for (const name of expand(alias, map.shape).present) {
                    if (symbols.indexOf(name) === undefined) {
                        unreadable.push(`${field} -> ${name}`);
                    }
                }
            }
            expect(unreadable).to.deep.equal(
                [],
                `alias signals that do not exist:\n  ${unreadable.join("\n  ")}`,
            );
        });
    });
}
