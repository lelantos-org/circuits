import { expect } from "chai";
import { existsSync } from "node:fs";

import { TIMEOUT_CIRCUIT } from "../lib/constants";
import { readJson, repoPath } from "../lib/files";
import { loadSymbols, type SymbolTable } from "../lib/r1cs";

// Model-to-circuit signal parity.
//
// `lean/` proves properties of `TransactSat`, a structure over `TxWitness`, each
// field of which corresponds to a signal of `4x6.circom`.
// `lean/expected/signal-map.json` records the correspondence. This file checks
// the circom half: each named signal exists in the compiled `.sym`.
// `lean/scripts/check-names.py` checks the Lean half: each key resolves as a
// declaration.
//
// Scope: this checks that the signal a field names exists, not that it is the
// correct signal; a field mapped to a real but wrong signal passes.
//
// Arity: a template is checked at every index below its bound and at the bound
// itself, where it must be absent, so `Transact(11, 4, 6)` is read off the
// circuit.
//
// `absent`: the circom optimizer removes a signal that a constraint pins to a
// constant. `main.all_dummy.out` is removed because `all_dummy.out === 0` pins
// it to zero, the constraint `TransactSat.not_all_dummy` models and
// `TxWellFormed.someRealInput` depends on. Asserting that it stays absent
// detects removal of that constraint.


interface CircuitMap {
    sym: string;
    shape: Record<string, number>;
    present: Record<string, string>;
    absent: Record<string, { was: string; why: string }>;
    aliases?: Record<string, string>;
}

const raw = readJson<Record<string, unknown>>("lean/expected/signal-map.json");
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
 * Each placeholder is swept independently with the others held at 0, not over
 * the full product. The out-of-range name for each placeholder pins the arity.
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
    const symPath = repoPath(map.sym);

    describe(`formal model / signal parity (${circuit})`, function () {
        this.timeout(TIMEOUT_CIRCUIT);

        let symbols: SymbolTable;

        before(async function () {
            if (!existsSync(symPath)) {
                // circom_tester writes its artifacts outside `build/`, so local
                // runs and the `test` workflow have no `build/*.sym` and skip.
                // `REQUIRE_ARTIFACTS=1`, set by the `build` workflow, turns the
                // skip into a failure.
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
            // Without an alias, a witness harness using this map cannot populate
            // a model field whose signal is optimized away.
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
