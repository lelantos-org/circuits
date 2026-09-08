// Suite scaffolding: the `before` hook almost every suite was writing by hand.
//
// A dozen suites opened with some subset of `loadCircuit(WRAPPER)`,
// `Poseidon.build()` and `Jubjub.build()`, assigning into `let` bindings
// declared above. The bodies differed only in which of the three they wanted,
// so a change to how a circuit is loaded — the projection wrapper, a new
// artifact — had a dozen landing sites.
//
// Four suites still build directly, each for a reason `useCircuit` does not
// cover: `fuzz/fixed_base_mul.fuzz.test.ts` loads three circuits in one
// `Promise.all`; `formal/pubsignal_order.test.ts` loads a per-shape path inside
// a nested hook and keeps the witness, not the tester;
// `transact/binding.test.ts` deliberately loads the UNWRAPPED circuit to prove
// the challenge-only fields are not signals; `underconstrained_selftest.test.ts`
// wants `compileConstraintsOnly`, a different artifact.
//
// The shape here is `test/transact/setup.ts :: useTransactCircuit`, which got it
// right first: return a STABLE context object and let `before` populate it, so
// callers destructure at test time rather than capturing an undefined binding at
// declaration time. That file now builds on this.
//
// WHY `before` AND NOT A TOP-LEVEL AWAIT. `before` is here to DEFER, not to
// cache — `loadCircuit` already caches. Mocha loads every spec file before
// running any test, so a module-level `await loadCircuit(...)` would compile
// every circuit on every invocation, including a `--grep` replay of one shrunk
// fuzz counterexample (the workflow the justfile documents), which today pays
// for one circuit. A `before` failure also names its suite and fails only that
// suite, where a top-level-await failure aborts the run with no attribution,
// and `this.timeout(...)` on the describe covers a hook but not a module load.
//
// `Jubjub.build()` is memoized here as well. It initialises two circomlibjs wasm
// modules and was NOT cached, so every suite that wanted a curve paid for it
// again; `loadCircuit` and `compileConstraintsOnly` were already memoized per
// path, so this closes the last repeated setup cost.

import { Jubjub, Poseidon } from "../helpers";
import { loadCircuit, type CircuitTester } from "./circuit";

let jubjub: Promise<Jubjub> | undefined;

export function buildJubjub(): Promise<Jubjub> {
    return (jubjub ??= Jubjub.build());
}

/** The reference gadgets a suite needs to build witnesses off-circuit. */
export interface Gadgets {
    P: Poseidon;
    J: Jubjub;
}

/**
 * A context whose fields throw until `before` fills them.
 *
 * The type says `circuit: CircuitTester`, which is a lie for the interval
 * between `useCircuit()` returning and the hook running — and the natural way to
 * get that lie wrong is to destructure at `describe` scope instead of inside the
 * `it`. That used to surface as `Cannot read properties of undefined (reading
 * 'calculateWitness')`, naming neither the suite nor the mistake.
 *
 * Defining the fields as throwing getters makes the rule enforced rather than a
 * comment, and costs nothing at a call site: `ctx.circuit` still reads as a
 * plain property once the hook has run.
 */
export function pendingCtx<T extends object>(keys: readonly (keyof T)[], what: string): T {
    const store: Partial<T> = {};
    const ctx = {} as T;
    for (const key of keys) {
        Object.defineProperty(ctx, key, {
            get() {
                if (!(key in store)) {
                    throw new Error(
                        `${what}: ctx.${String(key)} was read before the before() hook ran — ` +
                            "destructure inside the it(), not at describe scope",
                    );
                }
                return store[key];
            },
            set(v: T[keyof T]) {
                store[key] = v;
            },
            enumerable: true,
            configurable: true,
        });
    }
    return ctx;
}

export interface CircuitCtx extends Gadgets {
    /** Populated by `before`; reading it earlier throws, see `pendingCtx`. */
    circuit: CircuitTester;
}

/** For suites that assert against the reference implementation without compiling anything. */
export function useGadgets(): Gadgets {
    const ctx = pendingCtx<Gadgets>(["P", "J"], "useGadgets");
    before(async () => {
        [ctx.P, ctx.J] = await Promise.all([Poseidon.build(), buildJubjub()]);
    });
    return ctx;
}

/**
 *
 * `wrap` adapts the tester before it is handed over; `test/transact/setup.ts`
 * uses it for `projectingTester`. See that function's docblock for why the
 * projection is applied at load.
 */
export function useCircuit(
    path: string,
    wrap: (c: CircuitTester) => CircuitTester = c => c,
): CircuitCtx {
    const ctx = pendingCtx<CircuitCtx>(["circuit", "P", "J"], `useCircuit(${path})`);
    before(async () => {
        const [circuit, P, J] = await Promise.all([
            loadCircuit(path),
            Poseidon.build(),
            buildJubjub(),
        ]);
        ctx.circuit = wrap(circuit);
        ctx.P = P;
        ctx.J = J;
    });
    return ctx;
}
