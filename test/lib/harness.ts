// Suite scaffolding: a shared `before` hook for loading circuits and gadgets.
//
// Suites need some subset of `loadCircuit(WRAPPER)`, `Poseidon.build()` and
// `Jubjub.build()`. Centralising the hook gives a change to circuit loading
// (the projection wrapper, a new artifact) a single site.
//
// Per-circuit suites layer on top: `test/transact/setup.ts :: useTransactCircuit`
// adds the `TxBuilder`, `test/batch/setup.ts :: useBatchCircuit` the
// `BatchBuilder` and the batch assertions, and
// `lib/underconstrained_suite.ts :: useSearchSuite` the R1CS search context.
// Each returns a stable context object and lets `before` populate it, so callers
// destructure at test time rather than capturing an undefined binding at
// declaration time.
//
// Three suites build directly, each for a reason these do not cover:
// `formal/pubsignal_order.test.ts` loads a per-shape path inside a nested hook
// and keeps the witness, not the tester; `transact/binding.test.ts` loads the
// unwrapped circuit to prove the challenge-only fields are not signals;
// `tooling/underconstrained_selftest.test.ts` loads a different fixture per case.
//
// `before` rather than top-level await: `before` defers the load (`loadCircuit`
// already caches). Mocha loads every spec file before running any test, so a
// module-level `await loadCircuit(...)` would compile every circuit on every
// invocation, including a `--grep` replay of one shrunk fuzz counterexample (the
// workflow the justfile documents), which otherwise compiles one circuit. A
// `before` failure also names and fails only its suite, whereas a
// top-level-await failure aborts the run without attribution, and
// `this.timeout(...)` on the describe covers a hook but not a module load.
//
// `Jubjub.build()` is memoized here because it initialises two circomlibjs wasm
// modules. `loadCircuit` and `compileConstraintsOnly` are memoized per path, so
// no setup cost repeats across suites.

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
 * The type declares `circuit: CircuitTester`, which does not hold between
 * `useCircuit()` returning and the hook running. Destructuring at `describe`
 * scope instead of inside the `it` reads the field in that interval; with plain
 * fields that fails as `Cannot read properties of undefined (reading
 * 'calculateWitness')`, naming neither the suite nor the mistake.
 *
 * Throwing getters enforce the rule at no cost to call sites: `ctx.circuit`
 * reads as a plain property once the hook has run.
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
 * Load a circuit and the reference gadgets in `before`.
 *
 * `wrap` adapts the tester before it is handed over; `test/transact/setup.ts`
 * uses it for `projectingTester`, whose docblock explains why the projection is
 * applied at load.
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

/**
 * Load several circuits, keyed by name, and the reference gadgets in `before`.
 *
 * For suites that compare circuits against each other; the compiles run
 * concurrently.
 */
export function useCircuits<K extends string>(
    paths: Record<K, string>,
): Gadgets & { circuits: Record<K, CircuitTester> } {
    type Ctx = Gadgets & { circuits: Record<K, CircuitTester> };
    const ctx = pendingCtx<Ctx>(["circuits", "P", "J"], `useCircuits(${Object.keys(paths).join(", ")})`);
    before(async () => {
        const names = Object.keys(paths) as K[];
        const [testers, P, J] = await Promise.all([
            Promise.all(names.map(name => loadCircuit(paths[name]))),
            Poseidon.build(),
            buildJubjub(),
        ]);
        ctx.circuits = Object.fromEntries(names.map((name, i) => [name, testers[i]])) as Record<K, CircuitTester>;
        ctx.P = P;
        ctx.J = J;
    });
    return ctx;
}
