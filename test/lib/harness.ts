// Suite scaffolding: a shared `before` hook that loads circuits and gadgets.
//
// Loading happens in `before` rather than at module level: mocha imports every
// spec file before running any test, so a module-level load would compile every
// circuit even under `--grep`.

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
 * A context whose fields throw until `before` fills them, so destructuring at
 * `describe` scope fails with an error naming the suite and the field.
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
 * Load a circuit and the reference gadgets in `before`. `wrap` adapts the
 * tester before it is handed over.
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

/** Load several circuits, keyed by name, and the reference gadgets in `before`. */
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
