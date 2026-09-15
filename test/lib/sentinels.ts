// Distinct-value builders for the layout-parity suites.
//
// A layout test checks an order, so it needs one distinguishable value per slot:
// assign a unique sentinel to each named slot, run the flattener, and require
// the result to reproduce the published order. A transposition then shows up as
// a mismatch rather than two equal words agreeing.
//
// Used by `formal/layout_parity.test.ts` (transact) and
// `formal/batch_layout_parity.test.ts` (batch). Each suite keeps its own anchor,
// since they assert different claims.

/** Sentinels by slot name, plus the accessors a layout test needs. */
export interface Sentinels {
    /** Slot name -> its unique value. */
    map: Record<string, bigint>;
    /** One slot; throws on an unknown name rather than yielding `undefined`. */
    at(name: string): bigint;
    /** `[at("<field> 0"), ...]` for `n` slots. */
    scalars(field: string, n: number): bigint[];
    /** `[[at("<field>X i"), at("<field>Y i")], ...]` for `n` slots. */
    points(field: string, n: number): bigint[][];
}

/**
 * Build sentinels for `names`, numbered from `base`.
 *
 * `base` separates two families in one test: `formal/layout_parity.test.ts`
 * builds the coefficient slots at 1000 and the challenge-only words at 9000.
 * They must not collide, or a word moving between the two vectors would go
 * undetected. `base` and `label` are required rather than defaulted, so every
 * call site states its family and a new one cannot overlap an existing range
 * unnoticed.
 */
export function sentinels(names: readonly string[], base: number, label: string): Sentinels {
    const map = Object.fromEntries(names.map((name, i) => [name, BigInt(base + i)]));

    const at = (name: string): bigint => {
        const v = map[name];
        if (v === undefined) throw new Error(`${label}: no sentinel for slot "${name}"`);
        return v;
    };

    return {
        map,
        at,
        scalars: (field, n) => Array.from({ length: n }, (_, i) => at(`${field} ${i}`)),
        points: (field, n) => Array.from({ length: n }, (_, i) => [at(`${field}X ${i}`), at(`${field}Y ${i}`)]),
    };
}
