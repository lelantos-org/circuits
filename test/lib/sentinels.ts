// Distinct-value builders for the layout-parity suites.
//
// A layout test assigns a unique sentinel to each named slot, runs the
// flattener, and requires the result to reproduce the published order.

/** Sentinels by slot name, plus the accessors a layout test needs. */
export interface Sentinels {
    /** Slot name -> its unique value. */
    map: Record<string, bigint>;
    /** One slot; throws on an unknown name rather than yielding `undefined`. */
    at(name: string): bigint;
    /** `[at("<field> 0"), ...]` for `n` slots. */
    scalars(field: string, n: number): bigint[];
}

/**
 * Build sentinels for `names`, numbered from `base`.
 *
 * `base` separates two families in one test: `formal/layout_parity.test.ts`
 * builds the coefficient slots at 1000 and the challenge-only words at 9000.
 * The ranges must not overlap, or a word moving between the two vectors would
 * go undetected.
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
    };
}
