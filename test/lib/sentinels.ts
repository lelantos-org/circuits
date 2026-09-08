// Distinct-value builders for the layout-parity suites.
//
// A layout test proves an ORDER, so it needs one distinguishable value per slot:
// assign a unique sentinel to each named slot, run the flattener, and require
// the result to reproduce the published order. Any transposition then shows up
// as a mismatch instead of two equal words coincidentally agreeing.
//
// Both `formal/layout_parity.test.ts` (transact, anchored on the Lean dump) and
// `formal/batch_layout_parity.test.ts` (batch, anchored on the published vector)
// built the same three accessors by hand, differing only in an error prefix.
// The anchors stay per-suite — they assert genuinely different claims — but the
// mechanism does not.

/** Sentinels by slot name, plus the accessors a layout test needs. */
export interface Sentinels {
    /** Slot name -> its unique value. */
    map: Record<string, bigint>;
    /** One slot, failing loudly rather than yielding `undefined` on a typo. */
    at(name: string): bigint;
    /** `[at("<field> 0"), ...]` for `n` slots. */
    scalars(field: string, n: number): bigint[];
    /** `[[at("<field>X i"), at("<field>Y i")], ...]` for `n` slots. */
    points(field: string, n: number): bigint[][];
}

/**
 * Build sentinels for `names`, numbered from `base`.
 *
 * `base` separates two families in one test — `formal/layout_parity.test.ts`
 * builds the coefficient slots at 1000 and the challenge-only words at 9000, and
 * they must not collide, or a word moving between the two vectors would go
 * unnoticed. Both are required rather than defaulted: every call site states its
 * family, so a third one cannot silently land on top of an existing range.
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
