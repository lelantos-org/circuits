// Address one entry of a circom input object by the name the circom uses:
// `merkle_root`, `in_rcv[2]`, `in_path_elements[0][3][1]`.
//
// Tamper and divergence cases change exactly one entry of an honest witness.
// Writing the path as a string keeps the row readable and greppable against the
// template, and keeps nested-array copying out of each test.
//
// Values are decimal strings, as circom input objects carry them.

type Nested = string | Nested[];
type InputObject = object;

function parse(path: string): { key: string; idx: number[] } {
    const [key, ...rest] = path.split("[");
    const idx = rest.map(part => {
        const n = Number(part.replace("]", ""));
        if (!Number.isInteger(n) || n < 0) throw new Error(`signal path "${path}": bad index "${part}"`);
        return n;
    });
    return { key, idx };
}

function root(input: InputObject, key: string, path: string): Nested {
    const v = (input as Record<string, Nested | undefined>)[key];
    if (v === undefined) throw new Error(`signal path "${path}": no signal "${key}" in the input`);
    return v;
}

/** The entry at `path`, parsed. */
export function readSignal(input: InputObject, path: string): bigint {
    const { key, idx } = parse(path);
    let cur = root(input, key, path);
    for (const i of idx) {
        if (!Array.isArray(cur) || cur[i] === undefined) {
            throw new Error(`signal path "${path}": index ${i} is out of range`);
        }
        cur = cur[i];
    }
    if (Array.isArray(cur)) throw new Error(`signal path "${path}" names an array, not an entry`);
    return BigInt(cur);
}

/**
 * Overwrite the entry at `path` in place.
 *
 * Only the addressed entry changes; sibling arrays are shared with the input, so
 * callers that need the original intact clone first (`structuredClone`).
 */
export function writeSignal(input: InputObject, path: string, value: bigint): void {
    const { key, idx } = parse(path);
    if (idx.length === 0) {
        root(input, key, path);
        (input as Record<string, Nested>)[key] = value.toString();
        return;
    }
    let cur = root(input, key, path);
    for (const i of idx.slice(0, -1)) {
        if (!Array.isArray(cur)) throw new Error(`signal path "${path}": index ${i} is out of range`);
        cur = cur[i];
    }
    const last = idx[idx.length - 1];
    if (!Array.isArray(cur) || cur[last] === undefined) {
        throw new Error(`signal path "${path}": index ${last} is out of range`);
    }
    cur[last] = value.toString();
}

/** Add `delta` (default 1) to the entry at `path`, in place. Enough to break any binding. */
export function bumpSignal(input: InputObject, path: string, delta = 1n): void {
    writeSignal(input, path, readSignal(input, path) + delta);
}

/** `v + 1` for a decimal-string value. */
export function incremented(v: string): string {
    return (BigInt(v) + 1n).toString();
}
