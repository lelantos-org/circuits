// Circuit dimensions and test-wide literals. Each dimension mirrors the circom
// declaration its comment names.

import type { Field } from "../helpers";

/** The optimization level the circuits ship at — `CIRCOM_OPT` in the justfile. */
export const CIRCOM_OPT = "--O2";

/**
 * The level the second-witness search reads. `--O2` only substitutes signals a
 * linear constraint determines, so the two systems have the same solutions,
 * and the `--O1` rows are sparse: a sweep costs about 15x less.
 */
export const SEARCH_OPT = "--O1";

// ===== circuit dimensions =====

/**
 * Quaternary tree depth, shared by `Transact(11, 4, 6)` and
 * `TreeUpdateBatch(11, 8)` because a spend's output leaves are inserted by the
 * batch circuit. 4^11 = 4,194,304 leaves.
 */
export const DEPTH = 11;

/** Alias naming the first argument of `TreeUpdateBatch` for the batch suites. */
export const BATCH_DEPTH = DEPTH;

/**
 * Shielded input slots — `N_IN` in `Transact(11, 4, 6)`, `src/4x6.circom`.
 * The width is fixed; `TxBuilder.build` pads with dummies.
 */
export const N_IN = 4;

/** Shielded output slots — `N_OUT` in `Transact(11, 4, 6)`. */
export const N_OUT = 6;

/** Children per node — `src/lib/merkle.circom`. */
export const ARITY = 4;

/**
 * Max leaves per batch — the second argument to `TreeUpdateBatch` at the bottom
 * of `src/tree_update_batch.circom`.
 *
 * The minimum valid value: COUNT_BITS requires a power of two, and a spend's
 * TRANSACT_OUT = 6 leaves must fit one batch.
 */
export const MAX_L = 8;

/**
 * Bits `actual_count - 1` decomposes into — `COUNT_BITS` in
 * `src/lib/batch_append.circom`, which asserts `1 << COUNT_BITS == MAX_L`.
 */
export const COUNT_BITS = 3;

// ===== range bounds the circuit enforces =====

/** The asset_id / value bound: the smallest value Num2Bits(64) rejects. */
export const TWO_64 = 1n << 64n;

// ===== named actors =====

/** Default spending key for the note owner under test. */
export const ALICE_NSK: Field = 11n;

/** A second owner, where a test needs the recipient to differ. */
export const BOB_NSK: Field = 22n;

/** A third key, for tests where the declared pk does not match the nsk. */
export const MALLORY_NSK: Field = 12n;

// ===== mocha timeouts =====

/** No circuit compile: reference-implementation and file-parsing suites. */
export const TIMEOUT_FAST = 60_000;

/** Compiles a fixture or production circuit and generates a few witnesses. */
export const TIMEOUT_CIRCUIT = 300_000;

/** Many witnesses over a production-depth circuit: batch and fuzz suites. */
export const TIMEOUT_HEAVY = 900_000;
