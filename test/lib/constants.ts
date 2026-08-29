// Circuit dimensions and test-wide literals.
//
// Every value mirrors a circom declaration; each comment names the declaration
// site so a circuit change has a single place to land.

import type { Field } from "../helpers";

// ===== circuit dimensions =====

/**
 * Quaternary tree depth. `Transact(11, 4, 6)` and `TreeUpdateBatch(11, 8)` share
 * it — they must, since a spend's output leaves are inserted by the batch
 * circuit. 4^11 = 4,194,304 leaves.
 */
export const DEPTH = 11;

/**
 * Alias kept so the batch suites read against their own circuit's first
 * argument rather than a constant named for the transact side.
 */
export const BATCH_DEPTH = DEPTH;

/**
 * Shielded input slots — `N_IN` in `Transact(11, 4, 6)`, `src/4x6.circom`.
 *
 * The circuit takes exactly this many; a witness short of it fails witness
 * calculation with "Not enough values for input signal". `TxBuilder.build`
 * pads with dummies rather than making every suite spell out the padding.
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
 * At its floor: COUNT_BITS below requires a power of two, and a spend emits
 * TRANSACT_OUT = 6 leaves that must fit one batch. Six is not a power of two,
 * so the floor is 8.
 */
export const MAX_L = 8;

/**
 * Bits `actual_count - 1` decomposes into — `COUNT_BITS` in the same file. The
 * circuit asserts `1 << COUNT_BITS == MAX_L`. Derived there from MAX_L; mirrored
 * here because the tests build witnesses against it directly.
 */
export const COUNT_BITS = 3;

/** Blinder width — `RCV_BITS()` in `src/lib/value_commit.circom`. */
export const RCV_BITS = 252n;

// ===== range bounds the circuit enforces =====

/** The asset_id / value bound; tamper tests set a field to exactly this to trip Num2Bits(64). */
export const TWO_64 = 1n << 64n;

/** One past the blinder range, for the Num2Bits(RCV_BITS) rejection tests. */
export const TWO_252 = 1n << RCV_BITS;

// ===== named actors =====
//
// Named so that "same owner" and "different owner" are visible at the call site.

/** Default spending key for the note owner under test. */
export const ALICE_NSK: Field = 11n;

/** A second owner, where a test needs the recipient to differ. */
export const BOB_NSK: Field = 22n;

/** A third key, for tests where the declared pk does not match the nsk. */
export const MALLORY_NSK: Field = 12n;

// ===== mocha timeouts =====
//
// Three tiers, chosen by what the suite does.

/** No circuit compile: reference-implementation and file-parsing suites. */
export const TIMEOUT_FAST = 60_000;

/** Compiles a fixture or production circuit and generates a few witnesses. */
export const TIMEOUT_CIRCUIT = 300_000;

/** Many witnesses over a production-depth circuit: batch and fuzz suites. */
export const TIMEOUT_HEAVY = 900_000;
