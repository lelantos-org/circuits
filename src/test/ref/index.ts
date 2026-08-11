// Reference implementation of the primitives and witness builders the circuit
// tests require.
//
// This package has no dependency on @lelantos-org/sdk. The circom under
// `src/lib/` defines the signal layout and is the source of truth for every
// value here; where a value is also pinned by the Lean model or by
// PubInputs.sol, the comment names it. Agreement with the SDK is established
// through the vectors under `vectors/`, which are generated from this
// directory and verified by the SDK's test suite.
//
// Module map:
//   field     BN254 / Baby-Jubjub constants, the Field and Point types
//   tags      the TAG_* table, from lib/tags.circom
//   bytes     LE/BE field<->byte conversion and LSB-first bit packing
//   poseidon  BN254 Poseidon, arities 1..8
//   jubjub    the curve; sole point of contact with circomlibjs field elements
//   merkle    quaternary tree; node = Poseidon(TAG_MERKLE, c0..c3)
//   path      independent root recomputation, cross-checks merkle
//   note      commitment, nullifier, rho, key derivation
//   sqrt      Legendre symbol and Tonelli-Shanks, for the FMD bit
//   fmd       FMD2 clue construction
//   compress  the PolyEval layouts, Horner eval, Fiat-Shamir
//   witness   the circom input objects
//
// Modules export disjoint names, so the barrel re-exports each in full.

export * from "./field.js";
export * from "./tags.js";
export * from "./bytes.js";
export * from "./poseidon.js";
export * from "./jubjub.js";
export * from "./merkle.js";
export * from "./path.js";
export * from "./note.js";
export * from "./sqrt.js";
export * from "./fmd.js";
export * from "./compress.js";
export * from "./witness.js";
