# Lelantos Circuits

Groth16 prover artifacts for the Lelantos multi-asset shielded pool.

| Doc | Contents |
|---|---|
| [src/README.md](src/README.md) | Circuit design, threat model, public-input layout |
| [lean/README.md](lean/README.md) | Machine-checked soundness proofs |
| [lean/FIDELITY.md](lean/FIDELITY.md) | How closely the Lean model tracks the circom |

> **Prototype. Not production-safe.** The phase-2 setup has a single
> contributor, so anyone holding that contribution can forge proofs. A real MPC
> ceremony is required before mainnet use. The package bumps to `1.0.0` once it
> completes.

## Installation

```bash
npm install @lelantos-org/circuits
```

### Exports

| Specifier | File |
|---|---|
| `@lelantos-org/circuits/4x6/4x6.wasm` | Witness generator |
| `@lelantos-org/circuits/4x6/4x6_final.zkey` | Proving key |
| `@lelantos-org/circuits/4x6/verification_key.json` | Verification key |
| `@lelantos-org/circuits/vectors` | Vector index, with a SHA-256 per file |
| `@lelantos-org/circuits/vectors/transact-4x6.json` | Transact test vector |
| `@lelantos-org/circuits/vectors/tree-update-batch-8.json` | Batch test vector |

The vectors are the cross-repo contract: each carries the witness, the
coefficient vector, the Fiat-Shamir challenge and the `y` read out of a compiled
circuit. Consumers check their own implementation against them.

## Circuits

| Circuit | Instantiation | Purpose |
|---|---|---|
| `src/4x6.circom` | `Transact(11, 4, 6)` | Spend 4 notes, create 6 |
| `src/tree_update_batch.circom` | `TreeUpdateBatch(11, 8)` | Advance the commitment tree by up to 8 leaves |

The two are **ceremony-paired**. A spend emits `N_OUT = 6` leaves that the batch
circuit inserts, so they share `DEPTH = 11` and cannot be mixed across versions.
`MAX_L = 8` rather than 6 because `COUNT_BITS` requires a power of two.

Each circuit has exactly one public input, the Fiat-Shamir challenge `z`, and
one public output, `y`. circom orders main outputs before main public inputs, so
the generated verifier takes `_pubSignals = [y, z]`, in that order.

### Constraint counts

R1CS totals on BN254 (`snarkjs r1cs info`):

| Circuit | Constraints | Wires | Private inputs |
|---|---:|---:|---:|
| `Transact(11, 4, 6)` | 100,320 | 100,473 | 323 |
| `TreeUpdateBatch(11, 8)` | 113,527 | 113,378 | 93 |

Both sit in the 2^17 FFT domain. snarkjs sizes that domain from
`nConstraints + nPubInputs + nOutputs` and requires the sum to be at most
`2^17 - 1`, so the ceiling on the constraint count is **131,069**: the transact
circuit clears it by 30,749 and the batch circuit by 17,542. `just budget` pins
both to their exact counts in [budget.json](budget.json), so growth lands as a
reviewable diff rather than a silent doubling of proving time.

`TreeUpdateBatch` is the tighter of the two and is what a further widening
breaks first: a leaf slot costs roughly 12k constraints.

## Asset id registration

A deposit leaf is pinned only by the Pedersen equality

```
cv_dep == leaf_public_in · V^leaf_asset + rcv · H
```

and every asset generator is a known multiple `m(a) · BASE0` of one base. The
equality therefore fixes the product `value · m(asset)`, not the pair, so two
registered ids whose multipliers share a large factor admit a deposit paid in
one asset and spent as another.

Run `just asset-ids <ids>` over an id set **before** registering it.
`AssetRegistry.addAsset` accepts an arbitrary `uint64` and checks nothing here.
Small sequential ids clear the bound by 18 bits or more; the risk is in
hash-like ids. See the header of
[src/tree_update_batch.circom](src/tree_update_batch.circom).

## Formal verification

The circuits have machine-checked soundness proofs in Lean 4
([`lean/`](lean/README.md), run with `just lean-check`). The proofs quantify
over every assignment satisfying the modelled constraints, which is the
under-constrained-signal class a test suite cannot reach.

Headline results:

- Per-asset value conservation holds for every asset id, as an exact integer
  equation over the naturals.
- Two distinct public-input vectors collide on at most 68 Fiat-Shamir
  challenges out of `p ≈ 2^253.6`.
- The Edwards point balance is proved **not** to be a conservation check, so
  nothing can re-derive one from it.
- `TreeUpdateBatch` advances the root by exactly `actual_count` appends, for any
  count.

Conservation and the PolyEval binding assume only that the BN254 scalar field is
prime, and nothing about Poseidon. Collision resistance is an explicit
hypothesis, never an axiom, and a build-time guard rejects any axiom outside
[lean/expected/axioms.txt](lean/expected/axioms.txt). Every soundness result is
paired with a satisfying assignment, so none is vacuous.

Not covered: `FrontierRoot`, the `BabyCheck` on `cv_dep`, uniqueness of a
deposit leaf's opening (see *Asset id registration*), and the model-to-source
correspondence, which is a hand-maintained table. See
[lean/README.md](lean/README.md) § *What is not proved*.

## Development

```bash
just build-artifacts-4x6   # compile + phase-2 setup for the transact circuit
just test                  # TypeScript suite over the compiled circuits
just budget                # constraint budget gate
just lint                  # circomspect
just lean-check            # build, axiom guard, layout and citation checks
just vectors-check         # regenerate vectors/ and diff against the committed files
```

`just --list` shows the rest. Rebuild recipes re-run the single-contributor
ceremony and invalidate every existing proof and committed fixture.
