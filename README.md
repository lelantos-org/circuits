# Lelantos Circuits

Groth16 prover artifacts for the Lelantos transact circuit.

Circuit design: [src/README.md](src/README.md). Formal verification:
[lean/README.md](lean/README.md).

## Installation

```bash
npm install @lelantos-org/circuits
```

### Constraint counts

R1CS totals on BN254 (`snarkjs r1cs info`):

| Circuit                                               | Constraints | Wires   | Private inputs |
|-------------------------------------------------------|------------:|--------:|---------------:|
| `2x2.circom` — `Transact(10, 2, 2)`                   |      69,350 |  69,419 |            143 |
| `3x3.circom` — `Transact(10, 3, 3)`                   |     102,939 | 103,040 |            210 |
| `tree_update_batch.circom` — `TreeUpdateBatch(10, 16)` |     252,672 | 252,368 |            146 |

Each has one public input (the Fiat–Shamir challenge `z`). Only the `2x2`
artifacts ship in the npm package; `3x3` is built but not wired on-chain (it
needs a 42-slot `PubInputs.compress` overload — see [src/3x3.circom](src/3x3.circom)).

## Formal verification

The transact circuit has a machine-checked soundness proof in Lean 4
([`lean/`](lean/README.md), run with `just lean-check`). It quantifies over
every assignment satisfying the modeled constraints — the under-constrained
signal class the test suite cannot reach.

Headline results: per-asset value conservation holds for every asset id, as an
exact integer equation; distinct public inputs collide on at most 30 Fiat–Shamir
challenges; and the Edwards point balance is proved **not** to be a conservation
check, so nothing can re-derive one from it. Conservation and PolyEval binding
assume only the primality of the BN254 scalar field — nothing about Poseidon.
Collision resistance is an explicit hypothesis, never an axiom, and a build-time
guard rejects any axiom outside [`lean/expected/axioms.txt`](lean/expected/axioms.txt).

Scope: `Transact` only — `tree_update_batch` is not formalized, and model-to-source
correspondence is a hand-maintained table. See
[lean/FIDELITY.md](lean/FIDELITY.md) and `lean/README.md` § *What is not proved*.

## Status

Prototype. The trusted setup uses a single contributor — **not
production-safe**. A real MPC ceremony is required before mainnet use; the
package bumps to `1.0.0` once that ceremony completes.
