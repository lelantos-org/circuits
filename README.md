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

| Circuit                                               | Constraints |   Wires | Private inputs |
|-------------------------------------------------------|------------:|--------:|---------------:|
| `4x6.circom` — `Transact(11, 4, 6)`                   |     100,320 | 100,473 |            323 |
| `tree_update_batch.circom` — `TreeUpdateBatch(11, 8)` |     113,502 | 113,361 |             93 |

The two are **ceremony-paired**: a spend emits `N_OUT = 6` leaves that the batch
circuit inserts, so they share `DEPTH = 11` and cannot be mixed across versions.
`MAX_L = 8` rather than 6 because `COUNT_BITS` requires a power of two.

Three narrower shapes — `Transact(10, 2, 2)`, `(10, 3, 3)` and `(10, 4, 4)` —
were removed once 4x6 landed. Each cost a trusted-setup ceremony per release and
20-40 MB in every npm install without covering anything the generic template did
not. They are recoverable from git history.

Both sit in the 2^17 FFT domain, and `just budget` holds each to its exact count
in [budget.json](budget.json) so a change lands as a reviewable diff. snarkjs
sizes the domain from `nConstraints + nPubInputs + nOutputs`, so the ceiling is
131,070 rather than 131,072: 4x6 clears it by 30,750 and `tree_update_batch` by
17,568. The batch circuit is the tighter of the two and is what a further
widening breaks first — it grew on both axes at once, four more leaf slots at
roughly 12k constraints each plus the extra depth level across all eight.

Each has exactly one public *input* — the Fiat–Shamir challenge `z` — and one
public *output*, `y`. circom orders main outputs before main public inputs, so
the generated Groth16 verifier takes `_pubSignals = [y, z]`, in that order.

Nothing verifies 4x6 on-chain yet: that needs a `PubInputs.compress` overload at
69 slots, whose calldata prefix is 50 words rather than the 40 the old 4x4 layout
used, and a production ceremony.

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

Both circuits are covered: `Transact` and `TreeUpdateBatch`. Every soundness
result is paired with a satisfying assignment, so none of them is vacuous —
including at the shipped `Transact(11, 4, 6)` shape and for a partially-filled
`TreeUpdateBatch(11, 8)`.

Scope limits: `FrontierRoot` is not modelled, model-to-source correspondence is a
hand-maintained table, and the collision-resistance results rest on a hypothesis
that is itself unsatisfiable. See [lean/FIDELITY.md](lean/FIDELITY.md) and
`lean/README.md` § *What is not proved*.

## Status

Prototype. The trusted setup uses a single contributor — **not
production-safe**. A real MPC ceremony is required before mainnet use; the
package bumps to `1.0.0` once that ceremony completes.
