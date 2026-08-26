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

| Circuit                                              | Constraints | Wires  | Private inputs |
|------------------------------------------------------|------------:|-------:|---------------:|
| `2x2.circom` — `Transact(10, 2, 2)`                  |      44,406 | 44,475 |            143 |
| `3x3.circom` — `Transact(10, 3, 3)`                  |      65,523 | 65,624 |            210 |
| `4x4.circom` — `Transact(10, 4, 4)`                  |      86,680 | 86,813 |            277 |
| `tree_update_batch.circom` — `TreeUpdateBatch(10, 4)` |      57,106 | 57,054 |             62 |

`3x3.circom` is the deployed transact shape; `2x2.circom` is a second
instantiation of `Transact`, and the shape the Lean satisfiability witnesses are
built at. `4x4.circom` is a third instantiation: published as an npm artifact, a
release asset and a golden vector, and covered by the Lean development —
soundness, binding, a satisfying witness and a layout dump — but **not deployed**.
Nothing verifies it on-chain until `PubInputs.sol` gains a 53-slot compress
overload. It is also the shape that fixes the `N_IN, N_OUT ≤ 4` bound the proofs
carry.

All but `4x4` fit the 2^16 FFT domain, and `just budget` holds each to its exact
count in [budget.json](budget.json) so a change lands as a reviewable diff.
`Transact(10, 4, 4)` is 21,147 constraints past the 65,533 ceiling, so `setup-4x4`
fetches its own 2^17 ptau and its proofs cost roughly twice a 3x3 proof.
`Transact(10, 3, 3)` clears the domain by **10** constraints: snarkjs sizes the
domain from `nConstraints + nPubInputs + nOutputs`, so the ceiling for 2^16 is
65,533, not 65,536. Treat it as a cliff — a per-slot gadget change is multiplied
by six. (`just budget` reports 13, because it compares the raw count against the
domain; see `src/README.md` §12.)

Each has exactly one public *input* — the Fiat–Shamir challenge `z` — and one
public *output*, `y`. circom orders main outputs before main public inputs, so
the generated Groth16 verifier takes `_pubSignals = [y, z]`, in that order.

### Published artifacts

`2x2`, `3x3` and `4x4` prover artifacts ship in the npm package, under these
export subpaths:

| Export                            | File                               |
|-----------------------------------|------------------------------------|
| `./2x2/2x2.wasm`                  | `build/2x2.wasm`                   |
| `./2x2/2x2_final.zkey`            | `build/2x2_final.zkey`             |
| `./2x2/verification_key.json`     | `build/verification_key.json`      |
| `./3x3/3x3.wasm`                  | `build/3x3.wasm`                   |
| `./3x3/3x3_final.zkey`            | `build/3x3_final.zkey`             |
| `./3x3/verification_key.json`     | `build/3x3_verification_key.json`  |
| `./4x4/4x4.wasm`                  | `build/4x4.wasm`                   |
| `./4x4/4x4_final.zkey`            | `build/4x4_final.zkey`             |
| `./4x4/verification_key.json`     | `build/4x4_verification_key.json`  |

The tarball is ~56 MB packed, ~107 MB unpacked: `3x3` accounts for ~30 MB of
that and `4x4` for ~42 MB, since a 2^17 zkey is roughly 1.4x a 2^16 one even at
1.3x the constraints. Every install pays for all three shapes.
`tree_update_batch` is published only as a GitHub release asset, alongside the
`.r1cs` and `Verifier*.sol` for each circuit.

The golden vectors ship too, as the cross-repo contract the SDK checks itself
against — see [vectors/](vectors/) and `just vectors`:

| Export                                | File                                |
|---------------------------------------|-------------------------------------|
| `./vectors`                           | `vectors/index.json`                |
| `./vectors/transact-2x2.json`         | `vectors/transact-2x2.json`         |
| `./vectors/transact-3x3.json`         | `vectors/transact-3x3.json`         |
| `./vectors/transact-4x4.json`         | `vectors/transact-4x4.json`         |
| `./vectors/tree-update-batch-4.json`  | `vectors/tree-update-batch-4.json`  |

> **Known issue.** `package.json` still names `tree-update-batch-8.json` in both
> `files` and `exports`, a filename left over from `MAX_L = 8`. The generator
> writes `tree-update-batch-${MAX_L}.json`, so the batch vector is currently
> excluded from the package by the `files` whitelist and that export path
> resolves to nothing. `scripts/check-artifacts.ts` validates `vectors/index.json`
> against the files on disk but never against `package.json`, which is why the
> gate does not catch it.

`3x3` is not wired on-chain: it needs a 42-slot `PubInputs.compress` overload
(see [src/3x3.circom](src/3x3.circom)).

## Development

Everything is driven by [`just`](justfile); `just --list` is the full menu.

| Command | What it does |
|---|---|
| `just test-unit` | 196 witness-level tests (mocha + `circom_tester`), excluding fuzz. |
| `just test-fuzz` | Property-based suites. Tier via `FUZZ=light\|medium\|heavy`. |
| `just compile compile-3x3 compile-4x4 compile-batch` | Build the `.r1cs` / `.wasm` / `.sym` for all four shapes. |
| `just budget` | Gate the constraint counts against [budget.json](budget.json). Needs the `.r1cs`. |
| `just vectors` / `just vectors-check` | Regenerate the golden vectors, or diff a regeneration against the committed ones. |
| `just lint` | circomspect over `src/lib` and the entry points. |
| `just lean-check` | The whole Lean development: build, axiom guard, layout dumps, citations. |
| `just picus-all` | Under-constrainedness check on the compiled R1CS (needs Docker). |

CI runs `test-unit`, `vectors-check`, the compile + budget gate, and circomspect on
every pull request; the Lean checks run when `lean/**` or `src/**` changes. Picus
and the heavy fuzz tier run nightly.

Tests are witness-level: `circom_tester` generates a witness and checks the
constraints. It cannot detect an under-constrained signal — that class is covered
by Picus and by the Lean proofs, which quantify over every satisfying assignment
rather than the one an honest prover produces.

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
including at the deployed `3x3` shape, at `4x4`, and for a partially-filled
batch.

Scope limits: `FrontierRoot` is not modelled, model-to-source correspondence is a
hand-maintained table, and the collision-resistance results rest on a hypothesis
that is itself unsatisfiable. See [lean/FIDELITY.md](lean/FIDELITY.md) and
`lean/README.md` § *What is not proved*.

## Status

Prototype. The trusted setup uses a single contributor — **not
production-safe**. A real MPC ceremony is required before mainnet use; the
package bumps to `1.0.0` once that ceremony completes.
