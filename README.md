# Lelantos Circuits

Groth16 circuits and prover artifacts for the Lelantos multi-asset shielded pool,
written in circom over the BN254 scalar field.

> **Prototype.** The phase-2 setup has a single contributor, who can forge
> proofs. A multi-party ceremony is required before mainnet use. The package
> moves to `1.0.0` once it completes.

| Document | Contents |
|---|---|
| [src/README.md](src/README.md) | Circuit specification, security goals, public-input layout, contract obligations |
| [lean/README.md](lean/README.md) | Lean 4 soundness proofs |
| [lean/FIDELITY.md](lean/FIDELITY.md) | Correspondence between the Lean model and the circom source |

## Installation

```bash
npm install @lelantos-org/circuits
```

| Export | Contents |
|---|---|
| `@lelantos-org/circuits/4x6/4x6.wasm` | Witness generator |
| `@lelantos-org/circuits/4x6/4x6_final.zkey` | Proving key |
| `@lelantos-org/circuits/4x6/verification_key.json` | Verification key |
| `@lelantos-org/circuits/vectors` | Vector index with a SHA-256 per file |
| `@lelantos-org/circuits/vectors/transact-4x6.json` | Transact test vector |
| `@lelantos-org/circuits/vectors/tree-update-batch-8.json` | Batch test vector |

Each vector carries the witness, the coefficient vector, the Fiat-Shamir
challenge, and the `y` and `digest` produced by the compiled circuit. Consumers
check their own implementation against them.

## Circuits

| Circuit | Instantiation | Purpose | Constraints | Domain |
|---|---|---|---:|---:|
| `src/4x6.circom` | `Transact(11, 4, 6)` | Spend through 4 input slots, create 6 notes | 69,291 | 2^17 |
| `src/tree_update_batch.circom` | `TreeUpdateBatch(11, 8)` | Advance the commitment tree by 1 to 8 leaves | 41,521 | 2^16 |

The two circuits are paired. A spend emits 6 leaves that the batch circuit
inserts, both use tree depth 11, and both must come from the same release.

Each circuit has one public input, the Fiat-Shamir challenge `z`, and two public
outputs: `y`, the evaluation of its coefficient vector at `z`, and `digest`, a
Poseidon commitment to that vector. The generated verifier takes
`_pubSignals = [y, digest, z]`, in that order.

## Integration notes

A note commits to its asset and value by hash, and `cm` is the tree leaf:

```
inner = Poseidon(TAG_INNER, pk, rho, rcm)
cm    = Poseidon(TAG_CM, asset_id · 2^64 + value, inner)
```

- The calldata carries the `digest` word. The contract hashes it into `z` and
  passes it to the verifier unmodified. It is not evaluated into `y` and is not
  recomputed on chain.
- On a deposit slot the batch calldata word is `inner`, not the leaf. A consumer
  that rebuilds the tree computes the leaf from `(leaf_asset, leaf_public_in,
  inner)`. `vectors/tree-update-batch-8.json` publishes both per slot.
- `public_asset_id` is `0` unless a withdrawal takes place. Asset id `0` is
  reserved and must not be registered.

The full specification is in [src/README.md](src/README.md).

## Formal verification

The Lean 4 development in [`lean/`](lean/README.md) proves, for every assignment
satisfying the modelled constraints:

- per-asset value conservation, as an exact integer equation, for every asset id;
- `public_out = 0` if and only if `public_asset_id = 0`;
- under Poseidon collision resistance, the public digest determines the
  coefficient vector, and two distinct coefficient vectors agree on at most 12
  challenges for transact and 35 for the batch;
- a deposit leaf has a unique `(asset, value, inner)` opening;
- `TreeUpdateBatch` advances the root by exactly `actual_count` appends.

The trusted base is primality of the BN254 scalar field. Collision resistance
is a hypothesis of the theorems that use it, not an axiom. Scope and limits are
listed in [lean/README.md](lean/README.md#what-is-not-proved).

`just picus` checks the compiled R1CS for under-constrained outputs.

## Development

```bash
just build-artifacts-4x6   # compile and run phase-2 setup for the transact circuit
just test                  # TypeScript suite over the compiled circuits
just test-fuzz             # property-based suite
just underconstrained      # second-witness search over the R1CS
just budget                # constraint budget gate (budget.json)
just lint                  # circomspect
just lean-check            # Lean build, axiom guard, layout and citation checks
just vectors-check         # regenerate vectors/ and diff against the committed files
just picus-all             # Picus weak-safety check (requires Docker)
```

`just --list` shows every recipe. Rebuild recipes re-run the single-contributor
setup and invalidate existing proofs and committed fixtures.

### Fuzzing

Trial counts are set by `FUZZ` (`light`, `medium`, `heavy` = 5, 20, 100) and
overridden per suite with `FUZZ_RUNS_<SUITE>=N`. Each run uses one fast-check
seed, printed on stderr. To replay:

```bash
FUZZ=heavy FUZZ_SEED=1234 just test-fuzz
```

CI derives the seed from the run id and writes the replay command to the job
summary.

### Under-constraint search

`just underconstrained` starts from an honest witness and searches for a second
witness the R1CS accepts, with three checks:

- **Single signal.** Each witness entry is varied with all others fixed.
- **Multiple signals.** The null space of the Jacobian restricted to each
  gadget and each constraint gives directions along which several signals move
  together.
- **Bit decompositions.** Recovered from the `--O0` build and checked for
  widths that admit a second decomposition modulo `p` and for digits without a
  booleanity constraint.

A differing output or public input is a soundness failure. A differing
intermediate signal must match a rule whose precondition is verified against
the witness.

The search is local to a gadget and linear in direction. Freedom spanning
unrelated components is covered by `just picus`.
`test/tooling/underconstrained_selftest.test.ts` runs each check against a
fixture circuit containing the defect that check targets.
