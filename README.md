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
| `src/4x6.circom` | `Transact(11, 4, 6)` | Spend through 4 input slots, create 6 notes | 69,635 | 2^17 |
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
just mutate                # mutation fuzzer: plant a defect in src/, expect a gate to reject it
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

### Mutation fuzzing

`just mutate` measures the gates above instead of the circuits. It rewrites one
statement of `src/` into a defect, in a private copy under `build/.mutation/`,
and runs every gate against the result:

| Operator | Defect |
|---|---|
| `drop-assert` | a `===` deleted |
| `unconstrain` | `<==` turned into `<--`: same witness, no constraint |
| `const-rhs` | a wire tied to 0 or 1 |
| `swap-index` | an array index moved to another slot |
| `loop-bound` | a loop that skips its first or last iteration |
| `flip-gate` | `(1 - s)` turned into `(s)` |
| `arith-flip` | `+` and `-` exchanged |
| `const-tweak` | a template argument or tag off by one |
| `cross-wire` | two adjacent wires transposed |

A mutant that does not compile is discarded. So is one that compiles to the
original constraint system, byte for byte or with its intermediate signals
renamed: it proves the same statement. The renaming is found by colour
refinement and confirmed by comparing the renamed constraints exactly
(`test/mutation/isomorphic.ts`). Each remaining mutant ends in one of three
states:

- **killed**: a suite that runs the circuit fails (`unit`, `fuzz`, or `sweep`,
  the second-witness search).
- **static**: only `lint` or the `lean` citation checks reject it. CI would
  stop the change, but no test runs into the defect.
- **survived**: nothing rejects it. The run fails unless
  `test/mutation/survivors.json` accepts the mutant with a reason.

A mutant stops at its first kill, and a gate that cannot reject it is not run:
`unconstrain` leaves the witness calculator unchanged, so only the
second-witness search and lint can see it, and once lint has rejected it the
search is skipped. `--matrix` runs every gate on every mutant, which shows
which gates overlap and what the second-witness search finds on its own.

For a static or surviving mutant the run then looks for the test that is
missing: it tampers one field of several honest witnesses at a time, keeps the
inputs the shipped circuit rejects, and reports any the mutant accepts. A
mutant with no such input is either equivalent to the original in a way the
renaming check does not cover, or differs only in the constraint system, which
the witness calculator does not exercise.

Runs learn from each other through `build/.mutation/history.json`:

- The spec that rejected a mutant last time runs first, then the specs that
  reject other mutants of the same file, then the cheapest.
- A sample is drawn from mutants that no test rejected before a change to the
  tree, then from mutants never run, then from repeats. Within those it leans
  towards the file and operator pairs that have let the most mutants through.
- `--resume` reuses the outcomes recorded for the current tree, so an
  interrupted `--all` continues where it stopped.

None of this changes a verdict: every gate able to reject a mutant still runs
before it is called a survivor. An outcome is reused only when no file a gate
reads has changed.

`FUZZ` sets the sample size (`light`, `medium`, `heavy` = 8, 40, 160 mutants);
`--all` runs every mutant. Each run prints the ids it tested, and `just mutate
--only <id>` replays one. After adding a test for a survivor, re-run it by id;
to accept one instead, `just mutate --update --only <id>` and fill in the
`reason`.

CI runs a `heavy` sample nightly (`.github/workflows/mutate.yml`) and carries
the history from run to run in the Actions cache, so successive nights take
mutants not yet run against the current tree. It can be dispatched by hand
with extra arguments, for instance `--all --resume` repeated until the history
covers `src/`.

`test/tooling/mutation_selftest.test.ts` checks that every operator finds
statements to mutate, that every gate has specs to run, that the history only
reorders, and the renaming check against circuits that are and are not
equivalent.
