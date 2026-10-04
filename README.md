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

Each circuit has one public input, the Fiat-Shamir challenge `z`, and two public
outputs: `y`, the evaluation of its coefficients at `z`, and `digest`, a
Poseidon commitment to those coefficients. circom orders main outputs before
main public inputs, so the generated verifier takes
`_pubSignals = [y, digest, z]`, in that order.

### Constraint counts

R1CS totals on BN254 (`snarkjs r1cs info`):

| Circuit | Constraints | Wires | Private inputs |
|---|---:|---:|---:|
| `Transact(11, 4, 6)` | 69,291 | 69,422 | 247 |
| `TreeUpdateBatch(11, 8)` | 41,521 | 41,466 | 69 |

snarkjs sizes the FFT domain from `nConstraints + nPubInputs + nOutputs` and
requires the sum to be at most `domain - 1`, so with one public input and two
public outputs the ceiling on the constraint count is `domain - 4`. `Transact`
sits in **2^17** (ceiling 131,068) and clears it by 61,777. `TreeUpdateBatch`
sits in **2^16** (ceiling 65,532) and clears it by 24,011. `just budget` pins
both to their exact counts and domains in [budget.json](budget.json), so growth
lands as a reviewable diff rather than a silent doubling of proving time.

The two share a tree depth but not a ptau. `TreeUpdateBatch` inserts its leaves
in one batched build, so its tree work grows with depth rather than leaf count:
a depth level costs 2,534 constraints and a leaf slot about 1,800. 2^16 therefore
holds through depth 20 at `MAX_L = 8`, and through `MAX_L = 16` (56,026) at
depth 11.

## What the circuits bind, in brief

A note commits to its asset and value by hash:

```
inner = Poseidon(TAG_INNER, pk, rho, rcm)
cm    = Poseidon(TAG_CM, asset_id · 2^64 + value, inner)
```

and `cm` is the commitment-tree leaf. There are no value commitments and no
curve arithmetic in either circuit.

- A **spend** opens `cm` from the note and proves it is in the tree, so it can
  claim only the asset and value the leaf was inserted for.
- A **deposit** publishes `inner` beside its public asset and amount, and
  `TreeUpdateBatch` hashes the three into the leaf. The binding holds for any
  set of registered asset ids; id `0` is reserved for "no asset" and must not be
  registered.
- A **transfer** publishes no asset id: `public_asset_id` is `0` unless
  something is withdrawn.
- Each circuit outputs a Poseidon **digest** of its coefficients as a public
  signal, and calldata carries the same word. The contract hashes it into `z`
  and passes it to the verifier, which commits the witness before the challenge
  exists; that is what makes the compression bind the proof to the calldata. A
  consumer must hash that word, must not evaluate it, and never recomputes it.
  See [src/README.md § 2a](src/README.md#2a-public-input-compression).

On a deposit slot the calldata word is `inner`, not the leaf. A consumer that
rebuilds the tree must compute the leaf; `vectors/tree-update-batch-8.json`
publishes both per slot.

## Formal verification

The circuits have machine-checked soundness proofs in Lean 4
([`lean/`](lean/README.md), run with `just lean-check`). The proofs quantify
over every assignment satisfying the modelled constraints, which is the
under-constrained-signal class a test suite cannot reach.

Headline results:

- Per-asset value conservation holds for every asset id, as an exact integer
  equation over the naturals. The transparent bucket is output-side only, so an
  asset on no input can be neither created nor withdrawn.
- `public_out = 0` exactly when `public_asset_id = 0`: the constrained direction
  and the one that follows from balance.
- Under Poseidon collision resistance, a circuit's public digest determines its
  whole coefficient vector; and two distinct coefficient vectors agree at no
  more than 12 challenges for transact, 35 for the batch. Those are the two
  ingredients of the calldata-binding argument.
- A deposit leaf has one `(asset, value, inner)` opening, and a spend that opens
  it spends exactly that amount of that asset.
- `TreeUpdateBatch` advances the root by exactly `actual_count` appends, for any
  count.

Conservation and the PolyEval results assume only that the BN254 scalar field is
prime, and nothing about Poseidon. Collision resistance is an explicit
hypothesis, never an axiom, and a build-time guard rejects any axiom outside
[lean/expected/axioms.txt](lean/expected/axioms.txt); with the curve gone, the
trusted base is primality of the field. Every soundness result is paired with a
satisfying assignment, so none is vacuous.

Not covered: the step that joins those two ingredients, the standard
random-oracle argument for a challenge hashed after a commitment, which is not
formalised; the `EMPTY_SUBTREE` constants (the batch
result assumes they form the empty-subtree chain, which
`test/gadgets/merkle.test.ts` checks numerically); and the model-to-source
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

### Fuzzing

`just test-fuzz` runs the property suite. Trial counts come from `FUZZ`
(`light` / `medium` / `heavy` = 5 / 20 / 100), with `FUZZ_RUNS_<SUITE>=N` as a
per-suite override.

Each run pins one fast-check seed across every property and prints it on
stderr, so a failure is reproducible:

```bash
FUZZ=heavy FUZZ_SEED=1234 just test-fuzz
```

CI picks the seed from the run id and writes the replay command into the job
summary, so a nightly failure stays reproducible after the logs expire.

### Underconstraint search

`just underconstrained` searches for a SECOND witness the R1CS accepts.

The tamper and fuzz suites mutate the circuit's input object and require the
witness calculator to reject. That tests the witness generator. A Groth16 proof
binds the constraint system instead, and the two are not the same artifact: a
signal a template computes with `<--` but never constrains is one a prover picks
freely, and no input the generator accepts can reveal it, because the generator
turns every input it accepts into a self-consistent witness.

So this suite starts from an honest witness and edits the witness VECTOR. Every
search reduces to one question — given a direction `v`, which steps `t` keep
`w + t·v` satisfying? — which each constraint answers exactly, as a quadratic in
`t` whose constant term vanishes because `w` is honest.

- **Single-signal**: the unit vectors, so all ~70k witness entries, each decided
  exactly with everything else held fixed.
- **Multi-signal**: the null space of the Jacobian restricted to each gadget and
  each constraint. A null vector is a direction whose first-order effect cancels
  everywhere at once — exactly the freedom the unit sweep cannot see, because
  along it every individual signal is still pinned by the others.
- **Bit decompositions**: recovered from the coefficients of the `--O0` build and
  checked for a width past `2^253` (where the bits of `v` and `v + p` both
  satisfy the sum) and for digits carrying no booleanity constraint.

A differing output or public input is a soundness break. A differing intermediate
is malleability, and each one must be EXPLAINED by a rule that states a
precondition and has it verified against the witness — not by a list of accepted
signal names.

Remaining gap: the group search holds everything outside a group fixed, and null
directions are straight lines, so freedom spanning unrelated components or lying
along a curved variety is out of reach. `just picus` decides the general case.

`test/tooling/underconstrained_selftest.test.ts` points each check at a circuit broken in
exactly the way that check exists to find, so a detector that silently matches
nothing fails rather than reporting a clean bill of health. One fixture is built
so the single-signal sweep MUST miss it — each signal of a pair is pinned while
the other holds still — which is what keeps the multi-signal search honest.
