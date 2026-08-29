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

### Published artifacts

The npm package ships one shape. Its 2^17 zkey is by far the largest file in the
tarball, so dropping from three shapes to one is most of what an install pays
for.

| Export                          | File                               |
|---------------------------------|------------------------------------|
| `./4x6/4x6.wasm`                | `build/4x6.wasm`                   |
| `./4x6/4x6_final.zkey`          | `build/4x6_final.zkey`             |
| `./4x6/verification_key.json`   | `build/4x6_verification_key.json`  |

The golden vectors ship too, as the cross-repo contract the SDK checks itself
against — see [vectors/](vectors/) and `just vectors`:

| Export                                | File                                |
|---------------------------------------|-------------------------------------|
| `./vectors`                           | `vectors/index.json`                |
| `./vectors/transact-4x6.json`         | `vectors/transact-4x6.json`         |
| `./vectors/tree-update-batch-8.json`  | `vectors/tree-update-batch-8.json`  |

`tree_update_batch` has no npm export. It is relayer-side only, and ships as a
GitHub release asset: the `.wcd` witness graph the relayer evaluates (see [The
witness graph](#the-witness-graph)), the `.zkey`, its verification key and
`.r1cs`, and `TreeUpdateBatchVerifier.sol`. The release also carries 4x6's
`.r1cs` and `Verifier4x6.sol`, which the package omits.

## Development

Everything is driven by [`just`](justfile); `just --list` is the full menu.

| Command | What it does |
|---|---|
| `just test-unit` | 190 witness-level tests (mocha + `circom_tester`), excluding fuzz. |
| `just test-fuzz` | Property-based suites. Tier via `FUZZ=light\|medium\|heavy`. |
| `just compile-4x6 compile-batch` | Build the `.r1cs` / `.wasm` / `.sym` for both shapes. |
| `just all-tree` | Compile *and* run both trusted setups. Re-runs the ceremony. |
| `just budget` | Gate the constraint counts against [budget.json](budget.json). Needs the `.r1cs`. |
| `just build-graph` | Build `tree_update_batch.wcd`, the witness-calculation graph the relayer proves against. |
| `just vectors` / `just vectors-check` | Regenerate the golden vectors, or diff a regeneration against the committed ones. |
| `just lint` | circomspect over `src/lib` and the entry points. |
| `just lean-check` | The whole Lean development: build, axiom guard, layout dumps, citations. |
| `just picus-all` | Under-constrainedness check on the compiled R1CS (needs Docker). |

CI runs `test-unit`, `vectors-check`, the compile + budget gate, `build-graph`, and
circomspect on every pull request; the Lean checks run when `lean/**` or `src/**`
changes. Picus and the heavy fuzz tier run nightly.

### The witness graph

The relayer does not run the circom `.wasm` witness generator. It evaluates
`tree_update_batch.wcd`, built by `just build-graph` from
[iden3/circom-witnesscalc](https://github.com/iden3/circom-witnesscalc) and shipped
as a release asset. At `TreeUpdateBatch(11, 8)` one witness costs about 15 ms that
way against roughly 170 ms through the wasm generator, and the relayer no longer
embeds a wasm runtime. Add ~7 ms for deserialising the graph, which the upstream
API repeats per call rather than once per process.

The two paths produce **bit-identical** witnesses on the golden vectors, which is
the property that matters: the zkey indexes signals positionally, so a reordered
or differently-padded witness would be a silently wrong proof rather than an
error.

The builder cannot store a function result directly into a signal, so the circuits
write `var tag = TAG_LEAF(); h.inputs[0] <== tag;` rather than assigning the call
straight across. The call folds to a constant either way and the `.r1cs` is
byte-identical, so this costs nothing — but inlining one back breaks `build-graph`,
which is why CI runs it.

`build-graph` re-runs the circom front end through a different code path, so it also
emits its own `.r1cs` and diffs it against `compile-batch`'s. A graph built from a
different constraint system than the zkey would produce witnesses that fail
verification, and that diff turns it into a build failure instead.

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
