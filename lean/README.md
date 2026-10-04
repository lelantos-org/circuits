# Lean 4 soundness proofs

Machine-checked proofs for `Transact(DEPTH, N_IN, N_OUT)` and
`TreeUpdateBatch(DEPTH, MAX_L)`. Each result is proved for the generic template
and instantiated at the shipped shapes: `Transact(11, 4, 6)` (`src/4x6.circom`)
and `TreeUpdateBatch(11, 8)`.

The theorems hold for every assignment satisfying the modelled constraint
system, not only for witnesses an honest prover generates. This covers
under-constrained signals, which witness-generation tests do not detect.

| Theorem | Statement | Depends on |
|---|---|---|
| `transact_sound` | `TransactSat w → TxWellFormed w` | `p_prime` |
| `transact_binding` † | `TransactSat w → TxBinding w` | `p_prime`, `¬ PoseidonCollision` |

- `TxWellFormed`: per-asset conservation over ℕ, ownership, Merkle membership,
  64-bit ranges, a shared root, `rho` derivation, the digest, and `PolyEval` at
  `z ≠ 0`.
- `TxBinding`: pairwise-distinct output `rho`, binding membership, binding `cm`.

[FIDELITY.md](FIDELITY.md) describes how the model corresponds to the circom
source.

## Running the checks

```
cd lean
./scripts/check-all.sh            # or: just lean-check
```

| Command | Checks |
|---|---|
| `lake build` | Elaborates and kernel-checks every proof; runs the axiom guard over every declaration |
| `./scripts/check-axioms.sh` | The trusted base matches `expected/axioms.txt` |
| `./scripts/dump-layout.sh` | The transact and batch layouts match `expected/layout-*.txt` |
| `python3 lean/scripts/check-prime.py` | Verifies the primality axiom externally |
| `python3 lean/scripts/check-citations.py` | Every source-line citation resolves |
| `python3 lean/scripts/check-coverage.py` | Every `===` and `<==` the circom emits is cited in `lean/` |
| `python3 lean/scripts/check-names.py` | Every `Lelantos` name cited in prose exists |

CI runs the same set ([.github/workflows/lean.yml](../.github/workflows/lean.yml)).

## What is proved

Rows marked **†** take `¬ PoseidonCollision` as a hypothesis. That hypothesis is
unsatisfiable (`poseidon_collision`), so these rows record an assumption; see
[What is not proved](#what-is-not-proved). Unmarked rows are unconditional.

Paths are relative to `Lelantos/`.

### Top-level

All in `Circuit/Transact.lean`.

| Theorem | Statement |
|---|---|
| `transact_sound` | `TransactSat w → TxWellFormed w`, for `N_IN ≤ 7` and `N_OUT ≤ 7` |
| `transact4x6_sound` | The same at `Transact(11, 4, 6)` |
| `transact_binding` † | `TransactSat w → TxBinding w` |

The bound of 7 comes from the proof, not the circuit: `two_pow_67_lt_p` bounds
the balance sums by `8 · 2^64 < p`. A wider shape requires a larger power of two
in `Model/Field.lean`.

### Value conservation

| Theorem | Where | Statement |
|---|---|---|
| `perAssetValueBalance_all_assets` | `Gadgets/Balance.lean` | The `N_IN + N_OUT + 1` candidate checks imply conservation for every asset id in the field |
| `perAssetValueBalance_nat` | `Gadgets/Balance.lean` | The equation holds over ℕ, not only modulo `p` |
| `no_asset_creation` | `Circuit/Transact.lean` | An asset on no input appears on no output with a non-zero value |
| `no_asset_withdrawal` | `Circuit/Transact.lean` | An asset on no input cannot be withdrawn through the transparent bucket |

The equation is `Σ in = Σ out + public_out`. These results depend on `p_prime`
and the 64-bit range checks, and on no hash assumption.

### Transparent bucket

All in `Circuit/Transact.lean`.

| Theorem | Statement |
|---|---|
| `publicBucket_zero_asset` | `public_out = 0 ⇒ public_asset_id = 0`, from the bucket constraint |
| `publicBucket_zero_out` | `public_asset_id = 0 ⇒ public_out = 0`, from conservation at id 0, the `asset ≠ 0` rules and `DummyZeroValue` |
| `publicBucket_zero_iff` | Both directions |

### Per-slot soundness

| Theorem | Where | Statement |
|---|---|---|
| `spentNote_sound` | `Circuit/Spent.lean` | A non-dummy slot proves ownership and Merkle membership of its commitment |
| `spentNote_assetRange`, `spentNote_valueRange` | `Circuit/Spent.lean` | Both packed fields are 64-bit on every input slot, dummies included |
| `outputNote_sound` | `Circuit/Output.lean` | An output's `cm` is the commitment of its note, with a non-zero 64-bit asset id and a 64-bit value |
| `merkleProofOrDummy_sound` | `Gadgets/Merkle.lean` | A non-dummy slot's leaf is under the root |
| `num2Bits_sound` | `Model/Bits.lean` | `2ⁿ ≤ p` makes the decomposition alias-free |
| `pathIndexSelectors_sound` | `Gadgets/Common.lean` | The selector is one-hot at `path_index` |
| `packAV_inj` | `Gadgets/Note.lean` | `(asset, value)` packing is injective given the two range checks |
| `slots_inj` | `Gadgets/Merkle.lean` | Inserting at a fixed position is injective |

### Public-input compression

The public signals of both circuits are `(y, digest, z)`. `z` is the challenge,
`y` is the evaluation of the coefficient vector at `z`, and `digest` is the
`CoeffDigest` of the same vector, a `Poseidon(5)` fold.

| Circuit | Coefficients | Challenge preimage |
|---|---:|---|
| `4x6` | 13 | 38 words: the coefficients, the digest word, 24 challenge-only words |
| `tree_update_batch` | 36 | 37 words: the coefficients, the digest word |

| Theorem | Where | Statement |
|---|---|---|
| `polyEval_sound` | `Gadgets/PolyEval.lean` | The Horner chain computes `Σ cₖ zᵏ` |
| `polyEvalSat_z_ne_zero` | `Gadgets/PolyEval.lean` | The challenge is nonzero |
| `polyEval_binding` | `Gadgets/PolyEval.lean` | Coefficient vectors differing below `n` agree on at most `n - 1` challenges |
| `polyEval_forge`, `polyEval_not_binding` | `Gadgets/PolyEval.lean` | One coefficient chosen after the challenge sends `y` to any target at a nonzero `z`, so the evaluation alone does not bind |
| `coeffDigest_sound` | `Gadgets/CoeffDigest.lean` | The `Poseidon(5)` block chain computes `coeffDigest` of its input words |
| `digest_inj` † | `Gadgets/CoeffDigest.lean` | Equal `CoeffDigest(m)` outputs force equal length-`m` inputs |
| `transact_digest_public` | `Circuit/Transact.lean` | The public `digest` of a satisfying witness is `coeffDigest` of its coefficient vector |
| `txCoeffs_determined_by_digest` †, `slotValue_determined_by_digest` † | `Circuit/Transact.lean` | Two satisfying witnesses with the same public digest have the same coefficient vector; stated per vector and per named public input |
| `transact_calldata_binding` † | `Circuit/Transact.lean` | A calldata vector whose `coeffDigest` is the public digest of a satisfying witness is that witness's coefficient vector |
| `transact_pi_binding`, `transact_pi_binding_slot` | `Circuit/Transact.lean` | Two transactions with different coefficient vectors share `(z, y)` for at most `piCount - 1` challenges, 12 at the shipped shape |
| `transact_calldata_pi_binding` | `Circuit/Transact.lean` | A calldata vector differing from the witness's evaluates to the proof's `y` at the proof's `z` for at most `piCount - 1` challenges |
| `piSlot_slotIndex`, `slotIndex_piSlot` | `Circuit/Layout.lean` | `slotIndex` is the two-sided inverse of the coefficient layout |

The batch counterparts are listed in the next section.

**Calldata binding.** The contract reads the digest word `d` from calldata,
derives `z = keccak(coefficients, d, challenge-only words) mod r`, computes `y`
over the calldata coefficients, and verifies the proof against `(y, d, z)`. The
proof shows a witness `w` with `CoeffDigest(w) = d` and `Σ wₖ zᵏ = y`. (`r` is
the BN254 scalar-field modulus, `p` in the Lean sources.)

1. `d` is in the preimage of `z`. Under collision resistance of the fold, the
   prover knows one coefficient vector with digest `d`, so the witness vector is
   fixed before `z`.
2. The calldata vector `c` is in the preimage of `z`. If `w ≠ c`, they are
   distinct polynomials of degree below `N` fixed before `z` and agree there
   with probability at most `(N − 1)/r`: `12/r` for `4x6`, `35/r` for the batch.

Lean proves that the public digest is the `CoeffDigest` of the witness vector,
that the digest binds the vector (†), and that distinct vectors agree on at most
`N − 1` challenges. The step combining them, the Fiat-Shamir random-oracle
argument over keccak256, is not formalised.

The argument requires three conditions of the contract, recorded in
`ContractObligations` and `BatchContractObligations`:
`digest_passed_unmodified` (stated), `digest_in_challenge` (stub) and
`coefficients_in_challenge` (stub).

The challenge-only words (`recipient`, `chainId`, `payer`, `relayer`, the intent
hash, the FMD clue triples, the payload digest) are not signals of `4x6.circom`
and are not coefficients. `piCount` is the coefficient count.

`TransactSat.not_all_dummy` records that the circuit rejects a witness whose
input slots are all dummies; `TxWellFormed.someRealInput` is the consequence.

### `tree_update_batch.circom`

`Circuit/TreeUpdateBatch.lean` defines the constraint system `BatchSat`. The
tree gadget `BatchAppend` (`Gadgets/BatchAppend.lean`) is proved against the
specification in `Spec/QuatTree.lean`. Every result takes a `BatchShape`, the
numeric side conditions of an instance.

In `Circuit/TreeUpdateBatch.lean`:

| Theorem | Statement |
|---|---|
| `batch_count_range` | `actual_count ∈ [1, MAX_L]` |
| `batch_active_spec` | `active[k]` is the indicator of `k < actual_count` |
| `batch_padding_zero` | Every field of an inactive slot is zero |
| `batch_spend_fields_zero` | A spend slot carries no `leaf_asset` and no `leaf_public_in` |
| `batch_deposit_leaf` | A deposit slot's leaf is `NoteCommitment(leaf_asset, leaf_public_in, cms[k])` |
| `batch_spend_leaf` | A spend slot's leaf is `cms[k]` |
| `batch_no_value_under_zero` | `leaf_asset = 0 ⇒ leaf_public_in = 0` |
| `batch_deposit_opening_unique` † | A note commitment equal to a deposit leaf has that leaf's `(leaf_asset, leaf_public_in)` and `inner` |
| `batch_deposit_spend_binds` † | A `SpentNote` slot whose commitment is that leaf spends exactly `leaf_public_in` units of `leaf_asset` |
| `batch_capacity` | `start_index + actual_count ≤ 4^DEPTH` |
| `batch_frontier_canonical` | Every `frontier_in` slot at or above its level's digit is zero |
| `batch_old_root` | `old_root` is the tree holding `start_index` leaves with this frontier |
| `batch_advances_by_count` | `new_root` is that tree after appending exactly the first `actual_count` leaves |
| `batch_advances_at_positions` | The same root as `appendRoot`, a run of single-leaf `InsertsTo` steps at positions `start_index + k` |
| `batch_new_root_determined` † | Two proofs with the same `old_root`, `start_index`, `actual_count`, `cms`, `leaf_asset`, `leaf_public_in` and `is_deposit` reach the same `new_root` |
| `batch_compression`, `batch_challenge_nonzero` | `y` is the evaluation of the 36-coefficient layout at a nonzero `z` |
| `batch_digest_public` | The public `digest` of a satisfying witness is `coeffDigest` of its 36 coefficients |
| `batchCoeffs_determined_by_digest` †, `batchSlotValue_determined_by_digest` † | Two satisfying witnesses with the same public digest have the same coefficient vector |
| `batch_calldata_binding` † | A calldata vector whose `coeffDigest` is the public digest of a satisfying witness is that witness's coefficient vector |
| `batch_pi_binding`, `batch_calldata_pi_binding` | Two distinct coefficient vectors evaluate equally on at most `batchPiCount - 1` challenges, 35 at the shipped shape |
| `BatchShape.deployed` | The numeric side conditions hold at `TreeUpdateBatch(11, 8)`, `COUNT_BITS = 3` |

Supporting results:

| Theorem | Where | Statement |
|---|---|---|
| `batchPiSlot_batchSlotIndex` | `Circuit/BatchLayout.lean` | The batch coefficient layout is invertible |
| `batchAppend_sound` | `Gadgets/BatchAppend.lean` | The run fits the tree, and the gadget's roots are `batchTree` at counts `0` and `actual_count` (`batchAppend_old_root`, `batchAppend_new_root`) |
| `batchAppend_frontier_zero` | `Gadgets/BatchAppend.lean` | The frontier pin zeroes exactly the slots no digit reads |
| `batchWindow_covers` | `Gadgets/BatchAppend.lean` | The fixed window covers every start position and every count up to `MAX_L` |
| `batchTree_eq_appendRoot` | `Spec/QuatTree.lean` | The tree after the append is the root reached by a run of single-leaf `InsertsTo` steps (`append_insertsTo`, `seqFr_inv`) |
| `batchTree_frozen`, `batchTree_empty`, `batchTree_congr` | `Spec/QuatTree.lean` | A completed subtree does not change; the tree is empty past the run; the tree reads the frontier only where it is filled |
| `batchTree_frontier_inj` † | `Spec/QuatTree.lean` | The tree before the append determines every frontier slot it reads |
| `InsertsTo.unique` | `Spec/QuatTree.lean` | The insert is a function of `(leaf, digits, frontier)` |
| `lessThan_sound` | `Gadgets/Comparators.lean` | circomlib `LessThan(n)` is the comparison indicator, given `n`-bit operands |

Notes:

- **Tree results need no hash assumption.** By `InsertsTo.unique` the root is
  determined by induction on the step equation. Only the two results about the
  private frontier are †.
- **The frontier is private and bound.** Under collision resistance the public
  `old_root` determines every frontier slot a root reads
  (`batchTree_frontier_inj`), so `new_root` is a function of the public
  statement (`batch_new_root_determined`).
- **`new_root` is not injective in the coefficients.** A zero leaf equals the
  empty leaf. The batch therefore has its own `CoeffDigest` public signal, and
  the calldata-binding argument applies with `N = 36`.
- **`ZerosCoherent`.** The advance results assume that the `EMPTY_SUBTREE`
  constants form the empty-subtree chain. This is a hypothesis about a
  compile-time table. `ZerosCoherent.eq_emptyChain` shows it determines the
  table, and `batch_advances_witness` discharges it together with `BatchSat` on
  one assignment.
- **`is_deposit` is constrained only to be boolean.** `batch_deposit_leaf`
  assumes `is_deposit[k] = 1` and `batch_spend_leaf` assumes `0`. Either value
  satisfies `BatchSat` on any slot. The contract fixes it
  (`BatchContractObligations.is_deposit_pinned`).
- **The batch inputs are not pinned by the circuit.** `old_root`, `start_index`,
  `actual_count` and the leaf fields are inputs, and every result above is
  conditional on them. `BatchContractObligations` records the contract-side
  checks: `old_root_is_live`, `start_index_is_committed_count`,
  `count_matches_payload`, `is_deposit_pinned` and `leaves_match_escrow`, stubs
  naming `MASP._requireTreePosition`, `MASP._validateBatchHeader` and
  `MASP._drainDeposit`. No theorem assumes them.

### Hash binding †

| Theorem | Where | Statement |
|---|---|---|
| `nullifier_binds_cm` † | `Gadgets/Note.lean` | `cm` is in the nullifier preimage |
| `noteCommitment_inj` † | `Gadgets/Note.lean` | `cm` binds `(asset_id, value, inner)`, given both 64-bit range checks |
| `noteInner_inj` † | `Gadgets/Note.lean` | `inner` binds `(pk, rho, rcm)` |
| `noteCm_inj` † | `Gadgets/Note.lean` | `cm` binds all five note fields |
| `merkleMember_inj` † | `Gadgets/Merkle.lean` | The root binds the leaf at a position |
| `merkleNode_inj` † | `Gadgets/Note.lean` | Injectivity of the Merkle node hash |
| `noteCommitment_ne_deriveRho` † | `Gadgets/Note.lean` | The two arity-3 sites are separated by their leading tags |
| `noteInner_ne_nullifier` † | `Gadgets/Note.lean` | The two arity-4 sites are separated by their leading tags |
| `noteCommitment_ne_merkleNode` † | `Gadgets/Note.lean` | A leaf is not an internal node (arity 3 against 5) |
| `digestBlock_zero_ne_merkleNode` † | `Gadgets/CoeffDigest.lean` | Block 0 of a digest is not a Merkle node |

### Non-vacuity

Each soundness result is paired with a satisfying assignment, so no hypothesis
is unsatisfiable through over-constraint in the model.

| Theorem | Where | Statement |
|---|---|---|
| `transactSat_satisfiable` | `Proofs/Completeness.lean` | `TransactSat` is satisfiable |
| `transactSat_spend_satisfiable` | `Proofs/Completeness.lean` | By a transaction moving value through a non-dummy slot with no withdrawal |
| `transactSat_withdraw_satisfiable` | `Proofs/Completeness.lean` | By a withdrawal of a non-zero amount of a non-zero asset |
| `transactSat_twoAsset_satisfiable` | `Proofs/Completeness.lean` | By a transaction moving two distinct assets from two real inputs under one root |
| `spentReal_witness` | `Proofs/Completeness.lean` | `SpentReal` is inhabited, so the `is_dummy = 0` case of `spentNote_sound` is reachable |
| `transact4x6Sat_satisfiable` | `Proofs/Completeness.lean` | At `Transact(11, 4, 6)` |
| `batchSat_satisfiable` | `Proofs/BatchCompleteness.lean` | `BatchSat` is satisfiable at `TreeUpdateBatch(11, 8)` |
| `batchSat_partial_batch` | `Proofs/BatchCompleteness.lean` | By a batch committing three leaves into eight slots |
| `batchSat_deposit_and_spend` | `Proofs/BatchCompleteness.lean` | With an active deposit of a non-zero amount and an active spend leaf |
| `batchSat_nonzero_frontier` | `Proofs/BatchCompleteness.lean` | At a start position whose frontier holds non-zero values |

The small transact assignments use a `(10, 2, 2)` shape. Every witness evaluates
at `z = 1` and carries the digest of its own coefficients.

### Rejected assignments

All in `Proofs/Rejection.lean`. Each states that no satisfying assignment exists.

| Theorem | Rejected |
|---|---|
| `inflation_rejected`, `mint_from_nothing_rejected` | Inflating or minting an asset |
| `withdraw_from_nothing_rejected` | Withdrawing an asset on no input |
| `transfer_naming_asset_rejected`, `withdraw_asset_zero_rejected` | A bucket naming an asset with nothing withdrawn; a withdrawal under id 0 |
| `oversized_input_asset_rejected`, `oversized_output_asset_rejected`, `oversized_public_rejected` | An asset id or public word at or above `2^64`, on every slot kind |
| `zero_challenge_rejected` | `z = 0` |
| `wrong_digest_rejected` | A public `digest` other than the `coeffDigest` of the witness's coefficients |

### Guards

| Theorem | Where | Statement |
|---|---|---|
| `poseidon_not_injective` | `Model/Poseidon.lean` | Literal injectivity of Poseidon is false, so it cannot be introduced as an axiom |
| `poseidon_collision` | `Model/Poseidon.lean` | A collision exists, so the † hypothesis is unsatisfiable |

## What is not proved

- **Groth16 knowledge soundness.** The theorems concern R1CS satisfaction, not
  the on-chain verifier.
- **That no forged calldata verifies.** The two halves are proved: the digest
  binds the coefficient vector (`transact_calldata_binding` †,
  `batch_calldata_binding` †), and distinct vectors agree on at most `N − 1`
  challenges (`polyEval_binding`). The Fiat-Shamir random-oracle step joining
  them is not formalised: no theorem states it, no hypothesis models keccak256
  as a random oracle, and the development does not model a prover.
- **Poseidon collision resistance.** The † rows follow from
  `¬ PoseidonCollision`, which is unsatisfiable, so as stated they are vacuous.
  The assumption is a hypothesis rather than an axiom because the axiom form is
  refutable. A non-vacuous treatment requires a concrete-security formulation
  with an explicit adversary. `transact_sound`, conservation, the range checks
  and `PolyEval` do not depend on it.
- **Separation of later digest blocks from a Merkle node.** Block 0 leads with
  `TAG_DIGEST`. A later block leads with the previous block's output, and
  separating it from `TAG_MERKLE` is a preimage statement.
- **The `EMPTY_SUBTREE` constants.** `ZerosCoherent` is assumed. Lean treats
  Poseidon as opaque; `test/gadgets/merkle.test.ts` recomputes the chain with
  circomlibjs.
- **Which batch slots are deposits.** `is_deposit` is boolean only;
  `BatchContractObligations.is_deposit_pinned` is a stub.
- **Contract obligations.** Nullifier freshness, the `chain_id` and
  `recipient_address` checks, the keccak-preimage conditions and the aux-digest
  recomputation are recorded in `Lelantos.ContractObligations` as `True` and
  assumed by no theorem. `digest_passed_unmodified` and `nullifiers_distinct`
  are stated but not proved.
- **The batch's position and payload.** Seven of the eight fields of
  `Lelantos.BatchContractObligations` are stubs.
- **Distinct notes across input slots.** Each slot is opened against the root
  independently, so one note can fill two slots. The contract rejects equal
  nullifiers (`ContractObligations.nullifiers_distinct`,
  `MASP._validateRequest`).
- **Distinct notes across leaves.** Two leaves with the same `cm` share a
  nullifier.
- **Hiding.** Nothing is proved about what a published `cm` or `inner` reveals.
- **Layout parity with the contract.** `dump-layout.sh` checks the layouts
  against Lean, and the layout-parity tests check the published vectors against
  those dumps. Agreement between the vectors and `PubInputs.sol` is not checked
  here.
- **Model constraints the circuit does not impose.** `check-coverage.py` and the
  signal map cover the opposite direction of transcription error. See
  [FIDELITY.md](FIDELITY.md), Defence 2.
- **Under-constrainedness of the compiled R1CS**, beyond the Picus result below.

## Under-constrainedness of the compiled R1CS

The proofs concern `TransactSat` and `BatchSat`, hand-written models, and not
the R1CS that circom emits. [Picus](https://github.com/Veridise/Picus) checks
the compiled artifact. Its default check is weak safety: for a fixed assignment
to the circuit's inputs, every output is uniquely determined.

`just picus-all` on 2026-10-04, over the `--O0` builds, with `y` and `digest` in
scope:

| Circuit | Wires (`--O0`) | Weak safety |
|---|---:|---|
| `4x6` | 110,397 | Properly constrained (exit `8`) |
| `tree_update_batch` | 66,042 | Properly constrained (exit `8`) |

- A verdict holds for the revision it ran on. Re-run after any change to `src/`
  (`just picus`, requires Docker). `.github/workflows/picus.yml` runs
  `just picus-all` nightly.
- Weak safety constrains the outputs, not every intermediate signal. Strong
  safety (`just picus STRONG=1`) has not been run on these circuits, and the
  `--O1` builds have not been run separately.
- Picus exits with `8` for a guarantee, `9` for a counterexample and `0` for
  unknown.

## Trusted base

| Axiom | Content |
|---|---|
| `p_prime` | The BN254 scalar-field modulus is prime |
| `propext`, `Classical.choice`, `Quot.sound` | Lean's own |

Every headline theorem depends on these or on a subset. The circuits contain no
curve arithmetic, so there is no group-law axiom, and there is no hash axiom.

- `AxiomGuard` runs at build time over every declaration in the namespace and
  fails the build on an axiom outside the allow-list.
- `check-axioms.sh` prints the axioms of each headline theorem and diffs the
  report against `expected/axioms.txt`.
- `lean/scripts/check-prime.py` verifies `p_prime` externally with a Lucas
  certificate (the factorisation of `p - 1` and a base of order `p - 1`) and
  re-checks every size bound the proofs use. Mathlib's `norm_num` cannot certify
  a 254-bit prime.

[Lelantos/Meta/Assumptions.lean](Lelantos/Meta/Assumptions.lean) documents each
axiom. [Lelantos/Model/Poseidon.lean](Lelantos/Model/Poseidon.lean) documents
why collision resistance is a hypothesis: literal injectivity is refutable, and
a `P ∨ PoseidonCollision` conclusion is trivially provable.

Two assumptions lie outside the trusted base: Poseidon collision resistance,
which appears in the † statements, and keccak256 as a random oracle, which
appears in no theorem.

## Layout

The layers form a dependency chain: `Model`, `Gadgets`, `Circuit`, `Proofs`.
`Meta` imports the whole development and is a separate build target.

```
lean/
  Lelantos.lean            root module
  Lelantos/
    Model/                 ambient objects, no circom counterpart
      Field                BN254 Fr, size bounds, p_prime
      Bits                 Num2Bits semantics and alias-freeness
      Poseidon             opaque hash, collision hypothesis, tags
    Gadgets/               one module per template family
      Comparators          IsZero, IsEqual, LessThan
      Common               PathIndexSelectors
      Note                 key chain, two-step commitment, nullifier, rho
      PolyEval             Horner soundness, z != 0, Schwartz-Zippel binding
      CoeffDigest          Poseidon(5) fold over the coefficients, injectivity
      Balance              RangeCheck64, DummyZeroValue, per-asset conservation
      Merkle               MerkleLevel4, MerkleRoot, MerkleProofOrDummy
      BatchAppend          both batch roots, count, prefix and capacity checks
    Spec/                  specifications the tree gadgets are proved against
      QuatTree             ZerosCoherent, InsertsTo, batchTree, frontier injectivity
    Circuit/               signals, coefficient layout and constraints per circuit
      Spent                SpentNote
      Output               OutputNote
      Witness              TxWitness
      Layout               PISlot, piSlot, txCoeffs, slotIndex
      Transact             TransactSat, TxWellFormed, TxBinding, transact_sound
      BatchWitness         BatchSignals
      BatchLayout          BatchPISlot, batchPiSlot, batchCoeffs, batchSlotIndex
      TreeUpdateBatch      BatchSat and the batch results
      Obligations          what each circuit leaves to its verifier
    Proofs/
      Completeness         satisfying assignments for transact
      BatchCompleteness    satisfying assignments for tree_update_batch
      Rejection            assignments with no satisfying witness
    Meta/
      Assumptions          the trusted base, documented and printed
      AxiomGuard           build-time axiom check over every declaration
  expected/                golden files; regenerate with --update on the relevant script
    axioms.txt             output of Meta/Assumptions
    layout-4x6.txt         output of Circuit/Layout :: layoutNames
    layout-batch-8.txt     output of Circuit/BatchLayout :: batchLayoutNames
    coverage.txt           constraints no narrow citation reaches
    signal-map.json        model field to circom signal, hand-maintained
  scripts/                 check-all, check-axioms, dump-layout, check-prime,
                           check-citations, check-coverage, check-names
```

Each `…Sat` definition is a structure mirroring one circom template constraint
by constraint in source order, with each field citing its source line, and has
a `…_sound` theorem.
