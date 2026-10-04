import Lelantos

/-!
# The trusted base

Everything this development assumes. The authoritative list is the `#print axioms` output,
checked against `lean/expected/axioms.txt` by `lean/scripts/check-axioms.sh` in CI.

That check covers the theorems named below. `Lelantos.Meta.AxiomGuard` walks every
declaration in the namespace at build time and rejects any axiom outside the trusted base,
including axioms reached only through theorems not listed here.

Run `lake env lean Lelantos/Meta/Assumptions.lean` to print the current dependency sets.

## Arithmetic

| Axiom | Why it is not a theorem | How to discharge |
|---|---|---|
| `p_prime` | `p` is 254 bits; Mathlib's `norm_num` primality extension is trial-division based and there is no Pocklington tactic | `python3 lean/scripts/check-prime.py` |

The script also checks every size bound (`2^64`, `2^66`, `2^67`, `2^128 < p`) that the
proofs consume. Those are theorems here, decided by `norm_num`; the script repeats them so
the constant is cross-checked outside Lean.

## Cryptographic

None. Neither circuit contains curve arithmetic, so there is no group law, no
scalar-multiplication gadget and no generator to axiomatise. The only cryptographic object
is Poseidon, and it is not an axiom either — see below.

`propext`, `Classical.choice` and `Quot.sound` are Lean's own; they are not assumptions
about the circuit.

## Poseidon is not in that table

There is no hash axiom. `Function.Injective poseidon` is refutable
(`Lelantos.poseidon_not_injective`), so assuming it makes the development inconsistent and
every theorem, `transact_sound` included, vacuous. An axiom asserting
`Function.Injective poseidon` must be removed, not added to the expectation.

Collision resistance is an explicit hypothesis `¬ PoseidonCollision` on the theorems that
need it, and `Lelantos.poseidon_collision` proves that hypothesis unsatisfiable. So
`nullifier_binds_cm`, `noteCommitment_inj`, `merkleMember_inj`, `digest_inj`,
`txCoeffs_determined_by_digest`, `transact_calldata_binding`,
`batchCoeffs_determined_by_digest`, `batch_calldata_binding`,
`batch_deposit_opening_unique`, `batch_new_root_determined` and `Lelantos.TxBinding` are
assumed rather than proved: they carry no axiom because they
carry the assumption in their statement. A non-vacuous treatment needs a concrete-security
formulation (explicit adversary, advantage bound) and is out of scope; `lean/README.md`
lists it under what is not proved.

`transact_sound`, conservation, the range checks and `PolyEval` are independent of it.

## What the binding of calldata assumes, and what is in no statement

Both circuits output `(y, digest, z)`. The contract reads the digest word `d` from calldata,
derives `z = keccak(coefficients, d, challenge-only words) mod r`, computes `y` over the
calldata coefficients, and verifies against `(y, d, z)`. That a proof verifies only for the
calldata its witness describes is a commit-then-challenge Fiat-Shamir argument with two
assumptions:

* **Poseidon(5) is collision resistant.** This is the † hypothesis, `¬ PoseidonCollision`,
  carried in the statement of `digest_inj`, `transact_calldata_binding`,
  `txCoeffs_determined_by_digest`, `batch_calldata_binding` and
  `batchCoeffs_determined_by_digest`. It makes the digest a commitment to one coefficient
  vector.
* **keccak256 behaves as a random oracle.** This is in no statement here. Nothing in this
  development models keccak256 or a prover.

Proved: the digest is the `CoeffDigest` of the coefficient vector (`transact_digest_public`,
`batch_digest_public`, unconditional); the digest binds the vector (the † results above);
distinct vectors agree on at most `N − 1` challenges (`polyEval_binding`,
`transact_pi_binding`, `batch_pi_binding`, unconditional), 12 for the transact layout and
35 for the batch layout.

Not formalised: the forking / random-oracle step that turns those two facts into "no forged
calldata verifies except with negligible probability". It is the standard Fiat-Shamir step
and it is prose, in `lean/README.md` and in the "Why the compression binds" section of
`Lelantos.Circuit.Transact`.

## Obligations, not assumptions

`Lelantos.ContractObligations` records what the transact circuit cannot enforce and the
contract must: nullifier freshness, distinctness of the nullifiers *within* one
transaction, the three conditions the compression needs (the calldata digest word is passed
to the verifier unmodified as the `digest` public signal; it is in the keccak preimage of
`z`; every coefficient is in the keccak preimage of `z`), the `chain_id` /
`recipient_address` checks, and the aux-digest recomputation.
`Lelantos.BatchContractObligations` is the same ledger for `tree_update_batch.circom`: the
same three conditions, plus the live root, the committed leaf count, the payload's leaf
count, the per-slot `is_deposit` flag and the escrow record behind each leaf. No theorem
here assumes any field of either; they are listed to separate the circuit's guarantees from
the system's.

Most fields are stubs (`True`, naming a check without stating it) because what they range
over — a nullifier set, an EVM `block.chainid`, a keccak preimage, the live accumulator, an
escrow digest — has no counterpart in this development. Three are stated in full:
`digest_passed_unmodified` on both structures, which relates the witness's public digest to
the calldata word, and `nullifiers_distinct`, which relates two fields of the same witness.
A stub is a claim made outside Lean; a stated field is an assumption, not a result.

## Notable non-dependencies

Every theorem listed below depends on `p_prime` and Lean's own axioms, or on less. That
includes `transact_sound`, which used to reach the curve gadget axioms through the value
commitments it described; there are none now.

`polyEval_forge`, which describes what a coefficient chosen after the challenge can do,
reduces to `p_prime` alone: it is one linear equation. `polyEval_binding`,
`transact_digest_public` and `batch_digest_public` do too.
-/

-- `src/4x6.circom`: soundness, conservation, the compression.
#print axioms Lelantos.transact_sound
#print axioms Lelantos.transact4x6_sound
#print axioms Lelantos.perAssetValueBalance_nat
#print axioms Lelantos.perAssetValueBalance_all_assets
#print axioms Lelantos.no_asset_creation
#print axioms Lelantos.no_asset_withdrawal
#print axioms Lelantos.publicBucket_zero_asset
#print axioms Lelantos.publicBucket_zero_out
#print axioms Lelantos.polyEval_sound
#print axioms Lelantos.polyEval_binding
#print axioms Lelantos.polyEval_forge
#print axioms Lelantos.polyEval_not_binding
#print axioms Lelantos.coeffDigest_sound
#print axioms Lelantos.transact_digest_public
#print axioms Lelantos.transact_pi_binding
#print axioms Lelantos.transact_pi_binding_slot
#print axioms Lelantos.transact_calldata_pi_binding
#print axioms Lelantos.piSlot_slotIndex
#print axioms Lelantos.slotIndex_piSlot
-- Per-slot and per-gadget soundness.
#print axioms Lelantos.spentNote_sound
#print axioms Lelantos.outputNote_sound
#print axioms Lelantos.merkleProofOrDummy_sound
#print axioms Lelantos.num2Bits_sound
#print axioms Lelantos.pathIndexSelectors_sound
#print axioms Lelantos.packAV_inj
#print axioms Lelantos.slots_inj
-- Hash binding: conditional on `¬ PoseidonCollision`, carried in the statement.
#print axioms Lelantos.nullifier_binds_cm
#print axioms Lelantos.noteInner_inj
#print axioms Lelantos.noteCommitment_inj
#print axioms Lelantos.noteCm_inj
#print axioms Lelantos.noteCommitment_ne_deriveRho
#print axioms Lelantos.noteInner_ne_nullifier
#print axioms Lelantos.noteCommitment_ne_merkleNode
#print axioms Lelantos.merkleMember_inj
#print axioms Lelantos.merkleNode_inj
#print axioms Lelantos.digest_inj
#print axioms Lelantos.digestBlock_zero_ne_merkleNode
#print axioms Lelantos.transact_calldata_binding
#print axioms Lelantos.txCoeffs_determined_by_digest
#print axioms Lelantos.slotValue_determined_by_digest
#print axioms Lelantos.transact_binding
#print axioms Lelantos.transact4x6_binding
-- Non-vacuity and rejection.
#print axioms Lelantos.transactSat_satisfiable
#print axioms Lelantos.transact4x6Sat_satisfiable
#print axioms Lelantos.transactSat_spend_satisfiable
#print axioms Lelantos.transactSat_withdraw_satisfiable
#print axioms Lelantos.transactSat_twoAsset_satisfiable
#print axioms Lelantos.spentNoteSat_real_satisfiable
#print axioms Lelantos.spentReal_witness
#print axioms Lelantos.batchSat_satisfiable
#print axioms Lelantos.batchSat_partial_batch
#print axioms Lelantos.batchSat_deposit_and_spend
#print axioms Lelantos.batchSat_nonzero_frontier
#print axioms Lelantos.inflation_rejected
#print axioms Lelantos.mint_from_nothing_rejected
#print axioms Lelantos.transfer_naming_asset_rejected
#print axioms Lelantos.withdraw_asset_zero_rejected
#print axioms Lelantos.wrong_digest_rejected
-- `src/tree_update_batch.circom`. Everything rests on `p_prime` alone; the † results carry
-- their hash assumption in the statement.
#print axioms Lelantos.batch_count_range
#print axioms Lelantos.batch_active_spec
#print axioms Lelantos.batch_padding_zero
#print axioms Lelantos.batch_capacity
#print axioms Lelantos.batch_frontier_canonical
#print axioms Lelantos.batch_old_root
#print axioms Lelantos.batch_advances_by_count
#print axioms Lelantos.batch_advances_at_positions
#print axioms Lelantos.batch_deposit_leaf
#print axioms Lelantos.batch_spend_leaf
#print axioms Lelantos.batch_no_value_under_zero
#print axioms Lelantos.batch_deposit_opening_unique
#print axioms Lelantos.batch_deposit_spend_binds
#print axioms Lelantos.batch_new_root_determined
#print axioms Lelantos.batch_compression
#print axioms Lelantos.batch_digest_public
#print axioms Lelantos.batch_calldata_binding
#print axioms Lelantos.batchCoeffs_determined_by_digest
#print axioms Lelantos.batchSlotValue_determined_by_digest
#print axioms Lelantos.batch_pi_binding
#print axioms Lelantos.batch_calldata_pi_binding
#print axioms Lelantos.batchPiSlot_batchSlotIndex
#print axioms Lelantos.InsertsTo.unique
#print axioms Lelantos.batchAppend_sound
#print axioms Lelantos.batchAppend_old_root
#print axioms Lelantos.batchAppend_new_root
#print axioms Lelantos.BatchShape.deployed
#print axioms Lelantos.batchAppend_frontier_zero
#print axioms Lelantos.batchTree_eq_appendRoot
#print axioms Lelantos.batchTree_frontier_inj
#print axioms Lelantos.lessThan_sound

#print axioms Lelantos.poseidon_not_injective
#print axioms Lelantos.poseidon_collision
