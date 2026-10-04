import Lelantos

/-!
# The trusted base

Everything this development assumes. The authoritative list is the `#print axioms` output
for the theorems below, checked against `lean/expected/axioms.txt` by
`lean/scripts/check-axioms.sh` in CI. Each depends on `p_prime` and Lean's own axioms, or on
less. `Lelantos.Meta.AxiomGuard` checks every declaration in the namespace at build time and
rejects any axiom outside the trusted base.

Run `lake env lean Lelantos/Meta/Assumptions.lean` to print the dependency sets.

## Arithmetic

| Axiom | Why it is not a theorem | How to discharge |
|---|---|---|
| `p_prime` | `p` is 254 bits; Mathlib's `norm_num` primality extension is trial-division based and there is no Pocklington tactic | `python3 lean/scripts/check-prime.py` |

The script also checks the size bounds the proofs consume (`2^64`, `2^66`, `2^67`,
`2^128 < p`). Those are theorems here, by `norm_num`; the script cross-checks the constant
outside Lean.

## Cryptographic

None. The only cryptographic object is Poseidon, and it is not an axiom (see below).
`propext`, `Classical.choice` and `Quot.sound` are Lean's own.

## Poseidon

There is no hash axiom. `Function.Injective poseidon` is refutable
(`Lelantos.poseidon_not_injective`), so an axiom asserting it would make every theorem
vacuous; it must be removed, not added to the expectation.

Collision resistance is an explicit hypothesis `¬ PoseidonCollision` on the theorems that
need it, and `Lelantos.poseidon_collision` proves that hypothesis unsatisfiable. So
`nullifier_binds_cm`, `noteCommitment_inj`, `merkleMember_inj`, `digest_inj`,
`txCoeffs_determined_by_digest`, `transact_calldata_binding`,
`batchCoeffs_determined_by_digest`, `batch_calldata_binding`,
`batch_deposit_opening_unique`, `batch_new_root_determined` and `Lelantos.TxBinding` are
assumed rather than proved: they carry the assumption in their statement and no axiom. A
non-vacuous treatment needs a concrete-security formulation (explicit adversary, advantage
bound) and is out of scope (`lean/README.md`).

`transact_sound`, conservation, the range checks and `PolyEval` are independent of it.

## Calldata binding

Both circuits output `(y, digest, z)`. The contract reads the digest word `d` from calldata,
derives `z = keccak(coefficients, d, challenge-only words) mod r`, computes `y` over the
calldata coefficients, and verifies against `(y, d, z)`. That a proof verifies only for the
calldata its witness describes is a commit-then-challenge Fiat-Shamir argument with two
assumptions:

* **Poseidon(5) is collision resistant**: the † hypothesis `¬ PoseidonCollision`, which
  makes the digest a commitment to one coefficient vector.
* **keccak256 behaves as a random oracle.** This is in no statement here; nothing in this
  development models keccak256 or a prover.

Proved: the digest is the `CoeffDigest` of the coefficient vector (`transact_digest_public`,
`batch_digest_public`, unconditional); the digest binds the vector (the † results);
distinct vectors agree on at most `N − 1` challenges (`polyEval_binding`,
`transact_pi_binding`, `batch_pi_binding`, unconditional), 12 for the transact layout and
35 for the batch layout.

Not formalised: the forking / random-oracle step that joins those two facts. It is prose,
in `lean/README.md` and in the "Why the compression binds" section of
`Lelantos.Circuit.Transact`.

## Obligations, not assumptions

`Lelantos.ContractObligations` records what the transact circuit cannot enforce and the
contract must: nullifier freshness and distinctness within one transaction, the three
compression conditions (the calldata digest word reaches the verifier unmodified as the
`digest` public signal; it and every coefficient are in the keccak preimage of `z`), the
`chain_id` / `recipient_address` checks, and the aux-digest recomputation.
`Lelantos.BatchContractObligations` does the same for `tree_update_batch.circom`: the three
conditions, the live root, the committed and payload leaf counts, the per-slot `is_deposit`
flag and the escrow record behind each leaf. No theorem here assumes any field of either.

Most fields are stubs (`True`, naming a check without stating it). Three are stated in
full: `digest_passed_unmodified` on both structures and `nullifiers_distinct`. A stub is a
claim made outside Lean; a stated field is an assumption, not a result.
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
-- `src/tree_update_batch.circom`.
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
