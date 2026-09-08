import Lelantos

/-!
# The trusted base

Everything this development assumes, in one place. The authoritative list is not this
prose — it is `#print axioms`, checked against `lean/expected/axioms.txt` by
`lean/scripts/check-axioms.sh` in CI.

That check covers the theorems named below. `Lelantos.Meta.AxiomGuard` covers the rest: it walks
every declaration in the namespace at build time and rejects any axiom outside the trusted
base, so an axiom cannot enter through a theorem nobody remembered to list here.

Run `lake env lean Lelantos/Meta/Assumptions.lean` to print the current dependency sets.

## Arithmetic

| Axiom | Why it is not a theorem | How to discharge |
|---|---|---|
| `p_prime` | `p` is 254 bits; Mathlib's `norm_num` primality extension is trial-division based and there is no Pocklington tactic | `python3 lean/scripts/check-prime.py` |
| `ell_prime` | same, 251 bits | same script |

Both are also checked structurally: the script verifies `babyjub_order = 8 · ell` and every
size bound (`2^64`, `2^66`, `2^128`, `2^252 < p`) that the proofs consume.

## Cryptographic

| Axiom | Content | Status |
|---|---|---|
| `coords` / `coords_injective` | distinct subgroup elements have distinct affine coordinates | True of any affine embedding of a curve group. Reaches no headline theorem — see below |
| `babyAdd` / `babyAdd_spec` | circomlib `BabyAdd` computes the group law | Packages the completeness of the twisted Edwards addition law on Baby Jubjub (`a` square, `d` non-square), which is what makes the two `<--` divisions at `babyjub.circom:45,48` well-constrained |
| `escalarMul` / `escalarMul_spec` | `EscalarMulAny` / `FixedBaseMul` compute `k • P` | gadget semantics; one uninterpreted symbol covers both, so replacing the fixed-base gadget is invisible here |
| `H`, `BASE0` | the two Pedersen bases | Constants |
| `assetMul` | `HashToAssetGen` is a known multiple of `BASE0` | **Deliberately models a weakness, not a strength** — see `pointBalance_not_sound` |
| `assetMul_arith` | `assetMul 1 + assetMul 3 = 2 · assetMul 2` | Follows from circomlib's signed 4-bit window encoding mapping asset ids 1,2,3 to multipliers 2,3,4; checked at runtime by `test/transact/multi_asset.test.ts` |

`propext`, `Classical.choice` and `Quot.sound` are Lean's own; they are not assumptions
about the circuit.

`coords_injective` appears in **no** entry of `lean/expected/axioms.txt`, and that is
informative rather than an oversight. Its only consumer is `perAssetPointBalance_group`, which
reads the point equation back as a group equality; nothing consumes *that*, because
`pointBalance_not_sound` proves nothing may be derived from the point equation. The
counterexample itself travels the other way, through `perAssetPointBalance_of_group`, which
needs `babyAdd_spec` and not injectivity. So the axiom is load-bearing for nothing at all,
and that is the intended state. Should it ever surface in a positive theorem's axiom set,
some proof has begun deriving conservation from the point balance — which this development
forbids. Treat that diff as a bug report, not a regeneration.

## Poseidon is deliberately *not* in that table

There is no hash axiom. `Function.Injective poseidon` is refutable
(`Lelantos.poseidon_not_injective`), so assuming it makes the development contradictory and
every theorem — `transact_sound` included — provable and empty. If a change to this
development adds an axiom asserting `Function.Injective poseidon` to the list below, the
correct response is to remove the axiom, not to regenerate the expectation.

Collision resistance is instead an explicit hypothesis `¬ PoseidonCollision` on the theorems
that need it, and `Lelantos.poseidon_collision` proves that hypothesis unsatisfiable. So
`nullifier_binds_cm`, `noteCommitment_inj`, `merkleMember_inj` and `Lelantos.TxBinding` are
assumed rather than proved: they carry no axiom precisely because they carry the assumption
in their statement. A non-vacuous treatment needs a concrete-security formulation (explicit
adversary, advantage bound) and is out of scope; `lean/README.md` lists it under what is
not proved.

Everything else — `transact_sound`, conservation, the range checks, `PolyEval` — is
independent of it.

## Not assumptions — obligations

`Lelantos.ContractObligations` records what the circuit cannot enforce and the contract
must: nullifier freshness, `z` being the challenge of *this witness's* coefficient vector,
the `chain_id` / `recipient_address` checks, and the aux-digest recomputation. No theorem
here assumes any of them; they are listed so that a reader cannot mistake the circuit's
guarantees for the system's.

Three of the four are stubs — `True`, naming a check without stating it, because what they
range over has no counterpart in this development. `challenge_binds_witness` is not: with
that obligation dropped the compressed public input carries no information at all, so a stub
there was not a harmless placeholder but a hole where the load-bearing hypothesis should be.
A stub is a claim made outside Lean; treat the remaining three the same way.

## Notable non-dependencies

`perAssetValueBalance_nat` and `polyEval_binding` — the two results carrying the most
weight — depend on **`p_prime` alone**. Neither uses a cryptographic assumption. That is
the point of `PerAssetValueBalance`: conservation is integer arithmetic, not a group
argument.

`polyEval_forge` — the result that says what an unpinned coefficient would buy an attacker
— reduces to `p_prime` alone. Nothing about the hash, and no adversary model: the forgery
is one linear equation, solved. It is why the layout carries only pinned slots.

`transact_sound` additionally pulls in `babyAdd_spec` and `escalarMul_spec`, because
`SpentReal.cvOpens` / `OutputWellFormed.cvOpens` state what `cv` commits to and that is a
statement about the curve gadgets. Nothing about the hash: the split into `TxWellFormed`
and `TxBinding` is what keeps it that way.
-/

#print axioms Lelantos.transact_sound
#print axioms Lelantos.transact4x6_sound
#print axioms Lelantos.perAssetValueBalance_nat
#print axioms Lelantos.perAssetValueBalance_all_assets
#print axioms Lelantos.polyEval_binding
#print axioms Lelantos.polyEval_forge
#print axioms Lelantos.polyEval_not_binding
#print axioms Lelantos.slotIndex_piSlot
#print axioms Lelantos.polyEval_sound
#print axioms Lelantos.pointBalance_not_sound
#print axioms Lelantos.spentNote_sound
#print axioms Lelantos.outputNote_sound
#print axioms Lelantos.merkleProofOrDummy_sound
#print axioms Lelantos.nullifier_binds_cm
#print axioms Lelantos.packAV_inj
#print axioms Lelantos.num2Bits_sound
#print axioms Lelantos.pathIndexSelectors_sound
#print axioms Lelantos.merkleMember_inj
#print axioms Lelantos.merkleNode_inj
#print axioms Lelantos.leafHash_inj
#print axioms Lelantos.slots_inj
#print axioms Lelantos.noteCommitment_inj
#print axioms Lelantos.noteCommitment_ne_leafHash
#print axioms Lelantos.no_asset_creation
#print axioms Lelantos.transact_pi_binding
#print axioms Lelantos.transactSat_satisfiable
#print axioms Lelantos.transact4x6Sat_satisfiable
#print axioms Lelantos.batchSat_satisfiable
#print axioms Lelantos.batchSat_partial_batch
#print axioms Lelantos.transactSat_spend_satisfiable
#print axioms Lelantos.transactSat_twoAsset_satisfiable
#print axioms Lelantos.cross_asset_cancellation_rejected
#print axioms Lelantos.inflation_rejected
#print axioms Lelantos.mint_from_nothing_rejected
#print axioms Lelantos.transact_pi_binding_slot
#print axioms Lelantos.piSlot_slotIndex
#print axioms Lelantos.spentNoteSat_real_satisfiable
#print axioms Lelantos.spentReal_witness
#print axioms Lelantos.transact_binding
#print axioms Lelantos.transact4x6_binding
#print axioms Lelantos.valueCommit_opens
#print axioms Lelantos.outputNote_cvDep_same_value
-- `src/tree_update_batch.circom`. The chain results rest on `p_prime` alone; only the
-- deposit binding reaches the curve gadgets, and none of them touches a hash assumption.
#print axioms Lelantos.batch_count_range
#print axioms Lelantos.batch_active_spec
#print axioms Lelantos.batch_padding_zero
#print axioms Lelantos.batch_step_inserts
#print axioms Lelantos.batch_step_stalls
#print axioms Lelantos.batch_advances_by_count
#print axioms Lelantos.batch_advances_by_count_deployed
#print axioms Lelantos.batch_active_index
#print axioms Lelantos.batch_advances_at_positions
#print axioms Lelantos.batch_advances_at_positions_deployed
#print axioms Lelantos.batch_count_range_deployed
#print axioms Lelantos.batch_bounds_deployed
#print axioms Lelantos.batch_depth_bound_deployed
#print axioms Lelantos.batchPiSlot_batchSlotIndex
#print axioms Lelantos.batch_deposit_opens
#print axioms Lelantos.quaternaryInsertLevel_sound
#print axioms Lelantos.quaternaryInsert_sound
#print axioms Lelantos.InsertsTo.unique
#print axioms Lelantos.lessThan_sound

#print axioms Lelantos.poseidon_not_injective
#print axioms Lelantos.poseidon_collision
