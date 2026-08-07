import Lelantos

/-!
# The trusted base

Everything this development assumes, in one place. The authoritative list is not this
prose — it is `#print axioms`, checked against `formal/expected-axioms.txt` by
`formal/scripts/check-axioms.sh` in CI.

That check covers the theorems named below. `Lelantos.AxiomGuard` covers the rest: it walks
every declaration in the namespace at build time and rejects any axiom outside the trusted
base, so an axiom cannot enter through a theorem nobody remembered to list here.

Run `lake env lean Lelantos/Assumptions.lean` to print the current dependency sets.

## Arithmetic

| Axiom | Why it is not a theorem | How to discharge |
|---|---|---|
| `p_prime` | `p` is 254 bits; Mathlib's `norm_num` primality extension is trial-division based and there is no Pocklington tactic | `python3 formal/scripts/check-prime.py` |
| `ell_prime` | same, 251 bits | same script |

Both are also checked structurally: the script verifies `babyjub_order = 8 · ell` and every
size bound (`2^64`, `2^66`, `2^128`, `2^253 < p`) that the proofs consume.

## Cryptographic

| Axiom | Content | Status |
|---|---|---|
| `coords` / `coords_injective` | distinct subgroup elements have distinct affine coordinates | True of any affine embedding of a curve group |
| `babyAdd` / `babyAdd_spec` | circomlib `BabyAdd` computes the group law | Packages the completeness of the twisted Edwards addition law on Baby Jubjub (`a` square, `d` non-square), which is what makes the two `<--` divisions at `babyjub.circom:45,48` well-constrained |
| `escalarMul` / `escalarMul_spec` | `EscalarMulAny` / `EscalarMulFix` compute `k • P` | circomlib gadget semantics |
| `H`, `BASE0` | the two Pedersen bases | Constants |
| `assetMul` | `HashToAssetGen` is a known multiple of `BASE0` | **Deliberately models a weakness, not a strength** — see `pointBalance_not_sound` |
| `assetMul_arith` | `assetMul 1 + assetMul 3 = 2 · assetMul 2` | Follows from circomlib's signed 4-bit window encoding mapping asset ids 1,2,3 to multipliers 2,3,4; checked at runtime by `src/test/transact.test.ts:847` |

`propext`, `Classical.choice` and `Quot.sound` are Lean's own; they are not assumptions
about the circuit.

## Poseidon is deliberately *not* in that table

There is no hash axiom. `Function.Injective poseidon` is refutable
(`Lelantos.poseidon_not_injective`), so assuming it makes the development contradictory and
every theorem — `transact_sound` included — provable and empty. If a change to this
development adds `poseidon_injective` to the list below, the correct response is to remove
the axiom, not to regenerate the expectation.

Collision resistance is instead an explicit hypothesis `¬ PoseidonCollision` on the theorems
that need it, and `Lelantos.poseidon_collision` proves that hypothesis unsatisfiable. So
`nullifier_binds_cm`, `noteCommitment_inj`, `merkleMember_inj` and `Lelantos.TxBinding` are
assumed rather than proved: they carry no axiom precisely because they carry the assumption
in their statement. A non-vacuous treatment needs a concrete-security formulation (explicit
adversary, advantage bound) and is out of scope; `formal/README.md` lists it under what is
not proved.

Everything else — `transact_sound`, conservation, the range checks, `PolyEval` — is
independent of it.

## Not assumptions — obligations

`Lelantos.ContractObligations` records what the circuit cannot enforce and the contract
must: nullifier freshness, `z` being a real Fiat-Shamir challenge, and the
`chain_id` / `recipient_address` checks. No theorem here assumes any of them; they are
listed so that a reader cannot mistake the circuit's guarantees for the system's.

## Notable non-dependencies

`perAssetValueBalance_nat` and `polyEval_binding` — the two results carrying the most
weight — depend on **`p_prime` alone**. Neither uses a cryptographic assumption. That is
the point of `PerAssetValueBalance`: conservation is integer arithmetic, not a group
argument.

`transact_sound` additionally pulls in `babyAdd_spec` and `escalarMul_spec`, because
`SpentReal.cvOpens` / `OutputWellFormed.cvOpens` state what `cv` commits to and that is a
statement about the curve gadgets. Nothing about the hash: the split into `TxWellFormed`
and `TxBinding` is what keeps it that way.
-/

#print axioms Lelantos.transact_sound
#print axioms Lelantos.transact2x2_sound
#print axioms Lelantos.perAssetValueBalance_nat
#print axioms Lelantos.perAssetValueBalance_all_assets
#print axioms Lelantos.polyEval_binding
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
#print axioms Lelantos.noteCommitment_inj
#print axioms Lelantos.noteCommitment_ne_leafHash
#print axioms Lelantos.no_asset_creation
#print axioms Lelantos.transact_pi_binding
#print axioms Lelantos.transactSat_satisfiable
#print axioms Lelantos.transactSat_spend_satisfiable
#print axioms Lelantos.transactSat_twoAsset_satisfiable
#print axioms Lelantos.cross_asset_cancellation_rejected
#print axioms Lelantos.inflation_rejected
#print axioms Lelantos.transact_pi_binding_slot
#print axioms Lelantos.piSlot_slotIndex
#print axioms Lelantos.spentNoteSat_real_satisfiable
#print axioms Lelantos.spentReal_witness
#print axioms Lelantos.transact_binding
#print axioms Lelantos.valueCommit_opens
#print axioms Lelantos.outputNote_cvDep_same_value
#print axioms Lelantos.poseidon_not_injective
#print axioms Lelantos.poseidon_collision
