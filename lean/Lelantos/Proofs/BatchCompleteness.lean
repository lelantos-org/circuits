import Lelantos.Circuit.TreeUpdateBatch
import Lelantos.Proofs.Completeness

/-!
# Non-vacuity of the batch results

`Circuit/TreeUpdateBatch.lean` proves a dozen theorems of the form `BatchChainSat … → P`.
Read literally, all of them are vacuous unless something satisfies `BatchChainSat`, and
nothing in `Proofs/Completeness.lean` does — that file exhibits assignments for the transact
circuit only. This file closes the gap for `TreeUpdateBatch(11, 8)`, the deployed shape.

`batchAt S fr` is one assignment per start position `S` and frontier `fr`, committing **three**
leaves into eight slots: an odd, partially-filled batch, where the padding constraints and
the leaf zeroing do work rather than being satisfied by `active ≡ 1`. Two instances are
exhibited:

* `batch`, at `start_index = 0` over an empty frontier — the base the named theorems use;
* `batchSat_nonzero_frontier`, at `start_index = 21` over a frontier holding a non-zero value
  in every slot a root reads — so both roots take their frontier branches and the zero pin
  is shown not to reject an honest filled frontier.

The empty-subtree fills are `emptyChain`, so `ZerosCoherent` is discharged rather than assumed.
Every leaf is a spend (`is_deposit = 0`), which is what lets `BatchChainSat` be exhibited
without reaching a curve axiom.
-/

namespace Lelantos

namespace BatchWitness

/-! ## Shape

Named rather than written as numerals so the arithmetic below reads as the circuit's own,
and so a change of shape is a change in one place.
-/

/-- `MAX_L`: slots per batch. -/
abbrev slots : ℕ := 8
/-- Tree depth, matching the transact circuits and the on-chain tree. -/
abbrev depth : ℕ := 11
/-- `COUNT_BITS`. The circuit asserts `2 ^ countBits = slots`. -/
abbrev countBits : ℕ := 3
/-- Leaves actually committed: odd, and short of `slots`. -/
abbrev filled : ℕ := 3


/-! ## Activity

`active[k] = LessThan(countBits + 1)(k, actual_count)`, as `batchAppend_witness` computes it.
-/

/-- `active[k]`, as the gadget computes it. -/
abbrev act : ℕ → F := lessThanActive countBits filled

/-- The activity vector, evaluated: the first `filled` slots are active, the rest padding. -/
theorem act_eq (k : ℕ) (hk : k < slots) : act k = if k < filled then 1 else 0 := by
  interval_cases k <;> norm_num [lessThanActive, natBits]

/-- The padding constraints. An active slot zeroes the `1 - active` factor; a padding slot
carries zero in every per-leaf field, which is the `hx` hypothesis.

`hx` quantifies over the padding slots rather than naming one. At `slots = 4` there was
exactly one (`k = 3`) and the hypothesis could be the point value `x 3 = 0`; `filled = 3`
of `slots = 8` leaves five, so the statement has to range over all of them. -/
theorem pad_mul {x : ℕ → F} (hx : ∀ j, ¬ j < filled → x j = 0) (k : ℕ) (hk : k < slots) :
    (1 - act k) * x k = 0 := by
  rw [act_eq k hk]
  by_cases h : k < filled
  · simp [h]
  · simp [h, hx k h]

/-! ## Leaves

Three distinct commitments and zeroed padding slots. `cv_dep` is the identity's coordinates
throughout, which keeps the padding constraints on slots 3..7 satisfiable without making the
first three degenerate.
-/

/-- Slot `k`'s note commitment. Distinct across the filled slots; zero on every padding
slot, which is what `pad_cm` requires. -/
def cm (k : ℕ) : F := if k < filled then ((k : ℕ) : F) + 7 else 0

theorem cm_pad : ∀ j, ¬ j < filled → cm j = 0 := by
  intro j hj; simp [cm, hj]

/-- Slot `k`'s leaf hash, over a zero `cv_dep`. -/
noncomputable def leafOf (k : ℕ) : F := leafHash (cm k) 0 0

/-! ## The assignment

The tree's signals are `batchAppendWitness`, which defines each as exactly the expression its
constraint requires. -/

/-- The tree's signals at start `S` over frontier `fr`. -/
noncomputable def appendAt (S : ℕ) (fr : ℕ → ℕ → F) : BatchAppendSignals :=
  batchAppendWitness depth slots countBits S filled leafOf fr emptyChain

/-- A satisfying assignment for `TreeUpdateBatch(11, 8)` committing three leaves at `S`. -/
noncomputable def batchAt (S : ℕ) (fr : ℕ → ℕ → F) : BatchSignals depth slots where
  -- chosen: the start, the frontier, three spend leaves, no public input
  oldRoot := (appendAt S fr).oldRoot
  newRoot := (appendAt S fr).newRoot
  startIndex := ((S : ℕ) : F)
  actualCount := ((filled : ℕ) : F)
  cms := cm
  cvDep := fun _ => ⟨0, 0⟩
  leafAsset := fun _ => 0
  leafPublicIn := fun _ => 0
  isDeposit := fun _ => 0
  frontierIn := fr
  rcv := fun _ => 0
  leaves := leafOf
  -- derived: the tree
  append := appendAt S fr
  -- deposit-side wiring, gated off by `is_deposit = 0` but still constrained
  activeDep := fun _ => 0
  gen := fun _ => Witness.gen 0
  pubInBits := fun _ => Witness.zeroBits
  rcvBits := fun _ => Witness.zeroBits
  vT := fun _ => Witness.vTOf Witness.zeroBits 0
  rH := fun _ => Witness.rH
  expected := fun _ => Witness.cvOf Witness.zeroBits 0
  assetInv := fun _ => 0
  assetIsZero := fun _ => 1
  pubInInv := fun _ => 0
  pubInIsZero := fun _ => 1

/-! ## The two halves of the constraint system -/

/-- **`BatchChainSat` is satisfiable** at every start that leaves room for the batch, over
every frontier zero where honest writers zero it. -/
theorem batchAt_chain_sat {S : ℕ} {fr : ℕ → ℕ → F} (hS : S + filled ≤ 4 ^ depth)
    (hfr : ∀ d k, quatDigit S d ≤ k → fr d k = 0) :
    BatchChainSat countBits emptyChain (batchAt S fr) where
  leaf_def _ _ := rfl
  append := batchAppend_witness BatchShape.deployed (by norm_num) (by norm_num) hS leafOf fr
    emptyChain hfr
  old_root_def := rfl
  new_root_def := rfl
  pad_cm k hk := pad_mul cm_pad k hk
  pad_cv_x k _ := by simp [batchAt]
  pad_cv_y k _ := by simp [batchAt]
  pad_asset k _ := by simp [batchAt]
  pad_public_in k _ := by simp [batchAt]
  pad_is_deposit k _ := by simp [batchAt]
  pad_rcv k _ := by simp [batchAt]
  deposit_bit k _ := by simp [batchAt, IsBit]
  spend_zero_asset k _ := by simp [batchAt]
  spend_zero_public_in k _ := by simp [batchAt]

/-- **`BatchDepositSat` is satisfiable too.** Every slot is a spend, so `active_dep` is zero
and the binding is gated off — but the wiring it gates (`HashToAssetGen`, the range check
and the `ValueCommit`) is still discharged in full, which is what `batch_deposit_opens`
quantifies over. -/
theorem batchAt_deposit_sat (S : ℕ) (fr : ℕ → ℕ → F) : BatchDepositSat (batchAt S fr) where
  active_dep_def k _ := by simp [batchAt]
  asset_isZero k _ := by constructor <;> simp [batchAt]
  public_in_isZero k _ := by constructor <;> simp [batchAt]
  asset_matches_value k _ := by simp [batchAt]
  gen_def k _ := rfl
  public_in_range k _ := Witness.num2Bits_zero 64
  expected_def k _ := Witness.valueCommit_witness Witness.zeroBits 0
  deposit_x k _ := by simp [batchAt]
  deposit_y k _ := by simp [batchAt]

/-- The base instance: an empty tree. -/
noncomputable def batch : BatchSignals depth slots := batchAt 0 (fun _ _ => 0)

theorem batch_chain_sat : BatchChainSat countBits emptyChain batch :=
  batchAt_chain_sat (by norm_num) (fun _ _ _ => rfl)

theorem batch_sat : BatchSat countBits emptyChain batch where
  chain := batch_chain_sat
  deposit := batchAt_deposit_sat 0 _

/-- A frontier holding `1` in every slot a root reads at `start_index = 21`, and `0` elsewhere. -/
noncomputable def frontier21 : ℕ → ℕ → F := fun d k => if k < quatDigit 21 d then 1 else 0

end BatchWitness

/-! ## Non-vacuity -/

/-- **The batch results are not vacuous.** There is an assignment satisfying the whole
constraint system of `TreeUpdateBatch(11, 8)`, so every `BatchChainSat … → P` has a
non-empty domain. -/
theorem batchSat_satisfiable : ∃ w : BatchSignals 11 8, BatchSat 3 emptyChain w :=
  ⟨BatchWitness.batch, BatchWitness.batch_sat⟩

/-- …and it is not the degenerate full batch: three leaves in eight slots, so the padding
constraints and the leaf zeroing are exercised rather than satisfied by `active ≡ 1`. -/
theorem batchSat_partial_batch :
    BatchWitness.batch.actualCount = ((3 : ℕ) : F) ∧ BatchWitness.batch.append.active 3 = 0 :=
  ⟨rfl, by
    show BatchWitness.act 3 = 0
    rw [BatchWitness.act_eq 3 (by norm_num)]
    norm_num⟩

/-- **A filled frontier is accepted.** At `start_index = 21` the digits are `1, 1, 1, 0, …`, so
both roots read a frontier slot at each of the three lowest levels, and a frontier carrying a
non-zero value there satisfies the whole constraint system — the zero pin rejects only the
slots no root reads. -/
theorem batchSat_nonzero_frontier :
    BatchSat 3 emptyChain (BatchWitness.batchAt 21 BatchWitness.frontier21) ∧
      (BatchWitness.batchAt 21 BatchWitness.frontier21).frontierIn 0 0 ≠ 0 := by
  refine ⟨⟨BatchWitness.batchAt_chain_sat (by norm_num) fun d k h => ?_,
    BatchWitness.batchAt_deposit_sat 21 _⟩, ?_⟩
  · simp [BatchWitness.frontier21, Nat.not_lt.mpr h]
  · simp [BatchWitness.batchAt, BatchWitness.frontier21, quatDigit]

/-- The chain result is derivable on it: the batch advances the root by its count, with the
coherence hypothesis discharged rather than assumed. -/
theorem batch_advances_witness :
    BatchWitness.batch.newRoot =
      batchTree BatchWitness.batch.startIndex.val BatchWitness.batch.actualCount.val
        BatchWitness.batch.leaves BatchWitness.batch.frontierIn emptyChain 11 0 :=
  batch_advances_by_count BatchShape.deployed emptyChain_coherent BatchWitness.batch_chain_sat

/-- …and so is the count range, on a real assignment rather than a hypothetical one. -/
theorem batch_count_range_witness :
    1 ≤ BatchWitness.batch.actualCount.val ∧ BatchWitness.batch.actualCount.val ≤ 8 :=
  batch_count_range BatchShape.deployed BatchWitness.batch_chain_sat

end Lelantos
