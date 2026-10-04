import Lelantos.Circuit.TreeUpdateBatch
import Lelantos.Proofs.Completeness

/-!
# Non-vacuity of the batch results

`Circuit/TreeUpdateBatch.lean` proves theorems of the form `BatchSat … → P`, which are
vacuous unless something satisfies `BatchSat`; `Proofs/Completeness.lean` covers the
transact circuit only. This file exhibits satisfying assignments for
`TreeUpdateBatch(11, 8)`, the deployed shape.

`batchAt S fr` is one assignment per start position `S` and frontier `fr`, committing three
leaves into eight slots: an odd, partially-filled batch, so the padding constraints and the
leaf zeroing are exercised rather than satisfied by `active ≡ 1`. Slot `0` is a deposit of
one unit of asset `1`, so its leaf goes through the deposit commitment, both of its range
checks decompose a non-zero value, and the asset guard is satisfied with a non-zero asset;
slots `1` and `2` are spend leaves, where the leaf is the word itself. Both branches of the
leaf mux are therefore taken on active slots. The mix is not one the contract would accept
in a single batch — it pins `is_deposit` uniformly — but the circuit does not know that, and
the point here is the constraint system.

Two instances:

* `batch`, at `start_index = 0` over an empty frontier — the base the named theorems use;
* `batchSat_nonzero_frontier`, at `start_index = 21` over a frontier holding a non-zero value
  in every slot a root reads, so both roots take their frontier branches and the zero pin
  accepts an honestly filled frontier.

The empty-subtree fills are `emptyChain`, so `ZerosCoherent` is discharged rather than assumed.
-/

namespace Lelantos

namespace BatchWitness

/-! ## Shape

Named constants rather than numerals, so the arithmetic below matches the circuit's and the
shape is defined in one place.
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
carries zero in every per-leaf field, which is the `hx` hypothesis. `hx` ranges over all
padding slots (five, for `filled = 3` of `slots = 8`). -/
theorem pad_mul {x : ℕ → F} (hx : ∀ j, ¬ j < filled → x j = 0) (k : ℕ) (hk : k < slots) :
    (1 - act k) * x k = 0 := by
  rw [act_eq k hk]
  by_cases h : k < filled
  · simp [h]
  · simp [h, hx k h]

/-! ## Slots

Three distinct words and zeroed padding slots. Slot `0` is a deposit; the single-slot
indicator `head` describes all three of its deposit fields.
-/

/-- Slot `k`'s word in `cms`: on slot `0` the depositor's `inner`, on slots `1` and `2` a
note commitment. Distinct across the filled slots; zero on every padding slot, as `pad_cm`
requires. -/
def cm (k : ℕ) : F := if k < filled then ((k : ℕ) : F) + 7 else 0

theorem cm_pad : ∀ j, ¬ j < filled → cm j = 0 := by
  intro j hj; simp [cm, hj]

/-- `1` on slot `0`, `0` elsewhere: `is_deposit`, `leaf_asset` and `leaf_public_in` all take
this value, so slot `0` deposits one unit of asset `1`. -/
def head (k : ℕ) : F := if k = 0 then 1 else 0

theorem head_pad : ∀ j, ¬ j < filled → head j = 0 := by
  intro j hj
  have : j ≠ 0 := fun h => hj (h ▸ (by decide : (0 : ℕ) < filled))
  simp [head, this]

/-- The bit decomposition of `head k`. -/
def headBits (k : ℕ) : ℕ → F := if k = 0 then Witness.oneBits else Witness.zeroBits

theorem head_range (k : ℕ) : Num2BitsSat 64 (head k) (headBits k) := by
  by_cases h : k = 0
  · subst h
    exact Witness.num2Bits_one (by norm_num)
  · simp only [head, headBits, if_neg h]
    exact Witness.num2Bits_zero 64

/-- The deposit commitment of slot `k`, over its declared fields. -/
noncomputable def depCmOf (k : ℕ) : F := noteCommitment (head k) (head k) (cm k)

/-- Slot `k`'s leaf, as the mux computes it. -/
noncomputable def leafOf (k : ℕ) : F := cm k + head k * (depCmOf k - cm k)

/-! ## The assignment

The tree's signals are `batchAppendWitness`, which defines each as exactly the expression its
constraint requires. -/

/-- The tree's signals at start `S` over frontier `fr`. -/
noncomputable def appendAt (S : ℕ) (fr : ℕ → ℕ → F) : BatchAppendSignals :=
  batchAppendWitness depth slots countBits S filled leafOf fr emptyChain

/-- Every signal but the digest, the Horner accumulator and `y`, which are computed from the
coefficient vector this fixes. The challenge is `1`: the circuit rejects `z = 0`. -/
noncomputable def baseAt (S : ℕ) (fr : ℕ → ℕ → F) : BatchSignals depth slots where
  z := 1
  y := 0
  digest := 0
  -- chosen: the start, the frontier, one deposit leaf and two spend leaves
  oldRoot := (appendAt S fr).oldRoot
  newRoot := (appendAt S fr).newRoot
  startIndex := ((S : ℕ) : F)
  actualCount := ((filled : ℕ) : F)
  cms := cm
  leafAsset := head
  leafPublicIn := head
  isDeposit := head
  frontierIn := fr
  -- derived: the leaf
  assetBits := headBits
  pubInBits := headBits
  depCm := depCmOf
  depDelta := fun k => head k * (depCmOf k - cm k)
  leaves := leafOf
  -- derived: the tree
  append := appendAt S fr
  -- derived: the asset guard
  assetInv := fun k => Witness.isZeroInv (head k)
  assetIsZero := fun k => Witness.isZeroOut (head k)
  dgBlock := fun _ => 0
  peAcc := fun _ => 0
  -- `IsZero(1)`: `inv = 1`, `out = 0`.
  zInv := 1
  zIsZero := 0

/-- A satisfying assignment for `TreeUpdateBatch(11, 8)` committing three leaves at `S`. -/
noncomputable def batchAt (S : ℕ) (fr : ℕ → ℕ → F) : BatchSignals depth slots :=
  let base := baseAt S fr
  { base with
    digest := coeffDigest (batchCoeffs base) (batchPiCount slots)
    dgBlock := digestBlock (batchCoeffs base) (batchPiCount slots)
    peAcc := hornerAcc (batchCoeffs base) (batchPiCount slots) base.z
    y := hornerAcc (batchCoeffs base) (batchPiCount slots) base.z (batchPiCount slots) }

/-- The base and the full assignment have the same coefficient vector: neither the digest
nor `y` is a coefficient. -/
theorem baseAt_coeffs (S : ℕ) (fr : ℕ → ℕ → F) (k : ℕ) :
    batchCoeffs (baseAt S fr) k = batchCoeffs (batchAt S fr) k := rfl

/-- **`BatchSat` is satisfiable** at every start that leaves room for the batch, over
every frontier zero where honest writers zero it. -/
theorem batchAt_sat {S : ℕ} {fr : ℕ → ℕ → F} (hS : S + filled ≤ 4 ^ depth)
    (hfr : ∀ d k, quatDigit S d ≤ k → fr d k = 0) :
    BatchSat countBits emptyChain (batchAt S fr) where
  deposit_bit k _ := by
    show IsBit (head k)
    unfold head; split <;> simp [IsBit]
  spend_zero_asset k _ := by
    show (1 - head k) * head k = 0
    unfold head; split <;> simp
  spend_zero_public_in k _ := by
    show (1 - head k) * head k = 0
    unfold head; split <;> simp
  asset_range k _ := head_range k
  public_in_range k _ := head_range k
  dep_cm_def _ _ := rfl
  dep_delta_def _ _ := rfl
  leaf_def _ _ := rfl
  append := batchAppend_witness BatchShape.deployed (by norm_num) (by norm_num) hS leafOf fr
    emptyChain hfr
  old_root_def := rfl
  new_root_def := rfl
  pad_cm k hk := pad_mul cm_pad k hk
  pad_asset k hk := pad_mul head_pad k hk
  pad_public_in k hk := pad_mul head_pad k hk
  pad_is_deposit k hk := pad_mul head_pad k hk
  asset_isZero k _ := Witness.isZero_witness (head k)
  no_value_under_zero k _ := by
    show Witness.isZeroOut (head k) * head k = 0
    unfold head Witness.isZeroOut; split <;> simp
  compress :=
    polyEvalSat_of_acc (show IsZeroSat (1 : F) 1 0 from ⟨by ring, by ring⟩) rfl
      (fun _ => rfl) rfl
  digest_def := coeffDigestSat_witness fun k _ => baseAt_coeffs S fr k

/-- The base instance: an empty tree. -/
noncomputable def batch : BatchSignals depth slots := batchAt 0 (fun _ _ => 0)

theorem batch_sat : BatchSat countBits emptyChain batch :=
  batchAt_sat (by norm_num) (fun _ _ _ => rfl)

/-- A frontier holding `1` in every slot a root reads at `start_index = 21`, and `0` elsewhere. -/
noncomputable def frontier21 : ℕ → ℕ → F := fun d k => if k < quatDigit 21 d then 1 else 0

end BatchWitness

/-! ## Non-vacuity -/

/-- **The batch results are not vacuous.** There is an assignment satisfying the whole
constraint system of `TreeUpdateBatch(11, 8)`, so every `BatchSat … → P` has a
non-empty domain. -/
theorem batchSat_satisfiable : ∃ w : BatchSignals 11 8, BatchSat 3 emptyChain w :=
  ⟨BatchWitness.batch, BatchWitness.batch_sat⟩

/-- The assignment is not the degenerate full batch: three leaves in eight slots, so the padding
constraints and the leaf zeroing are exercised rather than satisfied by `active ≡ 1`. -/
theorem batchSat_partial_batch :
    BatchWitness.batch.actualCount = ((3 : ℕ) : F) ∧ BatchWitness.batch.append.active 3 = 0 :=
  ⟨rfl, by
    show BatchWitness.act 3 = 0
    rw [BatchWitness.act_eq 3 (by norm_num)]
    norm_num⟩

/-- **Both branches of the leaf mux are taken on active slots.** Slot `0` is an active
deposit of a non-zero amount of a non-zero asset; slot `1` is an active spend leaf. So
`batch_deposit_leaf` and `batch_spend_leaf` each have a slot to apply to. -/
theorem batchSat_deposit_and_spend :
    BatchWitness.batch.isDeposit 0 = 1 ∧ BatchWitness.batch.leafAsset 0 = 1 ∧
      BatchWitness.batch.leafPublicIn 0 = 1 ∧ BatchWitness.batch.append.active 0 = 1 ∧
      BatchWitness.batch.isDeposit 1 = 0 ∧ BatchWitness.batch.append.active 1 = 1 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · show BatchWitness.act 0 = 1
    rw [BatchWitness.act_eq 0 (by norm_num)]
    norm_num
  · show BatchWitness.head 1 = 0
    simp [BatchWitness.head]
  · show BatchWitness.act 1 = 1
    rw [BatchWitness.act_eq 1 (by norm_num)]
    norm_num

/-- The deposit-leaf result is derivable on it: slot `0`'s leaf is the commitment of one
unit of asset `1` over the published word. -/
theorem batch_deposit_leaf_witness :
    BatchWitness.batch.leaves 0 = noteCommitment 1 1 (BatchWitness.batch.cms 0) :=
  batch_deposit_leaf BatchWitness.batch_sat (by norm_num) rfl

/-- **A filled frontier is accepted.** At `start_index = 21` the digits are `1, 1, 1, 0, …`, so
both roots read a frontier slot at each of the three lowest levels, and a frontier carrying a
non-zero value there satisfies the whole constraint system — the zero pin rejects only the
slots no root reads. -/
theorem batchSat_nonzero_frontier :
    BatchSat 3 emptyChain (BatchWitness.batchAt 21 BatchWitness.frontier21) ∧
      (BatchWitness.batchAt 21 BatchWitness.frontier21).frontierIn 0 0 ≠ 0 := by
  refine ⟨BatchWitness.batchAt_sat (by norm_num) fun d k h => ?_, ?_⟩
  · simp [BatchWitness.frontier21, Nat.not_lt.mpr h]
  · simp [BatchWitness.batchAt, BatchWitness.baseAt, BatchWitness.frontier21, quatDigit]

/-- The tree result is derivable on it: the batch advances the root by its count, with the
coherence hypothesis discharged rather than assumed. -/
theorem batch_advances_witness :
    BatchWitness.batch.newRoot =
      batchTree BatchWitness.batch.startIndex.val BatchWitness.batch.actualCount.val
        BatchWitness.batch.leaves BatchWitness.batch.frontierIn emptyChain 11 0 :=
  batch_advances_by_count BatchShape.deployed emptyChain_coherent BatchWitness.batch_sat

/-- The digest result is derivable on it: the public digest is the fold of the 36
coefficients. -/
theorem batch_digest_witness :
    BatchWitness.batch.digest = coeffDigest (batchCoeffs BatchWitness.batch) (batchPiCount 8) :=
  batch_digest_public BatchWitness.batch_sat

/-- The count range is also derivable on this assignment. -/
theorem batch_count_range_witness :
    1 ≤ BatchWitness.batch.actualCount.val ∧ BatchWitness.batch.actualCount.val ≤ 8 :=
  batch_count_range BatchShape.deployed BatchWitness.batch_sat

end Lelantos
