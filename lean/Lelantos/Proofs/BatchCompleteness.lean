import Lelantos.Circuit.TreeUpdateBatch
import Lelantos.Proofs.Completeness

/-!
# Non-vacuity of the batch results

`Circuit/TreeUpdateBatch.lean` proves a dozen theorems of the form `BatchChainSat … → P`.
Read literally, all of them are vacuous unless something satisfies `BatchChainSat`, and
nothing in `Proofs/Completeness.lean` does — that file exhibits assignments for the transact
circuit only. This file closes the gap for `TreeUpdateBatch(10, 4)`, the deployed shape.

The batch commits **three** leaves into four slots. That is deliberate: an odd,
partially-filled batch is the case `actual_count` exists for, and it is the one where the
padding constraints and the two muxes do work rather than being satisfied trivially by
`active ≡ 1`. `batchSat_partial_batch` records that as a theorem so the property cannot be
lost silently.

Everything else is as simple as the constraints allow. The tree starts empty, so
`start_index = 0` and the incoming frontier is zero; the empty-subtree fills are zero, which
the model permits because it leaves `zeros` a free parameter. Every leaf is a spend
(`is_deposit = 0`), which is what lets `BatchChainSat` be exhibited without reaching a curve
axiom — the same split `BatchChainSat` and `BatchDepositSat` already make.

## Reading the assignment

`batch` below is one `BatchSignals` record. Its fields fall into three groups:

* **chosen** — the shape, the leaves, and the public inputs. These are the only real
  decisions.
* **derived** — everything the circuit computes: activity, digits, per-slot inserts, the
  running frontier and root. Each is *defined as the expression its constraint requires*, so
  the corresponding field of `BatchChainSat` closes by `rfl`.
* **deposit-side** — the gadget wiring behind the deposit binding. Every slot is a spend, so
  the binding is gated off, but the wiring still has to be discharged.
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

/-- The empty-subtree fills. `zeros` is a free parameter in the model (see `FIDELITY.md`),
so any value satisfies the constraints and zero is the simplest. -/
def emptyFill : ℕ → F := fun _ => 0

/-! ## Activity

`active[k] = LessThan(countBits + 1)(k, actual_count)`. The witness is the canonical
decomposition of the shifted difference, and the output is its top bit, negated.
-/

/-- The bits `LessThan` decomposes for slot `k`. -/
def actBits (k : ℕ) : ℕ → F := natBits (k + 2 ^ (countBits + 1) - filled)

/-- `active[k]`, as the gadget computes it. -/
def act (k : ℕ) : F := 1 - actBits k (countBits + 1)

theorem act_sat (k : ℕ) (hk : k < slots) :
    LessThanSat (countBits + 1) ((k : ℕ) : F) ((filled : ℕ) : F) (actBits k) (act k) :=
  lessThan_witness (show k < 2 ^ (countBits + 1) by
    have : k < 8 := hk
    norm_num; omega) (by norm_num)

/-- The activity vector, evaluated: the first `filled` slots are active, the rest padding. -/
theorem act_eq (k : ℕ) (hk : k < slots) : act k = if k < filled then 1 else 0 := by
  interval_cases k <;> norm_num [act, actBits, natBits]

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

/-! ## Insertion indices

`start_index = 0`, so slot `k` inserts at index `k`.

At `slots = 4` this used to be a single non-zero quaternary digit at the lowest level, and
`dig` was written as `if d = 0 then k else 0`. `slots = 8` spans two digits — index 4 is
`(1, 0)` — so the model is now the real quaternary decomposition. The two levels are what
`dig_eq` splits on below; everything above level 1 has run out of bits because `k < 8`.
-/

/-- The quaternary digit of index `k` at level `d`. -/
def dig (k d : ℕ) : ℕ := (k / 4 ^ d) % 4

theorem dig_lt {k : ℕ} (_hk : k < slots) (d : ℕ) : dig k d < 4 :=
  Nat.mod_lt _ (by norm_num)

/-- Above level 1 the index has run out of bits: `k < slots = 8 ≤ 2 ^ i` for `i ≥ 3`. -/
theorem index_bit_high {k : ℕ} (hk : k < slots) {i : ℕ} (hi : 3 ≤ i) : natBits k i = 0 := by
  have hk8 : k < 8 := hk
  have h8 : (8 : ℕ) ≤ 2 ^ i := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
  have : k / 2 ^ i = 0 := Nat.div_eq_of_lt (by omega)
  simp [natBits, this]

/-- Above level 1 the digit is zero too, for the same reason. -/
theorem dig_high {k : ℕ} (hk : k < slots) {d : ℕ} (hd : 2 ≤ d) : dig k d = 0 := by
  have hk8 : k < 8 := hk
  have h16 : (16 : ℕ) ≤ 4 ^ d := by
    calc (16 : ℕ) = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have : k / 4 ^ d = 0 := Nat.div_eq_of_lt (by omega)
  simp [dig, this]

/-- The digit the circuit reads off the index bits is the one `dig` names. -/
theorem dig_eq {k : ℕ} (hk : k < slots) (d : ℕ) :
    natBits k (2 * d) + 2 * natBits k (2 * d + 1) = ((dig k d : ℕ) : F) := by
  match d with
  | 0 => interval_cases k <;> norm_num [natBits, dig]
  | 1 => interval_cases k <;> norm_num [natBits, dig]
  | (n + 2) =>
    rw [index_bit_high hk (by omega), index_bit_high hk (by omega),
      dig_high hk (by omega)]
    norm_num

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

/-! ## The running frontier, the per-slot chains, and the running root

These are the two muxes and the insert they feed, written as the recursion they are: an
active slot hands on its insert's outputs, an inactive one hands on its own input unchanged.
-/

/-- The frontier presented to slot `k`. The only place the full insert application is
written out; everything downstream goes through `chainOf`. -/
noncomputable def frAt : ℕ → ℕ → ℕ → F
  | 0, _, _ => 0
  | k + 1, d, s =>
      act k * insFrontierOut (dig k d)
          (insCur (leafOf k) (dig k) emptyFill (frAt k) d) (frAt k d) s
        + (1 - act k) * frAt k d s

/-- The running-node chain of slot `k`'s insert: `chainOf k d` is the node at level `d`, and
`chainOf k depth` is the root that insert produces. Every insert-related field of the
assignment is a projection of this. -/
noncomputable def chainOf (k : ℕ) : ℕ → F := insCur (leafOf k) (dig k) emptyFill (frAt k)

/-- The root after slot `k`. -/
noncomputable def rootAt : ℕ → F
  | 0 => 0
  | k + 1 => act k * chainOf k depth + (1 - act k) * rootAt k

/-! ## The assignment -/

/-- A satisfying assignment for `TreeUpdateBatch(10, 4)` committing three leaves. -/
noncomputable def batch : BatchSignals depth slots where
  -- chosen: an empty tree, three spend leaves, no public input
  oldRoot := 0
  startIndex := 0
  actualCount := ((filled : ℕ) : F)
  cms := cm
  cvDep := fun _ => ⟨0, 0⟩
  leafAsset := fun _ => 0
  leafPublicIn := fun _ => 0
  isDeposit := fun _ => 0
  frontierIn := fun _ _ => 0
  rcv := fun _ => 0
  zeros := emptyFill
  -- derived: activity
  cntBits := natBits (filled - 1)
  ltBits := actBits
  active := act
  -- derived: leaves and indices
  leaves := leafOf
  idxBits := fun k => natBits k
  idxDig := fun k d => ((dig k d : ℕ) : F)
  -- derived: one insert per slot, all projections of `chainOf`
  insB := fun k d => natBits (dig k d)
  insS := fun k d => selAt (dig k d)
  insC := fun k d => insChildren (dig k d) (chainOf k d) (emptyFill d) (frAt k d)
  insCur := chainOf
  insFrOut := fun k d => insFrontierOut (dig k d) (chainOf k d) (frAt k d)
  insRoot := fun k => chainOf k depth
  -- derived: the two muxes
  fr := frAt
  runningRoot := rootAt
  newRoot := rootAt slots
  -- deposit-side wiring, gated off by `is_deposit = 0` but still constrained
  activeDep := fun _ => 0
  gen := fun _ => Witness.gen 0
  pubInBits := fun _ => Witness.zeroBits
  rcvBits := fun _ => Witness.zeroBits
  vT := fun _ => Witness.vTOf Witness.zeroBits 0
  rH := fun _ => Witness.rH
  expected := fun _ => Witness.cvOf Witness.zeroBits 0

/-! ## The two halves of the constraint system -/

/-- **`BatchChainSat` is satisfiable at the deployed shape.** -/
theorem batch_chain_sat : BatchChainSat countBits batch where
  count_bits := by
    -- `actual_count - 1 = 2`, whose two-bit decomposition is the canonical one.
    have hcount : ((filled - 1 : ℕ) : F) = batch.actualCount - 1 := by norm_num [batch]
    exact hcount ▸ num2Bits_witness (n := countBits) (m := filled - 1) (by norm_num)
  active_def k hk := act_sat k hk
  pad_cm k hk := pad_mul cm_pad k hk
  pad_cv_x k _ := by simp [batch]
  pad_cv_y k _ := by simp [batch]
  pad_asset k _ := by simp [batch]
  pad_public_in k _ := by simp [batch]
  pad_is_deposit k _ := by simp [batch]
  pad_rcv k _ := by simp [batch]
  deposit_bit k _ := by simp [batch, IsBit]
  spend_zero_asset k _ := by simp [batch]
  spend_zero_public_in k _ := by simp [batch]
  leaf_def k _ := rfl
  idx_bits k hk := by
    -- `start_index = 0`, so the value decomposed is just `k`, and `k < 8 ≤ 2 ^ 22`.
    have hk8 : k < 8 := hk
    have hlt : k < 2 ^ (2 * depth) := by
      have h : (8 : ℕ) ≤ 2 ^ (2 * depth) := by norm_num
      omega
    show Num2BitsSat (2 * depth) (0 + ((k : ℕ) : F)) (natBits k)
    rw [zero_add]
    exact num2Bits_witness hlt
  idx_dig k hk d _ := (dig_eq hk d).symm
  insert k hk :=
    quaternaryInsert_witness (leafOf k) (dig k) (dig_lt hk) emptyFill (frAt k)
  fr_base _ _ _ _ := rfl
  root_base := rfl
  fr_mux _ _ _ _ _ _ := rfl
  root_mux _ _ := rfl
  new_root_def := rfl

/-- **`BatchDepositSat` is satisfiable too.** Every slot is a spend, so `active_dep` is zero
and the binding is gated off — but the wiring it gates (`HashToAssetGen`, the range check
and the `ValueCommit`) is still discharged in full, which is what `batch_deposit_opens`
quantifies over. -/
theorem batch_deposit_sat : BatchDepositSat batch where
  active_dep_def k _ := by simp [batch]
  gen_def k _ := rfl
  public_in_range k _ := Witness.num2Bits_zero 64
  expected_def k _ := Witness.valueCommit_witness Witness.zeroBits 0
  deposit_x k _ := by simp [batch]
  deposit_y k _ := by simp [batch]

theorem batch_sat : BatchSat countBits batch where
  chain := batch_chain_sat
  deposit := batch_deposit_sat

end BatchWitness

/-! ## Non-vacuity -/

/-- **The batch results are not vacuous.** There is an assignment satisfying the whole
constraint system of `TreeUpdateBatch(11, 8)`, so every `BatchChainSat … → P` has a
non-empty domain. -/
theorem batchSat_satisfiable : ∃ w : BatchSignals 11 8, BatchSat 3 w :=
  ⟨BatchWitness.batch, BatchWitness.batch_sat⟩

/-- …and it is not the degenerate full batch: three leaves in eight slots, so the padding
constraints and both muxes are exercised rather than satisfied by `active ≡ 1`. -/
theorem batchSat_partial_batch :
    BatchWitness.batch.actualCount = ((3 : ℕ) : F) ∧ BatchWitness.batch.active 3 = 0 :=
  ⟨rfl, by
    show BatchWitness.act 3 = 0
    rw [BatchWitness.act_eq 3 (by norm_num)]
    norm_num⟩

/-- The chain result is derivable on it: the batch advances the root by its count. -/
theorem batch_advances_witness :
    (∀ k, k < BatchWitness.batch.actualCount.val →
      InsertsTo 11 (BatchWitness.batch.leaves k) (BatchWitness.batch.idxDig k)
        (BatchWitness.batch.fr k) BatchWitness.batch.zeros (BatchWitness.batch.fr (k + 1))
        (BatchWitness.batch.runningRoot (k + 1))) ∧
    BatchWitness.batch.newRoot =
      BatchWitness.batch.runningRoot BatchWitness.batch.actualCount.val :=
  batch_advances_by_count_deployed BatchWitness.batch_chain_sat

/-- …and so is the count range, on a real assignment rather than a hypothetical one. -/
theorem batch_count_range_witness :
    1 ≤ BatchWitness.batch.actualCount.val ∧ BatchWitness.batch.actualCount.val ≤ 8 :=
  batch_count_range_deployed BatchWitness.batch_chain_sat

end Lelantos
