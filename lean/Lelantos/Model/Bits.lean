import Lelantos.Model.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# `Num2Bits` — bit decomposition

circomlib's `Num2Bits(n)` (`node_modules/circomlib/circuits/bitify.circom:24-39`) emits

    out[i] <-- (in >> i) & 1;        // witness hint, unconstrained
    out[i] * (out[i] - 1) === 0;     // booleanity
    lc1 === in;                      // lc1 = Σ out[i] · 2^i

Only the two `===` lines constrain the witness, and only those are modelled: a `<--`
assignment carries no soundness weight, so `Num2BitsSat` holds of every satisfying
assignment regardless of how the prover produced the bits.

`num2Bits_sound` is the result the rest of the development consumes. When `2 ^ n ≤ p` the
decomposition is alias-free, so `v.val < 2 ^ n` holds over `ℕ` rather than modulo `p`;
every no-wrap argument downstream rests on it.

## Modelling convention for arrays

circom arrays are 0-indexed and read only below their declared length. Signal arrays are
therefore modelled as total functions `ℕ → F`, with every constraint guarded by `i < n`.
Values at indices `≥ n` are unconstrained and never observed.
-/

namespace Lelantos

/-! ## Booleanity -/

/-- circom's booleanity constraint `b * (b - 1) === 0`. -/
def IsBit (b : F) : Prop := b * (b - 1) = 0

theorem isBit_iff {b : F} : IsBit b ↔ b = 0 ∨ b = 1 := by
  unfold IsBit
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  · rintro (rfl | rfl) <;> ring

/-! ## Reading bits as natural numbers -/

/-- The `ℕ` reading of a field element known to be a bit. -/
def bitNat (b : F) : ℕ := if b = 1 then 1 else 0

theorem bitNat_le_one (b : F) : bitNat b ≤ 1 := by unfold bitNat; split <;> omega

/-- For a genuine bit the `ℕ` reading casts back to the field element itself. -/
theorem cast_bitNat {b : F} (h : IsBit b) : ((bitNat b : ℕ) : F) = b := by
  rcases isBit_iff.mp h with rfl | rfl <;> simp [bitNat]

/-- `Σ_{i < n} bitNat (bs i) · 2^i`, computed in `ℕ`. -/
def bitsNat (bs : ℕ → F) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, bitNat (bs i) * 2 ^ i

theorem bitsNat_lt (bs : ℕ → F) (n : ℕ) : bitsNat bs n < 2 ^ n := by
  induction n with
  | zero => simp [bitsNat]
  | succ m ih =>
    rw [bitsNat, Finset.sum_range_succ]
    have hterm : bitNat (bs m) * 2 ^ m ≤ 2 ^ m := by
      calc bitNat (bs m) * 2 ^ m ≤ 1 * 2 ^ m := Nat.mul_le_mul_right _ (bitNat_le_one (bs m))
        _ = 2 ^ m := one_mul _
    have hrest : bitsNat bs m < 2 ^ m := ih
    rw [bitsNat] at hrest
    rw [pow_succ]
    omega

theorem cast_bitsNat {n : ℕ} {bs : ℕ → F} (h : ∀ i, i < n → IsBit (bs i)) :
    ((bitsNat bs n : ℕ) : F) = ∑ i ∈ Finset.range n, bs i * (2 : F) ^ i := by
  induction n with
  | zero => simp [bitsNat]
  | succ m ih =>
    have hsplit : bitsNat bs (m + 1) = bitsNat bs m + bitNat (bs m) * 2 ^ m := by
      simp [bitsNat, Finset.sum_range_succ]
    rw [hsplit, Nat.cast_add, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
      Finset.sum_range_succ]
    congr 1
    push_cast
    rw [cast_bitNat (h m (Nat.lt_succ_self m))]

/-! ## The constraint system -/

/-- The constraint system of `Num2Bits(n)` — `circomlib/circuits/bitify.circom:24-39`. -/
structure Num2BitsSat (n : ℕ) (v : F) (bs : ℕ → F) : Prop where
  /-- `out[i] * (out[i] - 1) === 0`. -/
  bits : ∀ i, i < n → IsBit (bs i)
  /-- `lc1 === in`, i.e. `in = Σ out[i] · 2^i`. -/
  recomposition : v = ∑ i ∈ Finset.range n, bs i * (2 : F) ^ i

/-- **Soundness of `Num2Bits`.** When `2 ^ n ≤ p` the decomposition cannot alias, so the
field element is the small natural number its bits denote. -/
theorem num2Bits_sound {n : ℕ} {v : F} {bs : ℕ → F}
    (hn : 2 ^ n ≤ p) (h : Num2BitsSat n v bs) :
    v.val = bitsNat bs n ∧ v.val < 2 ^ n := by
  have hlt : bitsNat bs n < p := lt_of_lt_of_le (bitsNat_lt bs n) hn
  have hv : v = ((bitsNat bs n : ℕ) : F) := by rw [cast_bitsNat h.bits, h.recomposition]
  have hval : v.val = bitsNat bs n := by rw [hv, ZMod.val_natCast_of_lt hlt]
  exact ⟨hval, hval ▸ bitsNat_lt bs n⟩

/-! ## A canonical satisfying assignment

`Num2BitsSat` is a constraint, so every result consuming it is conditional on something
satisfying it. These exhibit the obvious witness for an arbitrary natural below `2 ^ n`,
which is what the completeness proofs need in order to instantiate `LessThan`, the
quaternary-insert chain and the batch circuit at concrete indices.
-/

/-- Bit `i` of `m` as a field element — the little-endian decomposition `Num2Bits` emits,
so `natBits m i` is what the circuit calls `out[i]`. -/
def natBits (m : ℕ) : ℕ → F := fun i => ((m / 2 ^ i % 2 : ℕ) : F)

theorem natBits_isBit (m i : ℕ) : IsBit (natBits m i) := by
  have h : m / 2 ^ i % 2 = 0 ∨ m / 2 ^ i % 2 = 1 := by omega
  rcases h with h | h <;> simp [natBits, h, IsBit]

/-- Splitting the low `n + 1` bits of `m` into its low `n` bits and bit `n`. Pure `Nat`
arithmetic; it exists to carry the induction in `natBits_recompose`. -/
theorem mod_two_pow_succ (m n : ℕ) :
    m % 2 ^ (n + 1) = m % 2 ^ n + 2 ^ n * (m / 2 ^ n % 2) := by
  have hdvd : (2 : ℕ) ^ n ∣ 2 ^ (n + 1) := pow_dvd_pow 2 (Nat.le_succ n)
  have h1 : m % 2 ^ (n + 1) % 2 ^ n = m % 2 ^ n := Nat.mod_mod_of_dvd m hdvd
  have h2 : m / 2 ^ n % 2 = m % 2 ^ (n + 1) / 2 ^ n := by
    rw [← Nat.mod_mul_right_div_self, ← pow_succ]
  have h3 := Nat.div_add_mod (m % 2 ^ (n + 1)) (2 ^ n)
  rw [h2, ← h1]
  omega

/-- `natBits` recomposes to the low `n` bits of `m`. -/
theorem natBits_recompose (m n : ℕ) :
    ((m % 2 ^ n : ℕ) : F) = ∑ i ∈ Finset.range n, natBits m i * (2 : F) ^ i := by
  induction n with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, mod_two_pow_succ m k]
    push_cast [natBits]
    ring

/-- **`Num2Bits(n)` is satisfiable at every value it admits.** The counterpart to
`num2Bits_sound`: that reads a decomposition off a satisfying assignment, this exhibits one.
-/
theorem num2Bits_witness {n m : ℕ} (h : m < 2 ^ n) :
    Num2BitsSat n ((m : ℕ) : F) (natBits m) where
  bits i _ := natBits_isBit m i
  recomposition := by
    have hm : m % 2 ^ n = m := Nat.mod_eq_of_lt h
    have := natBits_recompose m n
    rwa [hm] at this

end Lelantos
