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

/-! ## Reading a bit back out

`bitsNat` sends a bit vector to the natural it denotes. `bitNat_eq_digit` is the inverse
direction: the decomposition is unique, so bit `i` of that natural is the bit the assignment
supplied. Nothing downstream can read an individual bit without it — `num2Bits_sound` pins
only the *sum*, and a statement about one bit (or, in `Gadgets.Insert`, about one quaternary
digit) needs the bits back.
-/

/-- Splitting a decomposition at position `i`: the low `i` bits, plus the rest shifted. -/
theorem bitsNat_add (bs : ℕ → F) (i m : ℕ) :
    bitsNat bs (i + m) = bitsNat bs i + 2 ^ i * bitsNat (fun j => bs (i + j)) m := by
  induction m with
  | zero => simp [bitsNat]
  | succ t ih =>
    have hidx : i + (t + 1) = (i + t) + 1 := by omega
    rw [hidx, bitsNat, Finset.sum_range_succ, ← bitsNat, ih]
    simp only [bitsNat, Finset.sum_range_succ]
    rw [pow_add]
    ring

/-- **The decomposition is unique.** Bit `i` of the natural the bits denote is the bit at
index `i`, so `num2Bits_sound` pins every bit individually and not merely their sum. -/
theorem bitNat_eq_digit {bs : ℕ → F} {n i : ℕ} (hi : i < n) :
    bitsNat bs n / 2 ^ i % 2 = bitNat (bs i) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = i + (m + 1) := ⟨n - i - 1, by omega⟩
  -- Peel the low `i` bits, then the bit at `i` itself, leaving an even remainder.
  have hhigh : bitsNat (fun j => bs (i + j)) (m + 1)
      = bitNat (bs i) + 2 * bitsNat (fun j => bs (i + 1 + j)) m := by
    have h1 : (1 : ℕ) + m = m + 1 := by omega
    have := bitsNat_add (fun j => bs (i + j)) 1 m
    rw [h1] at this
    simp only [bitsNat, Finset.sum_range_one, pow_zero, mul_one, pow_one] at this ⊢
    rw [this]
    simp only [Nat.add_zero]
    congr 2
    · exact Finset.sum_congr rfl fun j _ => by rw [show i + (1 + j) = i + 1 + j by omega]
  have hlow : bitsNat bs i < 2 ^ i := bitsNat_lt bs i
  have hpos : 0 < 2 ^ i := by positivity
  rw [bitsNat_add, hhigh, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlow,
    Nat.zero_add, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (bitNat_le_one _) (by norm_num))

/-! ## Quaternary digits

The quaternary tree reads its path one *digit* at a time, and the circuits produce that
digit by pairing two bits of a `Num2Bits` output — `idx_dig[k][d] <== out[2d] + 2·out[2d+1]`
(`src/tree_update_batch.circom:336`), the same shape as `src/lib/common.circom:21`. -/

/-- Digit `d` of `m` in base 4. -/
def quatDigit (m d : ℕ) : ℕ := m / 4 ^ d % 4

theorem quatDigit_lt (m d : ℕ) : quatDigit m d < 4 := Nat.mod_lt _ (by norm_num)

/-- **The paired bits are the quaternary digit.** With `bitNat_eq_digit` this is what turns
a `Num2Bits(2·depth)` decomposition of an index into the digit vector the insert consumes.
-/
theorem quatDigit_eq_bits {bs : ℕ → F} {n d : ℕ} (h : 2 * d + 1 < n) :
    quatDigit (bitsNat bs n) d = bitNat (bs (2 * d)) + 2 * bitNat (bs (2 * d + 1)) := by
  have h0 := bitNat_eq_digit (bs := bs) (n := n) (i := 2 * d) (by omega)
  have h1 := bitNat_eq_digit (bs := bs) (n := n) (i := 2 * d + 1) (by omega)
  have hpow : (4 : ℕ) ^ d = 2 ^ (2 * d) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]
  have hdiv : bitsNat bs n / 2 ^ (2 * d + 1) = bitsNat bs n / 2 ^ (2 * d) / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [quatDigit, hpow, ← h0, ← h1, hdiv]
  omega

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
