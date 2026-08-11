import Lelantos.Model.Bits

/-!
# circomlib comparators, and the indicators they compute

`IsZero` and `IsEqual` (`node_modules/circomlib/circuits/comparators.circom:24-43`) are the
only comparators the transact circuit uses. Both are modelled here, together with the
field- and `ℕ`-valued indicator functions their outputs are shown to equal.

The soundness of `IsZero` is where `p` being prime is consumed: the argument needs `F` to
have no zero divisors.
-/

namespace Lelantos

/-! ## `IsZero` and `IsEqual` -/

/-- The constraint system of circomlib `IsZero` — `comparators.circom:24-34`:

    inv <-- in != 0 ? 1/in : 0;    // witness hint, unconstrained
    out <== -in * inv + 1;
    in * out === 0;
-/
structure IsZeroSat (x inv out : F) : Prop where
  /-- `out <== -in * inv + 1`. -/
  out_def : out = -x * inv + 1
  /-- `in * out === 0`. -/
  annihilates : x * out = 0

/-- **Soundness of `IsZero`.** The `<--` hint is irrelevant: the two constraints pin `out`
to the indicator of `x = 0` on their own. -/
theorem isZero_sound {x inv out : F} (h : IsZeroSat x inv out) :
    out = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · rw [if_pos hx, h.out_def, hx]; ring
  · rw [if_neg hx]
    rcases mul_eq_zero.mp h.annihilates with hzero | hout
    · exact absurd hzero hx
    · exact hout

/-- circomlib `IsEqual` — `comparators.circom:37-43`. It is `IsZero(in[1] - in[0])`, so
`a` is `in[0]` and `b` is `in[1]`. -/
def IsEqualSat (a b inv out : F) : Prop := IsZeroSat (b - a) inv out

/-- **Soundness of `IsEqual`.** -/
theorem isEqual_sound {a b inv out : F} (h : IsEqualSat a b inv out) :
    out = if a = b then 1 else 0 := by
  rw [isZero_sound h]
  by_cases hab : a = b
  · simp [hab]
  · rw [if_neg (sub_ne_zero.mpr (Ne.symm hab)), if_neg hab]

/-! ## Indicators

Comparator outputs are indicator values. Two readings are needed: the field-valued one the
circuit multiplies with, and the `ℕ`-valued one the no-wrap lift in
`Lelantos.Gadgets.Balance` sums over.
-/

/-- Field-valued indicator. -/
def ind (P : Prop) [Decidable P] : F := if P then 1 else 0

/-- `ℕ`-valued indicator. -/
def indN (P : Prop) [Decidable P] : ℕ := if P then 1 else 0

theorem cast_indN (P : Prop) [Decidable P] : ((indN P : ℕ) : F) = ind P := by
  unfold indN ind; split <;> simp

theorem indN_le_one (P : Prop) [Decidable P] : indN P ≤ 1 := by
  unfold indN; split <;> omega

/-! ## `LessThan`

circomlib `LessThan(n)` (`comparators.circom:89-98`) is the comparator
`src/tree_update_batch.circom:86` uses to derive `active[k] = (k < actual_count)`:

    component n2b = Num2Bits(n + 1);
    n2b.in <== in[0] + (1 << n) - in[1];
    out <== 1 - n2b.out[n];

The offset `2^n` keeps the difference non-negative; the top bit of the `(n+1)`-bit
decomposition is then the borrow flag, and `out` is its complement. The two range
hypotheses are not decoration — `LessThan` is *unsound* without them. If `in[1]` may exceed
`2^n` the subtraction wraps and the comparator reports the wrong order, which is why
`src/tree_update_batch.circom` sizes the gadget as `LessThan(COUNT_BITS + 1)` rather than
`LessThan(COUNT_BITS)`.
-/

/-- Split the top bit off a bit-decomposition sum. -/
theorem bitsNat_succ (bs : ℕ → F) (n : ℕ) :
    bitsNat bs (n + 1) = bitsNat bs n + bitNat (bs n) * 2 ^ n := by
  simp [bitsNat, Finset.sum_range_succ]

/-- The top bit of an `(n+1)`-bit decomposition is set exactly when the value reaches
`2^n`. This is the borrow flag `LessThan` reads. -/
theorem bitNat_top_iff (bs : ℕ → F) (n : ℕ) :
    bitNat (bs n) = 1 ↔ 2 ^ n ≤ bitsNat bs (n + 1) := by
  have hlow : bitsNat bs n < 2 ^ n := bitsNat_lt bs n
  rw [bitsNat_succ]
  -- `omega` cannot see through `bitNat (bs n) * 2 ^ n`, so split the bit first.
  unfold bitNat
  split
  · simp
  · simp
    omega

/-- The constraint system of circomlib `LessThan(n)` — `comparators.circom:89-98`.
`a` is `in[0]`, `b` is `in[1]`, and `bs` the `Num2Bits(n+1)` output. -/
structure LessThanSat (n : ℕ) (a b : F) (bs : ℕ → F) (out : F) : Prop where
  /-- `:94-95` — `Num2Bits(n+1)` applied to `in[0] + 2^n - in[1]`. -/
  diff_bits : Num2BitsSat (n + 1) (a + (2 : F) ^ n - b) bs
  /-- `:97` — `out <== 1 - n2b.out[n]`. -/
  out_def : out = 1 - bs n

/-- **Soundness of `LessThan`.** Given that both operands really are `n`-bit, the output is
the comparison indicator. -/
theorem lessThan_sound {n : ℕ} {a b out : F} {bs : ℕ → F}
    (hp : 2 ^ (n + 1) ≤ p) (ha : a.val < 2 ^ n) (hb : b.val < 2 ^ n)
    (h : LessThanSat n a b bs out) : out = ind (a.val < b.val) := by
  -- The shifted difference is a small natural, so its `val` is that natural.
  have hble : b.val ≤ a.val + 2 ^ n := by omega
  have hcast : a + (2 : F) ^ n - b = ((a.val + 2 ^ n - b.val : ℕ) : F) := by
    rw [Nat.cast_sub hble]
    push_cast
    rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id]
  have hsmall : a.val + 2 ^ n - b.val < p := by
    have : a.val + 2 ^ n - b.val < 2 ^ (n + 1) := by rw [pow_succ]; omega
    omega
  have hval : (a + (2 : F) ^ n - b).val = a.val + 2 ^ n - b.val := by
    rw [hcast, ZMod.val_natCast_of_lt hsmall]
  -- ... and that natural is what the bits denote.
  obtain ⟨hbits, _⟩ := num2Bits_sound hp h.diff_bits
  rw [hval] at hbits
  have htop : bitNat (bs n) = 1 ↔ b.val ≤ a.val := by
    rw [bitNat_top_iff, ← hbits]; omega
  have hbit : IsBit (bs n) := h.diff_bits.bits n (Nat.lt_succ_self n)
  rw [h.out_def, ind]
  by_cases hlt : a.val < b.val
  · have : bitNat (bs n) ≠ 1 := fun hc => absurd (htop.mp hc) (by omega)
    have hz : bs n = 0 := by
      rcases isBit_iff.mp hbit with hz | ho
      · exact hz
      · exact absurd (by simp [bitNat, ho]) this
    rw [if_pos hlt, hz]; ring
  · have : bitNat (bs n) = 1 := htop.mpr (by omega)
    have ho : bs n = 1 := by
      rcases isBit_iff.mp hbit with hz | ho
      · simp [bitNat, hz] at this
      · exact ho
    rw [if_neg hlt, ho]; ring

end Lelantos
