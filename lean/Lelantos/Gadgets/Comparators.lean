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

end Lelantos
