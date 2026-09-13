import Lelantos.Model.Bits
import Mathlib.Tactic.IntervalCases

/-!
# `PathIndexSelectors`

`src/lib/common.circom:11-27` turns a 2-bit quaternary path index into a one-hot selector:

    component idx_bits = Num2Bits(2);  idx_bits.in <== path_index;
    bb   <== bits[0] * bits[1];
    s[0] <== 1 - bits[0] - bits[1] + bb;   s[1] <== bits[0] - bb;
    s[2] <== bits[1] - bb;                 s[3] <== bb;

`pathIndexSelectors_sound` establishes the two facts every `MerkleLevel4` argument needs:
`path_index < 4`, and `s` is one-hot at exactly `path_index`. One-hotness is what makes the
slot-filling arithmetic in `MerkleLevel4` a permutation; without it a prover could place the
current node in more than one child slot.
-/

namespace Lelantos

/-- The constraint system of `PathIndexSelectors` — `src/lib/common.circom:11-27`.
`b` is the `Num2Bits(2)` output, `s` the selector vector. -/
structure PathIndexSelectorsSat (idx : F) (b s : ℕ → F) : Prop where
  /-- `:16-19` — `Num2Bits(2)` on the index. -/
  index_bits : Num2BitsSat 2 idx b
  /-- `:22-23` — `s[0] <== 1 - b0 - b1 + bb`, with `bb <== b0·b1` inlined. -/
  s0_def : s 0 = 1 - b 0 - b 1 + b 0 * b 1
  /-- `:24` — `s[1] <== b0 - bb`. -/
  s1_def : s 1 = b 0 - b 0 * b 1
  /-- `:25` — `s[2] <== b1 - bb`. -/
  s2_def : s 2 = b 1 - b 0 * b 1
  /-- `:26` — `s[3] <== bb`. -/
  s3_def : s 3 = b 0 * b 1

/-- **Soundness of `PathIndexSelectors`.** The index is a quaternary digit and the selector
vector is one-hot at it. -/
theorem pathIndexSelectors_sound {idx : F} {b s : ℕ → F}
    (h : PathIndexSelectorsSat idx b s) :
    idx.val < 4 ∧ ∀ k, k < 4 → s k = if k = idx.val then 1 else 0 := by
  obtain ⟨hbits, hs0, hs1, hs2, hs3⟩ := h
  have hp : (2 : ℕ) ^ 2 ≤ p := le_of_lt (lt_trans (by norm_num) two_pow_64_lt_p)
  obtain ⟨hval, hlt⟩ := num2Bits_sound hp hbits
  have hb0 : IsBit (b 0) := hbits.bits 0 (by norm_num)
  have hb1 : IsBit (b 1) := hbits.bits 1 (by norm_num)
  -- The index is `b0 + 2·b1`, so each (b0, b1) case pins it to one of `0, 1, 2, 3`.
  have hvalEq : idx.val = bitNat (b 0) + 2 * bitNat (b 1) := by
    rw [hval, bitsNat]
    simp [Finset.sum_range_succ]
    ring
  clear hbits hval
  refine ⟨hlt, fun k hk => ?_⟩
  rcases isBit_iff.mp hb0 with hv0 | hv0 <;> rcases isBit_iff.mp hb1 with hv1 | hv1 <;>
    · simp only [hv0, hv1, bitNat] at hvalEq ⊢
      interval_cases k <;> simp_all

end Lelantos
