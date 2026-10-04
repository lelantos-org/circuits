import Lelantos.Gadgets.Comparators
import Mathlib.Tactic.Ring

/-!
# `src/lib/balance.circom` — range checks and per-asset conservation

Per-asset value conservation, `PerAssetValueBalance` (`src/lib/balance.circom:41`). The
transparent bucket sits on the output side only (a transact proof never moves tokens in),
so the equation is

    Σ in_value[i]·[in_asset[i] = c]
      = Σ out_value[j]·[out_asset[j] = c] + public_out·[public_asset_id = c].

The circuit checks it for the `N_IN + N_OUT + 1` asset ids that appear in the transaction;
`perAssetValueBalance_all_assets` extends that to every asset id in the field.

`perAssetValueBalance_nat` lifts the field equality to `ℕ` using the 64-bit range checks:
at most `n + 1` summands below `2^64` per side and `n ≤ 7` keep both sides under
`8 · 2^64 = 2^67 < p`, so the equality cannot be forged by wrapping. This is the
precondition stated at `src/lib/balance.circom:37-40`.
-/

namespace Lelantos

/-! ## `RangeCheck64` and `DummyZeroValue` -/

/-- `RangeCheck64` — `src/lib/balance.circom:11-15`. A wrapper over `Num2Bits(64)`; `bits`
is the decomposition's internal `n2b.out` array, which the template does not export. -/
def RangeCheck64Sat (v : F) (bits : ℕ → F) : Prop := Num2BitsSat 64 v bits

/-- **Soundness of `RangeCheck64`.** `2^64 < p`, so this is a bound over `ℕ`. -/
theorem rangeCheck64_sound {v : F} {bits : ℕ → F} (h : RangeCheck64Sat v bits) :
    v.val < 2 ^ 64 :=
  (num2Bits_sound (le_of_lt two_pow_64_lt_p) h).2

/-- `DummyZeroValue(N)` — `src/lib/balance.circom:18-25`:

    dummy[i] * (dummy[i] - 1) === 0;
    dummy[i] * value[i] === 0;
-/
def DummyZeroValueSat (n : ℕ) (dummy value : ℕ → F) : Prop :=
  ∀ i, i < n → IsBit (dummy i) ∧ dummy i * value i = 0

/-- The dummy flag is boolean, so every slot is either real or padding. -/
theorem dummyZeroValue_bit {n : ℕ} {dummy value : ℕ → F} (h : DummyZeroValueSat n dummy value)
    {i : ℕ} (hi : i < n) : dummy i = 0 ∨ dummy i = 1 :=
  isBit_iff.mp (h i hi).1

/-- A slot flagged as padding carries no value, so it is neutral for conservation. -/
theorem dummyZeroValue_zero {n : ℕ} {dummy value : ℕ → F} (h : DummyZeroValueSat n dummy value)
    {i : ℕ} (hi : i < n) (hd : dummy i = 1) : value i = 0 := by
  have hmul := (h i hi).2
  rwa [hd, one_mul] at hmul

/-! ## `PerAssetValueBalance` -/

/-- The candidate asset set: `{in_asset[*]} ∪ {out_asset[*]} ∪ {public_asset_id}`,
laid out as `src/lib/balance.circom:49-57` fills `cand[]`. -/
def candAt (nIn nOut : ℕ) (inA outA : ℕ → F) (pa : F) (c : ℕ) : F :=
  if c < nIn then inA c else if c < nIn + nOut then outA (c - nIn) else pa

/-- Running-sum accumulator, the shape circom uses for `lhs[c][·]` and `rhs[c][·]`
(`src/lib/balance.circom:72-87`). -/
structure AccChainSat (n : ℕ) (init : F) (t acc : ℕ → F) : Prop where
  /-- `lhs[c][0] <== 0`, resp. `rhs[c][0] <== public_out * pub_eq[c].out`. -/
  head : acc 0 = init
  /-- `lhs[c][i+1] <== lhs[c][i] + in_term[c][i]` (resp. `rhs`). -/
  step : ∀ i, i < n → acc (i + 1) = acc i + t i

/-- The chain accumulates the sum of its terms. -/
theorem accChain_sound {n : ℕ} {init : F} {t acc : ℕ → F} (h : AccChainSat n init t acc) :
    acc n = init + ∑ i ∈ Finset.range n, t i := by
  obtain ⟨h0, hstep⟩ := h
  induction n with
  | zero => simpa using h0
  | succ m ih =>
    rw [hstep m (Nat.lt_succ_self m), ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi)),
      Finset.sum_range_succ]
    ring

/-- The full constraint system of `PerAssetValueBalance(N_IN, N_OUT)` —
`src/lib/balance.circom:41-92` — including every intermediate signal circom declares. -/
structure PerAssetValueBalanceSat (nIn nOut : ℕ) (inA inV outA outV : ℕ → F) (pa po : F)
    (pubInv pubEq : ℕ → F) (inInv inEq outInv outEq : ℕ → ℕ → F)
    (inTerm outTerm lhs rhs : ℕ → ℕ → F) : Prop where
  /-- `:68-70` — `pub_eq[c] = IsEqual(public_asset_id, cand[c])`. -/
  pubEq_sat : ∀ c, c < nIn + nOut + 1 →
    IsEqualSat pa (candAt nIn nOut inA outA pa c) (pubInv c) (pubEq c)
  /-- `:76-78` — `in_eq[c][i] = IsEqual(in_asset[i], cand[c])`. -/
  inEq_sat : ∀ c, c < nIn + nOut + 1 → ∀ i, i < nIn →
    IsEqualSat (inA i) (candAt nIn nOut inA outA pa c) (inInv c i) (inEq c i)
  /-- `:83-85` — `out_eq[c][j] = IsEqual(out_asset[j], cand[c])`. -/
  outEq_sat : ∀ c, c < nIn + nOut + 1 → ∀ j, j < nOut →
    IsEqualSat (outA j) (candAt nIn nOut inA outA pa c) (outInv c j) (outEq c j)
  /-- `:79` — `in_term[c][i] <== in_value[i] * in_eq[c][i].out`. -/
  inTerm_def : ∀ c, c < nIn + nOut + 1 → ∀ i, i < nIn → inTerm c i = inV i * inEq c i
  /-- `:86` — `out_term[c][j] <== out_value[j] * out_eq[c][j].out`. -/
  outTerm_def : ∀ c, c < nIn + nOut + 1 → ∀ j, j < nOut → outTerm c j = outV j * outEq c j
  /-- `:72, 80` — `lhs[c][0] <== 0`, then a running sum of `in_term`. -/
  lhs_chain : ∀ c, c < nIn + nOut + 1 → AccChainSat nIn 0 (inTerm c) (lhs c)
  /-- `:73, 87` — `rhs[c][0] <== public_out * pub_eq[c].out`, then a running sum of
  `out_term`. -/
  rhs_chain : ∀ c, c < nIn + nOut + 1 → AccChainSat nOut (po * pubEq c) (outTerm c) (rhs c)
  /-- `:90` — `lhs[c][N_IN] === rhs[c][N_OUT]`. -/
  balanced : ∀ c, c < nIn + nOut + 1 → lhs c nIn = rhs c nOut

/-- Conservation of a single asset value `a`, stated over `F`: what the spent notes carry
of it equals what the output notes carry plus what leaves through the transparent bucket. -/
def ConservesAt (nIn nOut : ℕ) (inA inV outA outV : ℕ → F) (pa po a : F) : Prop :=
  ∑ i ∈ Finset.range nIn, inV i * ind (inA i = a)
    = po * ind (pa = a) + ∑ j ∈ Finset.range nOut, outV j * ind (outA j = a)

variable {nIn nOut : ℕ} {inA inV outA outV : ℕ → F} {pa po : F}
  {pubInv pubEq : ℕ → F} {inInv inEq outInv outEq : ℕ → ℕ → F}
  {inTerm outTerm lhs rhs : ℕ → ℕ → F}

/-- Collapse the accumulator chains: the `c`-th constraint is the statement given in the
header comment at `src/lib/balance.circom:30-31`. -/
theorem perAssetValueBalance_at_candidate
    (h : PerAssetValueBalanceSat nIn nOut inA inV outA outV pa po
      pubInv pubEq inInv inEq outInv outEq inTerm outTerm lhs rhs)
    {c : ℕ} (hc : c < nIn + nOut + 1) :
    ConservesAt nIn nOut inA inV outA outV pa po (candAt nIn nOut inA outA pa c) := by
  classical
  set a := candAt nIn nOut inA outA pa c with ha
  have hpub : pubEq c = ind (pa = a) := by
    rw [isEqual_sound (h.pubEq_sat c hc)]; rfl
  have hlhs := accChain_sound (h.lhs_chain c hc)
  have hrhs := accChain_sound (h.rhs_chain c hc)
  have hin : ∀ i ∈ Finset.range nIn, inTerm c i = inV i * ind (inA i = a) := by
    intro i hi
    rw [h.inTerm_def c hc i (Finset.mem_range.mp hi),
      isEqual_sound (h.inEq_sat c hc i (Finset.mem_range.mp hi))]
    rfl
  have hout : ∀ j ∈ Finset.range nOut, outTerm c j = outV j * ind (outA j = a) := by
    intro j hj
    rw [h.outTerm_def c hc j (Finset.mem_range.mp hj),
      isEqual_sound (h.outEq_sat c hc j (Finset.mem_range.mp hj))]
    rfl
  have := h.balanced c hc
  rw [hlhs, hrhs, Finset.sum_congr rfl hin, Finset.sum_congr rfl hout, hpub, zero_add] at this
  exact this

/-- **Per-asset conservation, for every asset.** The candidate checks suffice: an
asset id appearing nowhere in the transaction has all its indicators zero, so both sides
of its equation are `0`. This is the candidate-set argument of `src/README.md` § 6,
"Value conservation". -/
theorem perAssetValueBalance_all_assets
    (h : PerAssetValueBalanceSat nIn nOut inA inV outA outV pa po
      pubInv pubEq inInv inEq outInv outEq inTerm outTerm lhs rhs)
    (a : F) : ConservesAt nIn nOut inA inV outA outV pa po a := by
  classical
  by_cases hmem : ∃ c, c < nIn + nOut + 1 ∧ candAt nIn nOut inA outA pa c = a
  · obtain ⟨c, hc, hca⟩ := hmem
    have := perAssetValueBalance_at_candidate h hc
    rwa [hca] at this
  · simp only [not_exists, not_and] at hmem
    have hpa : pa ≠ a := by
      intro hEq
      exact hmem (nIn + nOut) (by omega) (by simp [candAt, hEq])
    have hInA : ∀ i, i < nIn → inA i ≠ a := by
      intro i hi hEq
      exact hmem i (by omega) (by simp [candAt, hi, hEq])
    have hOutA : ∀ j, j < nOut → outA j ≠ a := by
      intro j hj hEq
      refine hmem (nIn + j) (by omega) ?_
      simp only [candAt]
      rw [if_neg (by omega), if_pos (by omega)]
      simpa using hEq
    unfold ConservesAt
    rw [ind, if_neg hpa]
    rw [Finset.sum_eq_zero (fun i hi => by
        rw [ind, if_neg (hInA i (Finset.mem_range.mp hi))]; ring)]
    rw [Finset.sum_eq_zero (fun j hj => by
        rw [ind, if_neg (hOutA j (Finset.mem_range.mp hj))]; ring)]
    ring

/-! ### Lifting to `ℕ` -/

/-- Conservation of asset `a`, stated over `ℕ`. -/
def ConservesAtNat (nIn nOut : ℕ) (inA inV outA outV : ℕ → F) (pa po a : F) : Prop :=
  ∑ i ∈ Finset.range nIn, (inV i).val * indN (inA i = a)
    = po.val * indN (pa = a) + ∑ j ∈ Finset.range nOut, (outV j).val * indN (outA j = a)

/-- A sum of `n` indicator-weighted values, each below `2 ^ 64`. -/
private theorem sum_le (n : ℕ) (v : ℕ → F) (P : ℕ → Prop) [∀ i, Decidable (P i)]
    (hv : ∀ i, i < n → (v i).val < 2 ^ 64) :
    ∑ i ∈ Finset.range n, (v i).val * indN (P i) ≤ n * 2 ^ 64 := by
  have hterm : ∀ i ∈ Finset.range n, (v i).val * indN (P i) ≤ 2 ^ 64 := by
    intro i hi
    calc (v i).val * indN (P i) ≤ (v i).val * 1 :=
          Nat.mul_le_mul_left _ (indN_le_one _)
      _ = (v i).val := mul_one _
      _ ≤ 2 ^ 64 := le_of_lt (hv i (Finset.mem_range.mp hi))
  calc ∑ i ∈ Finset.range n, (v i).val * indN (P i)
      ≤ ∑ _i ∈ Finset.range n, 2 ^ 64 := Finset.sum_le_sum hterm
    _ = n * 2 ^ 64 := by simp

/-- The output side of the balance equation is at most `(n + 1)` terms below `2 ^ 64`: the
`n` output notes and the transparent bucket. Stated for arbitrary `n`, so
`perAssetValueBalance_nat` is not tied to one shape. -/
private theorem side_le (n : ℕ) (v : ℕ → F) (P : ℕ → Prop) [∀ i, Decidable (P i)]
    (pub : F) (Q : Prop) [Decidable Q]
    (hv : ∀ i, i < n → (v i).val < 2 ^ 64) (hpub : pub.val < 2 ^ 64) :
    pub.val * indN Q + ∑ i ∈ Finset.range n, (v i).val * indN (P i) ≤ (n + 1) * 2 ^ 64 := by
  have hsum := sum_le n v P hv
  have hp : pub.val * indN Q ≤ 2 ^ 64 := by
    calc pub.val * indN Q ≤ pub.val * 1 := Nat.mul_le_mul_left _ (indN_le_one _)
      _ = pub.val := mul_one _
      _ ≤ 2 ^ 64 := le_of_lt hpub
  have hexp : (n + 1) * 2 ^ 64 = 2 ^ 64 + n * 2 ^ 64 := by ring
  omega

private theorem cast_term (x : F) (Q : Prop) [Decidable Q] :
    ((x.val * indN Q : ℕ) : F) = x * ind Q := by
  rw [Nat.cast_mul, cast_indN]
  simp [ZMod.natCast_val, ZMod.cast_id]

private theorem cast_sum_terms (n : ℕ) (v : ℕ → F) (P : ℕ → Prop) [∀ i, Decidable (P i)] :
    ((∑ i ∈ Finset.range n, (v i).val * indN (P i) : ℕ) : F)
      = ∑ i ∈ Finset.range n, v i * ind (P i) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.cast_add, ih, cast_term]

private theorem cast_side (n : ℕ) (v : ℕ → F) (P : ℕ → Prop) [∀ i, Decidable (P i)]
    (pub : F) (Q : Prop) [Decidable Q] :
    ((pub.val * indN Q + ∑ i ∈ Finset.range n, (v i).val * indN (P i) : ℕ) : F)
      = pub * ind Q + ∑ i ∈ Finset.range n, v i * ind (P i) := by
  rw [Nat.cast_add, cast_term, cast_sum_terms]

/-- **Per-asset conservation over `ℕ`.** With every value 64-bit range-checked and at most
seven input and seven output slots, the field equality is an integer equality, so it cannot
be forged by wrapping.

`≤ 7` is a limit of the proof, not of `PerAssetValueBalance`: it is the largest slot count
for which `two_pow_67_lt_p` bounds `(n + 1) · 2^64`. The deployed `Transact(11, 4, 6)` is
within it; a wider shape needs a wider bound in `Lelantos.Model.Field`. -/
theorem perAssetValueBalance_nat
    (h : PerAssetValueBalanceSat nIn nOut inA inV outA outV pa po
      pubInv pubEq inInv inEq outInv outEq inTerm outTerm lhs rhs)
    (hnIn : nIn ≤ 7) (hnOut : nOut ≤ 7)
    (hInV : ∀ i, i < nIn → (inV i).val < 2 ^ 64)
    (hOutV : ∀ j, j < nOut → (outV j).val < 2 ^ 64)
    (hPo : po.val < 2 ^ 64)
    (a : F) : ConservesAtNat nIn nOut inA inV outA outV pa po a := by
  classical
  have hfield := perAssetValueBalance_all_assets h a
  -- `(n + 1) · 2^64 ≤ 8 · 2^64 = 2^67 < p` for `n ≤ 7`.
  have hbound : ∀ n : ℕ, n ≤ 7 → (n + 1) * 2 ^ 64 < p := by
    intro n hn
    have : (n + 1) * 2 ^ 64 ≤ 2 ^ 67 := by
      calc (n + 1) * 2 ^ 64 ≤ 8 * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ 67 := by norm_num
    exact lt_of_le_of_lt this two_pow_67_lt_p
  have hL := sum_le nIn inV (fun i => inA i = a) hInV
  have hR := side_le nOut outV (fun j => outA j = a) po (pa = a) hOutV hPo
  have hLp : ∑ i ∈ Finset.range nIn, (inV i).val * indN (inA i = a) < p :=
    lt_of_le_of_lt (le_trans hL (Nat.mul_le_mul_right _ (Nat.le_succ nIn))) (hbound nIn hnIn)
  have hRp : po.val * indN (pa = a) + ∑ j ∈ Finset.range nOut, (outV j).val * indN (outA j = a) < p :=
    lt_of_le_of_lt hR (hbound nOut hnOut)
  have hcast : ((∑ i ∈ Finset.range nIn, (inV i).val * indN (inA i = a) : ℕ) : F)
      = ((po.val * indN (pa = a)
      + ∑ j ∈ Finset.range nOut, (outV j).val * indN (outA j = a) : ℕ) : F) := by
    rw [cast_sum_terms, cast_side]
    exact hfield
  have := congrArg ZMod.val hcast
  rwa [ZMod.val_natCast_of_lt hLp, ZMod.val_natCast_of_lt hRp] at this

end Lelantos
