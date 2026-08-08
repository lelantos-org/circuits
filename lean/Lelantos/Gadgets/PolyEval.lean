import Lelantos.Model.Field
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push

/-!
# `PolyEval` — public-input compression

`src/lib/poly_eval.circom:7` compresses `N` logical public inputs into the single pair
`(z, y)` that the verifier actually sees:

    acc[0] <== 0;
    for (var i = N; i > 0; i--) { acc[N-i+1] <== acc[N-i] * z + coeffs[i-1]; }
    y <== acc[N];

Reindexing the loop by `j = N - i` (so `j` runs `0 .. N-1`) gives
`acc[j+1] = acc[j] · z + coeffs[N-1-j]`, which is `hornerAcc` below.

Two results:

* `polyEval_sound` — the accumulator chain really computes `y = Σ_k coeffs[k] · z^k`.
* `polyEval_binding` — two *distinct* coefficient vectors agree on at most `N - 1` points
  of the field. With `N = 31` and `|F| = p ≈ 2^253.6` that is the `≤ 30/p ≈ 2^-249`
  collision bound quoted in `src/README.md § 2 "SnarkCompression"`.

`polyEval_binding` is a statement about the number of bad challenges, not about the
prover. Turning it into a security claim needs `z` to be fixed *after* the coefficients —
that is the contract's Fiat-Shamir obligation and cannot be enforced in-circuit. It
appears as an explicit hypothesis wherever it is used.
-/

namespace Lelantos

/-- `Σ_{k < n} c k · z ^ k`. -/
def polyEval (c : ℕ → F) (n : ℕ) (z : F) : F := ∑ k ∈ Finset.range n, c k * z ^ k

/-- The Horner accumulator exactly as circom builds it: step `j` folds in coefficient
`c (n - 1 - j)`. Mirrors `src/lib/poly_eval.circom:14-16`. -/
def hornerAcc (c : ℕ → F) (n : ℕ) (z : F) : ℕ → F
  | 0 => 0
  | j + 1 => hornerAcc c n z j * z + c (n - 1 - j)

theorem hornerAcc_eq (c : ℕ → F) (n : ℕ) (z : F) :
    ∀ j, j ≤ n → hornerAcc c n z j = ∑ k ∈ Finset.range j, c (n - j + k) * z ^ k := by
  intro j
  induction j with
  | zero => intro _; simp [hornerAcc]
  | succ m ih =>
    intro hm
    have hmn : m < n := hm
    rw [hornerAcc, ih (Nat.le_of_lt hmn),
      Finset.sum_range_succ' (fun k => c (n - (m + 1) + k) * z ^ k) m]
    have hzero : n - (m + 1) + 0 = n - 1 - m := by omega
    have hshift : ∀ k, n - (m + 1) + (k + 1) = n - m + k := by intro k; omega
    simp only [hzero, hshift, pow_zero, mul_one]
    congr 1
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem hornerAcc_full (c : ℕ → F) (n : ℕ) (z : F) :
    hornerAcc c n z n = polyEval c n z := by
  rw [hornerAcc_eq c n z n le_rfl]
  simp [polyEval]

/-- The constraint system of `PolyEval(n)` — `src/lib/poly_eval.circom:7-18`.
`acc` is the intermediate signal array. -/
structure PolyEvalSat (n : ℕ) (c : ℕ → F) (z : F) (acc : ℕ → F) (y : F) : Prop where
  /-- `:13` — `acc[0] <== 0`. -/
  base : acc 0 = 0
  /-- `:14-16` — the Horner step, reindexed by `j = N - i`. -/
  step : ∀ j, j < n → acc (j + 1) = acc j * z + c (n - 1 - j)
  /-- `:17` — `y <== acc[N]`. -/
  result : y = acc n

theorem polyEvalSat_acc {n : ℕ} {c : ℕ → F} {z : F} {acc : ℕ → F} {y : F}
    (h : PolyEvalSat n c z acc y) : ∀ j, j ≤ n → acc j = hornerAcc c n z j := by
  obtain ⟨h0, hstep, _⟩ := h
  intro j
  induction j with
  | zero => intro _; simpa [hornerAcc] using h0
  | succ m ih =>
    intro hm
    rw [hstep m hm, ih (Nat.le_of_lt hm), hornerAcc]

/-- **Soundness of `PolyEval`.** Any satisfying assignment has `y` equal to the
polynomial evaluation. -/
theorem polyEval_sound {n : ℕ} {c : ℕ → F} {z : F} {acc : ℕ → F} {y : F}
    (h : PolyEvalSat n c z acc y) : y = polyEval c n z := by
  rw [h.result, polyEvalSat_acc h n le_rfl, hornerAcc_full]

/-! ## Binding -/

/-- The polynomial whose evaluation `polyEval` computes. -/
noncomputable def coeffPoly (c : ℕ → F) (n : ℕ) : Polynomial F :=
  ∑ k ∈ Finset.range n, Polynomial.C (c k) * Polynomial.X ^ k

theorem coeffPoly_eval (c : ℕ → F) (n : ℕ) (z : F) :
    (coeffPoly c n).eval z = polyEval c n z := by
  simp [coeffPoly, polyEval, Polynomial.eval_finsetSum]

theorem coeffPoly_coeff (c : ℕ → F) (n m : ℕ) :
    (coeffPoly c n).coeff m = if m < n then c m else 0 := by
  rw [coeffPoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases h : m < n
  · rw [Finset.sum_eq_single m]
    · simp [h]
    · intro b _ hb; simp [Ne.symm hb]
    · intro hmem; exact absurd (Finset.mem_range.mpr h) hmem
  · rw [if_neg h]
    refine Finset.sum_eq_zero ?_
    intro b hb
    have : m ≠ b := by
      intro heq; exact h (heq ▸ Finset.mem_range.mp hb)
    simp [this]

theorem coeffPoly_degree_lt (c : ℕ → F) (n : ℕ) : (coeffPoly c n).degree < (n : ℕ) := by
  refine (Polynomial.degree_lt_iff_coeff_zero _ _).mpr fun m hm => ?_
  have hmn : n ≤ m := by exact_mod_cast hm
  simp [coeffPoly_coeff, Nat.not_lt.mpr hmn]

/-- **Binding of `PolyEval`.** Two coefficient vectors that differ somewhere below `n`
agree on at most `n - 1` challenges. -/
theorem polyEval_binding {n : ℕ} {c c' : ℕ → F} (hn : 0 < n)
    (hne : ∃ k, k < n ∧ c k ≠ c' k) :
    ({z : F | polyEval c n z = polyEval c' n z} : Set F).toFinset.card ≤ n - 1 := by
  classical
  set P : Polynomial F := coeffPoly c n - coeffPoly c' n with hP
  have hcoeff : ∀ m, P.coeff m = if m < n then c m - c' m else 0 := by
    intro m
    by_cases hm : m < n <;>
      simp [hP, Polynomial.coeff_sub, coeffPoly_coeff, hm]
  have hP0 : P ≠ 0 := by
    obtain ⟨k, hk, hck⟩ := hne
    intro hzero
    have hc := hcoeff k
    rw [hzero, Polynomial.coeff_zero, if_pos hk] at hc
    exact hck (sub_eq_zero.mp hc.symm)
  have hdeg : P.degree < (n : ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
      (max_lt (coeffPoly_degree_lt c n) (coeffPoly_degree_lt c' n))
  have hnat : P.natDegree ≤ n - 1 := by
    have := Polynomial.natDegree_lt_iff_degree_lt hP0 |>.mpr hdeg
    omega
  have hset : ({z : F | polyEval c n z = polyEval c' n z} : Set F).toFinset
      = P.roots.toFinset := by
    ext z
    simp only [Set.mem_toFinset, Set.mem_setOf_eq, Multiset.mem_toFinset,
      Polynomial.mem_roots hP0, Polynomial.IsRoot.def]
    rw [hP]
    simp [Polynomial.eval_sub, coeffPoly_eval, sub_eq_zero]
  rw [hset]
  exact le_trans (le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' P)) hnat

end Lelantos
