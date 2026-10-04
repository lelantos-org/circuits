import Lelantos.Gadgets.Comparators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push

/-!
# `PolyEval` — public-input compression

`src/lib/poly_eval.circom:30` compresses `N` logical public inputs into one field element
`y`, evaluated at the challenge `z`:

    z_nz.out === 0;                                  // z != 0
    acc[0] <== 0;
    for (var i = N; i > 0; i--) { acc[N-i+1] <== acc[N-i] * z + coeffs[i-1]; }
    y <== acc[N];

Reindexing the loop by `j = N - i` (so `j` runs `0 .. N-1`) gives
`acc[j+1] = acc[j] · z + coeffs[N-1-j]`, which is `hornerAcc` below.

Results:

* `polyEval_sound` — the accumulator chain computes `y = Σ_k coeffs[k] · z^k`, and
  `polyEvalSat_z_ne_zero` — the challenge is nonzero.
* `polyEval_binding` — two distinct coefficient vectors agree on at most `N - 1` points
  of the field. With `N = 13` (the shipped transact layout) that is at most 12 challenges,
  and with `N = 36` (the batch layout) at most 35, out of `|F| = p ≈ 2^253.6`.
* `polyEval_forge`, `polyEval_not_binding` — at a fixed nonzero challenge, one freely
  chosen coefficient sends `y` to any target.

## What `polyEval_binding` is and is not

It counts challenges for two vectors that are both fixed. It is not a statement about a
prover. On its own the evaluation binds nothing: `z` is a circuit input derived from
calldata the prover authored, so the prover reads it before choosing a witness, and
`polyEval_forge` is what a vector chosen after `z` can do.

The count becomes a probability bound once the witness's coefficient vector is fixed
before `z` is drawn. Both consumers arrange that outside this template: `TransactCompressN`
and `BatchCompress` output a `CoeffDigest` of their coefficients as a second public signal,
and the contract hashes that word into `z` (`Lelantos.Gadgets.CoeffDigest`,
`Lelantos.Circuit.Transact`). The step from the count to the probability is the
Fiat-Shamir argument, in the random-oracle model for keccak256. It is prose and is not
formalised here.

`z ≠ 0` is enforced by the template independently of how the consumer derives `z`. At
`z = 0` the chain reduces to `y = coeffs[0]`.
-/

namespace Lelantos

/-- `Σ_{k < n} c k · z ^ k`. -/
def polyEval (c : ℕ → F) (n : ℕ) (z : F) : F := ∑ k ∈ Finset.range n, c k * z ^ k

/-- The Horner accumulator as circom builds it: step `j` folds in coefficient
`c (n - 1 - j)`. Mirrors `src/lib/poly_eval.circom:41-43`. -/
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

/-- The constraint system of `PolyEval(n)` — `src/lib/poly_eval.circom:30-45`.
`acc` is the intermediate signal array; `zInv` and `zOut` are the `IsZero` signals of the
challenge check. -/
structure PolyEvalSat (n : ℕ) (c : ℕ → F) (z zInv zOut : F) (acc : ℕ → F) (y : F) : Prop where
  /-- `:35-36` — `z_nz = IsZero()` on `z`. -/
  z_isZero : IsZeroSat z zInv zOut
  /-- `:37` — `z_nz.out === 0`: the challenge is nonzero. At `z = 0` the chain reduces to
  `y = coeffs[0]` and every other coefficient drops out of the public signals. -/
  z_nonzero : zOut = 0
  /-- `:40` — `acc[0] <== 0`. -/
  base : acc 0 = 0
  /-- `:41-43` — the Horner step, reindexed by `j = N - i`. -/
  step : ∀ j, j < n → acc (j + 1) = acc j * z + c (n - 1 - j)
  /-- `:44` — `y <== acc[N]`. -/
  result : y = acc n

theorem polyEvalSat_acc {n : ℕ} {c : ℕ → F} {z zInv zOut : F} {acc : ℕ → F} {y : F}
    (h : PolyEvalSat n c z zInv zOut acc y) : ∀ j, j ≤ n → acc j = hornerAcc c n z j := by
  obtain ⟨_, _, h0, hstep, _⟩ := h
  intro j
  induction j with
  | zero => intro _; simpa [hornerAcc] using h0
  | succ m ih =>
    intro hm
    rw [hstep m hm, ih (Nat.le_of_lt hm), hornerAcc]

/-- **Soundness of `PolyEval`.** Any satisfying assignment has `y` equal to the
polynomial evaluation. -/
theorem polyEval_sound {n : ℕ} {c : ℕ → F} {z zInv zOut : F} {acc : ℕ → F} {y : F}
    (h : PolyEvalSat n c z zInv zOut acc y) : y = polyEval c n z := by
  rw [h.result, polyEvalSat_acc h n le_rfl, hornerAcc_full]

/-- **The challenge is nonzero.** `IsZero` pins its output to the indicator of `z = 0`, and
the circuit forces that output to `0`. -/
theorem polyEvalSat_z_ne_zero {n : ℕ} {c : ℕ → F} {z zInv zOut : F} {acc : ℕ → F} {y : F}
    (h : PolyEvalSat n c z zInv zOut acc y) : z ≠ 0 := by
  intro hz
  have hout := isZero_sound h.z_isZero
  rw [if_pos hz, h.z_nonzero] at hout
  exact zero_ne_one hout

/-- `polyEval` only reads coefficients below `n`. -/
theorem polyEval_congr {c c' : ℕ → F} {n : ℕ} (z : F) (h : ∀ k, k < n → c k = c' k) :
    polyEval c n z = polyEval c' n z :=
  Finset.sum_congr rfl fun k hk => by rw [h k (Finset.mem_range.mp hk)]

/-- **The honest assignment.** Every coefficient vector and nonzero challenge admits a
satisfying `PolyEval` assignment, with the accumulator and `y` determined by them. This is
the gadget's completeness, and turns a forged coefficient vector from `polyEval_forge` back
into a witness. -/
theorem polyEvalSat_horner (n : ℕ) (c : ℕ → F) {z : F} (hz : z ≠ 0) :
    PolyEvalSat n c z z⁻¹ 0 (hornerAcc c n z) (polyEval c n z) where
  z_isZero := ⟨by rw [neg_mul, mul_inv_cancel₀ hz]; ring, by ring⟩
  z_nonzero := rfl
  base := rfl
  step _ _ := rfl
  result := (hornerAcc_full c n z).symm

/-- The same, for an assignment given by its signals: any accumulator that is the Horner
accumulator pointwise, with `y` its last entry and a satisfied `IsZero` on a nonzero
challenge. The completeness witnesses are built in this shape. -/
theorem polyEvalSat_of_acc {n : ℕ} {c : ℕ → F} {z zInv zOut : F} {acc : ℕ → F} {y : F}
    (hz : IsZeroSat z zInv zOut) (hout : zOut = 0)
    (hacc : ∀ j, acc j = hornerAcc c n z j) (hy : y = acc n) :
    PolyEvalSat n c z zInv zOut acc y where
  z_isZero := hz
  z_nonzero := hout
  base := by rw [hacc]; rfl
  step j _ := by rw [hacc, hacc]; rfl
  result := hy

/-! ## Freedom

`polyEval` is affine in each coefficient: the map `v ↦ y` is a degree-one polynomial with
slope `z ^ k`, invertible whenever `z ≠ 0`. So a coefficient chosen after the challenge is
known sets `y` to anything. This is why the evaluation alone is not a binding, and why the
consumers commit to the coefficient vector with a digest that the challenge is derived
from.
-/

/-- Changing one coefficient shifts `y` by `(v - c k) · z ^ k`. -/
theorem polyEval_update (c : ℕ → F) {n k : ℕ} (hk : k < n) (z v : F) :
    polyEval (Function.update c k v) n z = polyEval c n z + (v - c k) * z ^ k := by
  have hterm : ∀ m ∈ Finset.range n,
      Function.update c k v m * z ^ m
        = c m * z ^ m + (if m = k then (v - c k) * z ^ k else 0) := by
    intro m _
    rw [Function.update_apply]
    by_cases hm : m = k
    · subst hm; simp; ring
    · simp [hm]
  rw [polyEval, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range n) k (fun _ => (v - c k) * z ^ k),
    if_pos (Finset.mem_range.mpr hk)]
  rfl

/-- **One free coefficient hits every `y`.** At a nonzero challenge, a prover who may
choose coefficient `k` freely can drive the compression output to any target, leaving every
other coefficient, hence every other public input, unchanged.

No collision is needed: the forged vector is the unique solution of one linear equation in
one unknown. -/
theorem polyEval_forge (c : ℕ → F) {n k : ℕ} (hk : k < n) {z : F} (hz : z ≠ 0) (t : F) :
    polyEval (Function.update c k (c k + (t - polyEval c n z) / z ^ k)) n z = t := by
  have hzk : z ^ k ≠ 0 := pow_ne_zero k hz
  rw [polyEval_update c hk]
  field_simp
  ring

/-- **`PolyEval` alone does not bind a vector chosen after the challenge.** Given a nonzero
`z` and any target `y`, there is a coefficient vector agreeing with a given one everywhere
except at `k` whose evaluation is that target.

A verifier that saw only `(y, z)` could not distinguish the two. The circuits' verifier
also sees the digest public signal, which the challenge is derived from; a vector changed
at `k` has a different digest unless Poseidon collides (`digest_inj`), so this construction
does not give a forgery against them. -/
theorem polyEval_not_binding {n k : ℕ} (hk : k < n) {z : F} (hz : z ≠ 0) (c : ℕ → F)
    (t : F) :
    ∃ c' : ℕ → F, (∀ m, m ≠ k → c' m = c m) ∧ polyEval c' n z = t :=
  ⟨Function.update c k (c k + (t - polyEval c n z) / z ^ k),
    fun m hm => by rw [Function.update_apply, if_neg hm],
    polyEval_forge c hk hz t⟩

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
