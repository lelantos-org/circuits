import Lelantos.Gadgets.ValueCommit

/-!
# `PerAssetPointBalance` is **not** a conservation check

`src/lib/balance.circom:143` checks the Edwards point equation

    Σ in_cv ⊕ pub_in_pt ⊕ Σ out_rH  ==  Σ out_cv ⊕ pub_out_pt ⊕ Σ in_rH

and the source comment is emphatic that this is defence in depth only
(`src/lib/balance.circom:140-142`, `src/README.md` § 6, "Per-asset point balance
(defense in depth)"). This module turns that
warning into a theorem.

The reason is `HashToAssetGen`: it Pedersen-hashes a 72-bit message, which circomlib packs
into a *single* segment, so every asset generator is a publicly computable multiple of one
shared base — `Lelantos.assetGen`. Asset ids `1, 2, 3` land in consecutive multipliers, so

    V¹ + V³ = 2 · V²

exactly, and a prover can spend one unit of asset 1 plus one unit of asset 3 while minting
two units of asset 2. `pointBalance_not_sound` constructs precisely that assignment: it
satisfies the point equation and violates per-asset conservation for asset 1.

Consequence for the rest of the development: conservation is proved **only** from
`perAssetValueBalance_nat`, and no theorem is allowed to appeal to the point equation.
The runtime counterpart of this proof is `src/test/transact.test.ts:847`.
-/

namespace Lelantos

/-- The constraint of `PerAssetPointBalance(N_IN, N_OUT)`. circom compares coordinates,
which is what this records; `perAssetPointBalance_group` moves it into the group. -/
def PerAssetPointBalanceSat (nIn nOut : ℕ) (inCv outCv inRH outRH : ℕ → G)
    (pubInPt pubOutPt : G) : Prop :=
  coords (pointSum inCv nIn + pubInPt + pointSum outRH nOut)
    = coords (pointSum outCv nOut + pubOutPt + pointSum inRH nIn)

theorem perAssetPointBalance_group {nIn nOut : ℕ} {inCv outCv inRH outRH : ℕ → G}
    {pubInPt pubOutPt : G} (h : PerAssetPointBalanceSat nIn nOut inCv outCv inRH outRH
      pubInPt pubOutPt) :
    pointSum inCv nIn + pubInPt + pointSum outRH nOut
      = pointSum outCv nOut + pubOutPt + pointSum inRH nIn :=
  coords_inj h

/-- The asset generators are in arithmetic progression across ids `1, 2, 3`. -/
theorem assetGen_collinear : assetGen 1 + assetGen 3 = (2 : ZMod ell) • assetGen 2 := by
  unfold assetGen
  rw [← add_smul, ← Nat.cast_add, assetMul_arith, Nat.cast_mul, mul_smul]
  norm_num

/-! ## The counterexample

One unit of asset 1 and one unit of asset 3 in; two units of asset 2 out, plus an empty
second output slot so the shape is the **deployed** `Transact(10, 2, 2)` rather than a
convenient 2-in/1-out variant. Nothing public.
-/

/-- Input asset ids: slot 0 holds asset 1, slot 1 holds asset 3. -/
def attackInA : ℕ → F := fun i => if i = 0 then 1 else 3

/-- Both input slots carry one unit. -/
def attackInV : ℕ → F := fun _ => 1

/-- Both output slots hold asset 2. The second one is padding — asset ids must be non-zero
even on a zero-value output (`output.circom:49-51`), so `2` is the legal choice. -/
def attackOutA : ℕ → F := fun _ => 2

/-- Slot 0 carries two units, minted out of nothing; slot 1 carries none. -/
def attackOutV : ℕ → F := fun j => if j = 0 then 2 else 0

variable (r0 r1 s0 s1 : ZMod ell)

/-- Input value commitments for the attack. -/
noncomputable def attackInCv : ℕ → G := fun i =>
  if i = 0 then assetGen 1 + r0 • H else assetGen 3 + r1 • H

/-- Input blinding points for the attack. -/
noncomputable def attackInRH : ℕ → G := fun i => if i = 0 then r0 • H else r1 • H

/-- Output value commitments: two units of asset 2, then an empty slot whose commitment is
pure blinding. -/
noncomputable def attackOutCv : ℕ → G := fun j =>
  if j = 0 then (2 : ZMod ell) • assetGen 2 + s0 • H else s1 • H

/-- Output blinding points for the attack. -/
noncomputable def attackOutRH : ℕ → G := fun j => if j = 0 then s0 • H else s1 • H

/-- **The point equation accepts the attack.** The padding output contributes `s1 • H` to
both sides, so it cancels and the equation still reduces to `V¹ + V³ = 2·V²`. -/
theorem attack_satisfies_pointBalance :
    PerAssetPointBalanceSat 2 2 (attackInCv r0 r1) (attackOutCv s0 s1) (attackInRH r0 r1)
      (attackOutRH s0 s1) 0 0 := by
  unfold PerAssetPointBalanceSat
  congr 1
  have hg : assetGen 1 + assetGen 3 = 2 * assetGen 2 := by
    simpa [smul_eq_mul] using assetGen_collinear
  simp only [pointSum, Finset.sum_range_succ, Finset.sum_range_zero, attackInCv, attackOutCv,
    attackInRH, attackOutRH, smul_eq_mul]
  norm_num
  linear_combination hg

/-- **The attack violates conservation of asset 1.** One unit goes in and none comes out. -/
theorem attack_violates_conservation :
    ¬ ConservesAt 2 2 attackInA attackInV attackOutA attackOutV 0 0 0 1 := by
  classical
  unfold ConservesAt
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, attackInA, attackInV, attackOutA,
    attackOutV, ind, zero_mul, zero_add]
  norm_num
  intro h
  exact one_ne_zero h

/-- **`PerAssetPointBalance` is not sound as a conservation check.** There is an assignment
satisfying the point equation whose per-asset value balance fails — at the deployed
`(N_IN, N_OUT) = (2, 2)` shape, so no reader can dismiss it as an artefact of the sizes.

This is why `PerAssetValueBalance` exists and why nothing downstream may substitute the
point equation for it. -/
theorem pointBalance_not_sound :
    ∃ (inCv outCv inRH outRH : ℕ → G) (inA inV outA outV : ℕ → F),
      PerAssetPointBalanceSat 2 2 inCv outCv inRH outRH 0 0 ∧
      ¬ ConservesAt 2 2 inA inV outA outV 0 0 0 1 :=
  ⟨attackInCv 0 0, attackOutCv 0 0, attackInRH 0 0, attackOutRH 0 0,
    attackInA, attackInV, attackOutA, attackOutV,
    attack_satisfies_pointBalance 0 0 0 0, attack_violates_conservation⟩

end Lelantos
