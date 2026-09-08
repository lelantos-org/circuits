import Lelantos.Gadgets.ValueCommit

/-!
# `PerAssetPointBalance` is **not** a conservation check

`src/lib/balance.circom:144` checks the Edwards point equation

    Σ in_cv ⊕ pub_in_pt ⊕ Σ out_rH  ==  Σ out_cv ⊕ pub_out_pt ⊕ Σ in_rH

and the source comment is emphatic that this is defence in depth only
(`src/lib/balance.circom:140-141`, `src/README.md` § 6, "Point balance
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
The runtime counterpart of this proof is `test/transact/multi_asset.test.ts`.
-/

namespace Lelantos

/-- `pbLhs` at the group level, for the counterexample. -/
def pbGroupLhs (nIn : ℕ) (inCv : ℕ → G) (pubInPt : G) (outRH : ℕ → G) : ℕ → G := fun i =>
  if i < nIn then inCv i else if i = nIn then pubInPt else outRH (i - nIn - 1)

/-- `pbRhs` at the group level. -/
def pbGroupRhs (nOut : ℕ) (outCv : ℕ → G) (pubOutPt : G) (inRH : ℕ → G) : ℕ → G := fun j =>
  if j < nOut then outCv j else if j = nOut then pubOutPt else inRH (j - nOut - 1)

/-! ## `PointSum`, over coordinates

`PointSum(N)` (`src/lib/value_commit.circom:157-183`) is what the constraint is written in
terms of, and it is a chain of `BabyAdd` over **coordinate pairs**. Modelling it that way
matters for more than tidiness: the earlier group-level formulation forced `TransactSat` to
carry six fields asserting that each published `cv` / `rH` pair is the image under `coords`
of a subgroup element, which the circuit does not check. Those were the only fields in the
whole model with no circom counterpart, and they were in the dangerous direction of
`FIDELITY.md`'s table — a model constraint the prover need not satisfy. Stating the sum over
`Pt` removes them.

The three-case shape is circom's, not a convenience: `N = 0` emits the identity literally
and `N = 1` emits the single point, neither through `BabyAdd`. Folding those into the
recursive case would assume `babyAdd ⟨0,1⟩ p = p`, which the gadget axioms do not give. -/
noncomputable def ptSum (pts : ℕ → Pt) : ℕ → Pt
  | 0 => ⟨0, 1⟩
  | 1 => pts 0
  | n + 2 => babyAdd (ptSum pts (n + 1)) (pts (n + 1))

/-- On a non-empty chain the coordinate fold is the group sum. `n = 0` is excluded because
the identity's coordinates are `⟨0, 1⟩` by circom's construction and `coords 0` is opaque;
`PerAssetPointBalance` never instantiates it, since both sides carry the public bucket. -/
theorem ptSum_coords (pts : ℕ → G) : ∀ n, 1 ≤ n →
    ptSum (fun i => coords (pts i)) n = coords (pointSum pts n) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    match m with
    | 0 => simp [ptSum, pointSum]
    | k + 1 =>
      rw [ptSum, ih (by omega), babyAdd_spec]
      congr 1
      simp [pointSum, Finset.sum_range_succ]

/-- The left-hand summand list: every input `cv`, then the public bucket's point, then
every output `rH` — `src/lib/balance.circom:156-168`. -/
def pbLhs (nIn : ℕ) (inCv : ℕ → Pt) (pubInPt : Pt) (outRH : ℕ → Pt) : ℕ → Pt := fun i =>
  if i < nIn then inCv i else if i = nIn then pubInPt else outRH (i - nIn - 1)

/-- The right-hand summand list — `src/lib/balance.circom:173-185`. -/
def pbRhs (nOut : ℕ) (outCv : ℕ → Pt) (pubOutPt : Pt) (inRH : ℕ → Pt) : ℕ → Pt := fun j =>
  if j < nOut then outCv j else if j = nOut then pubOutPt else inRH (j - nOut - 1)

/-- The constraint of `PerAssetPointBalance(N_IN, N_OUT)` — `src/lib/balance.circom:144-188`,
whose last two lines are the coordinate equalities, over the two `PointSum` chains above. -/
def PerAssetPointBalanceSat (nIn nOut : ℕ) (inCv outCv inRH outRH : ℕ → Pt)
    (pubInPt pubOutPt : Pt) : Prop :=
  ptSum (pbLhs nIn inCv pubInPt outRH) (nIn + 1 + nOut)
    = ptSum (pbRhs nOut outCv pubOutPt inRH) (nOut + 1 + nIn)

/-- The left chain is the input commitments, the public point and the output blinders,
summed. Stated once so callers never unfold `pbGroupLhs`'s if-chain. -/
theorem pointSum_pbGroupLhs (nIn nOut : ℕ) (inCv : ℕ → G) (pubInPt : G) (outRH : ℕ → G) :
    pointSum (pbGroupLhs nIn inCv pubInPt outRH) (nIn + 1 + nOut)
      = pointSum inCv nIn + pubInPt + pointSum outRH nOut := by
  induction nOut with
  | zero =>
    rw [Nat.add_zero, pointSum, Finset.sum_range_succ]
    simp only [pbGroupLhs, if_neg (lt_irrefl nIn), pointSum, Finset.sum_range_zero, add_zero]
    congr 1
    exact Finset.sum_congr rfl fun i hi => by
      simp only [pbGroupLhs, if_pos (Finset.mem_range.mp hi)]
  | succ m ih =>
    have hidx : nIn + 1 + (m + 1) = (nIn + 1 + m) + 1 := by omega
    rw [hidx, pointSum, Finset.sum_range_succ, ← pointSum, ih]
    have htail : pbGroupLhs nIn inCv pubInPt outRH (nIn + 1 + m) = outRH m := by
      simp only [pbGroupLhs, if_neg (show ¬ nIn + 1 + m < nIn by omega),
        if_neg (show nIn + 1 + m ≠ nIn by omega)]
      congr 1
      omega
    rw [htail, show pointSum outRH (m + 1) = pointSum outRH m + outRH m from
      Finset.sum_range_succ _ _, add_assoc]

/-- The right chain, likewise. -/
theorem pointSum_pbGroupRhs (nOut nIn : ℕ) (outCv : ℕ → G) (pubOutPt : G) (inRH : ℕ → G) :
    pointSum (pbGroupRhs nOut outCv pubOutPt inRH) (nOut + 1 + nIn)
      = pointSum outCv nOut + pubOutPt + pointSum inRH nIn := by
  induction nIn with
  | zero =>
    rw [Nat.add_zero, pointSum, Finset.sum_range_succ]
    simp only [pbGroupRhs, if_neg (lt_irrefl nOut), pointSum, Finset.sum_range_zero, add_zero]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by
      simp only [pbGroupRhs, if_pos (Finset.mem_range.mp hj)]
  | succ m ih =>
    have hidx : nOut + 1 + (m + 1) = (nOut + 1 + m) + 1 := by omega
    rw [hidx, pointSum, Finset.sum_range_succ, ← pointSum, ih]
    have htail : pbGroupRhs nOut outCv pubOutPt inRH (nOut + 1 + m) = inRH m := by
      simp only [pbGroupRhs, if_neg (show ¬ nOut + 1 + m < nOut by omega),
        if_neg (show nOut + 1 + m ≠ nOut by omega)]
      congr 1
      omega
    rw [htail, show pointSum inRH (m + 1) = pointSum inRH m + inRH m from
      Finset.sum_range_succ _ _, add_assoc]

/-- Coordinates commute with the left summand list. -/
theorem pbLhs_coords (nIn : ℕ) (inCv : ℕ → G) (pubInPt : G) (outRH : ℕ → G) :
    pbLhs nIn (fun i => coords (inCv i)) (coords pubInPt) (fun j => coords (outRH j))
      = fun i => coords (pbGroupLhs nIn inCv pubInPt outRH i) := by
  funext i; simp only [pbLhs, pbGroupLhs]; split_ifs <;> rfl

/-- …and with the right one. -/
theorem pbRhs_coords (nOut : ℕ) (outCv : ℕ → G) (pubOutPt : G) (inRH : ℕ → G) :
    pbRhs nOut (fun j => coords (outCv j)) (coords pubOutPt) (fun i => coords (inRH i))
      = fun j => coords (pbGroupRhs nOut outCv pubOutPt inRH j) := by
  funext j; simp only [pbRhs, pbGroupRhs]; split_ifs <;> rfl

/-- **A group-level identity gives a satisfying coordinate assignment.** The direction the
counterexample needs: it is built where the arithmetic is legible and lands on the
constraint the circuit actually writes. -/
theorem perAssetPointBalance_of_group {nIn nOut : ℕ} {inCv outCv inRH outRH : ℕ → G}
    {pubInPt pubOutPt : G}
    (h : pointSum (pbGroupLhs nIn inCv pubInPt outRH) (nIn + 1 + nOut)
      = pointSum (pbGroupRhs nOut outCv pubOutPt inRH) (nOut + 1 + nIn)) :
    PerAssetPointBalanceSat nIn nOut (fun i => coords (inCv i))
      (fun j => coords (outCv j)) (fun i => coords (inRH i)) (fun j => coords (outRH j))
      (coords pubInPt) (coords pubOutPt) := by
  rw [PerAssetPointBalanceSat, pbLhs_coords, pbRhs_coords,
    ptSum_coords _ _ (by omega), ptSum_coords _ _ (by omega), h]

/-- The same equation read in the group. Available only when every published pair really is
a subgroup element's coordinates — which the circuit does not check, so this is a lemma
taking that as a hypothesis rather than a field of the model. Nothing consumes it; it exists
so the counterexample below can be built where the arithmetic is legible. -/
theorem perAssetPointBalance_group {nIn nOut : ℕ} {inCv outCv inRH outRH : ℕ → G}
    {pubInPt pubOutPt : G}
    (h : PerAssetPointBalanceSat nIn nOut (fun i => coords (inCv i))
      (fun j => coords (outCv j)) (fun i => coords (inRH i)) (fun j => coords (outRH j))
      (coords pubInPt) (coords pubOutPt)) :
    pointSum (pbGroupLhs nIn inCv pubInPt outRH) (nIn + 1 + nOut)
      = pointSum (pbGroupRhs nOut outCv pubOutPt inRH) (nOut + 1 + nIn) := by
  rw [PerAssetPointBalanceSat, pbLhs_coords, pbRhs_coords, ptSum_coords _ _ (by omega),
    ptSum_coords _ _ (by omega)] at h
  exact coords_inj h

/-- The asset generators are in arithmetic progression across ids `1, 2, 3`. -/
theorem assetGen_collinear : assetGen 1 + assetGen 3 = (2 : ZMod ell) • assetGen 2 := by
  unfold assetGen
  rw [← add_smul, ← Nat.cast_add, assetMul_arith, Nat.cast_mul, mul_smul]
  norm_num

/-! ## The counterexample

One unit of asset 1 and one unit of asset 3 in; two units of asset 2 out, plus an empty
second output slot so the shape is square rather than a convenient 2-in/1-out variant.
Nothing public.
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

/-- **The point equation accepts the attack, in the group.** The padding output contributes
`s1 • H` to both sides, so it cancels and the equation reduces to `V¹ + V³ = 2·V²`. -/
theorem attack_satisfies_pointBalance_group :
    pointSum (pbGroupLhs 2 (attackInCv r0 r1) 0 (attackOutRH s0 s1)) (2 + 1 + 2)
      = pointSum (pbGroupRhs 2 (attackOutCv s0 s1) 0 (attackInRH r0 r1)) (2 + 1 + 2) := by
  have hg : assetGen 1 + assetGen 3 = 2 * assetGen 2 := by
    simpa [smul_eq_mul] using assetGen_collinear
  simp only [pointSum, Finset.sum_range_succ, Finset.sum_range_zero, pbGroupLhs, pbGroupRhs,
    attackInCv, attackOutCv, attackInRH, attackOutRH, smul_eq_mul]
  norm_num
  linear_combination hg

/-- **…and therefore accepts it as written**, over the coordinate pairs the circuit
compares. -/
theorem attack_satisfies_pointBalance :
    PerAssetPointBalanceSat 2 2 (fun i => coords (attackInCv r0 r1 i))
      (fun j => coords (attackOutCv s0 s1 j)) (fun i => coords (attackInRH r0 r1 i))
      (fun j => coords (attackOutRH s0 s1 j)) (coords 0) (coords 0) :=
  perAssetPointBalance_of_group (attack_satisfies_pointBalance_group r0 r1 s0 s1)

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
satisfying the point equation whose per-asset value balance fails — at a full
`(N_IN, N_OUT) = (2, 2)` shape, so no reader can dismiss it as an artefact of the sizes.
The attack is shape-generic; `2x2` is used because the concrete slot arithmetic is smallest
there.

This is why `PerAssetValueBalance` exists and why nothing downstream may substitute the
point equation for it. -/
theorem pointBalance_not_sound :
    ∃ (inCv outCv inRH outRH : ℕ → Pt) (pubInPt pubOutPt : Pt) (inA inV outA outV : ℕ → F),
      PerAssetPointBalanceSat 2 2 inCv outCv inRH outRH pubInPt pubOutPt ∧
      ¬ ConservesAt 2 2 inA inV outA outV 0 0 0 1 :=
  ⟨fun i => coords (attackInCv 0 0 i), fun j => coords (attackOutCv 0 0 j),
    fun i => coords (attackInRH 0 0 i), fun j => coords (attackOutRH 0 0 j),
    coords 0, coords 0,
    attackInA, attackInV, attackOutA, attackOutV,
    attack_satisfies_pointBalance 0 0 0 0, attack_violates_conservation⟩

end Lelantos
