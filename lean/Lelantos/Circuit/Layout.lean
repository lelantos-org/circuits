import Lelantos.Circuit.Witness

/-!
# The `Transact` public-input layout

The coefficient layout `TransactCompressN` folds into the verifier-visible pair `(z, y)`:
a map from coefficient index to a named slot (`piSlot`), the value lookup at a slot
(`slotValue`), and the inverse (`slotIndex`) that turns a difference in a named field into
a difference at a coefficient index.

It is its own module because it is hand-transcribed, is dumped and diffed against the SDK
and the contract by `lean/scripts/dump-layout.sh`, and should be reviewable without reading
either the signal set or the soundness proofs. `Lelantos.Circuit.BatchLayout` is the same
module for `tree_update_batch.circom`.
-/

namespace Lelantos

variable {depth nIn nOut : ℕ}

/-- Number of `PolyEval` coefficients: `4 + 3·N_IN + 5·N_OUT`
(`src/lib/poly_eval.circom:64`). For `(2, 2)` this is 20, for `(4, 6)` it is 46.

**Membership rule.** A logical public input is a coefficient only if some
constraint outside `TransactCompressN` pins it. `PolyEval` is affine in each
coefficient and `z` is an input the prover reads first, so an unpinned
coefficient is one linear equation in one unknown whose solution sets `y` to any
target. The five address and chain words, the FMD clue triples and the payload
digest carry no constraint, so they are excluded; they are bound by being hashed
into the challenge instead
(`PubInputs.TRANSACT_CHALLENGE_WORDS`, 70 words at the 4x6 shape). -/
def piCount (nIn nOut : ℕ) : ℕ := 4 + 3 * nIn + 5 * nOut

example : piCount 2 2 = 20 := by norm_num [piCount]
example : piCount 4 6 = 46 := by norm_num [piCount]

/-! ## The slot map

Defined once, as a map from coefficient index to a named slot; the field value at an index
is a separate lookup. The dumped names and the values the proofs use therefore come from
the same definition, which is what lets `lean/scripts/dump-layout.sh` cross-check it
against the other implementations of this ordering: `contracts/src/libs/PubInputs.sol ::
compress(Transact, aux)` and `test/ref/compress.ts :: coeffs`.
-/

/-- One coefficient position of `TransactCompressN`. -/
inductive PISlot where
  | merkleRoot
  | nullifier (i : ℕ)
  | outCm (j : ℕ)
  | publicAssetId
  | publicIn
  | publicOut
  | inCvX (i : ℕ)
  | inCvY (i : ℕ)
  | outCvX (j : ℕ)
  | outCvY (j : ℕ)
  | outCvDepX (j : ℕ)
  | outCvDepY (j : ℕ)
deriving Repr, DecidableEq, Inhabited

/-- The layout of `TransactCompressN(nIn, nOut)` — `src/lib/poly_eval.circom:63-107`.
Single source of truth. -/
def piSlot (nIn nOut : ℕ) (k : ℕ) : PISlot :=
  let oNf := 1
  let oCm := oNf + nIn
  let oPub := oCm + nOut
  let oInCv := oPub + 3
  let oOutCv := oInCv + 2 * nIn
  let oDep := oOutCv + 2 * nOut
  if k = 0 then .merkleRoot
  else if k < oCm then .nullifier (k - oNf)
  else if k < oPub then .outCm (k - oCm)
  else if k = oPub then .publicAssetId
  else if k = oPub + 1 then .publicIn
  else if k = oPub + 2 then .publicOut
  else if k < oOutCv then
    (if (k - oInCv) % 2 = 0 then .inCvX ((k - oInCv) / 2) else .inCvY ((k - oInCv) / 2))
  else if k < oDep then
    (if (k - oOutCv) % 2 = 0 then .outCvX ((k - oOutCv) / 2) else .outCvY ((k - oOutCv) / 2))
  else
    (if (k - oDep) % 2 = 0 then .outCvDepX ((k - oDep) / 2) else .outCvDepY ((k - oDep) / 2))

/-- The signal a slot names. -/
def slotValue (w : TxWitness depth nIn nOut) : PISlot → F
  | .merkleRoot => w.merkleRoot
  | .nullifier i => (w.spent i).nullifier
  | .outCm j => (w.out j).cm
  | .publicAssetId => w.publicAssetId
  | .publicIn => w.publicIn
  | .publicOut => w.publicOut
  | .inCvX i => (w.spent i).cv.x
  | .inCvY i => (w.spent i).cv.y
  | .outCvX j => (w.out j).cv.x
  | .outCvY j => (w.out j).cv.y
  | .outCvDepX j => (w.outCvDep j).x
  | .outCvDepY j => (w.outCvDep j).y

/-- The `PolyEval` coefficient vector. -/
def txCoeffs (w : TxWitness depth nIn nOut) (k : ℕ) : F :=
  slotValue w (piSlot nIn nOut k)

/-! ### Inverting the layout

`piSlot` maps a coefficient index to a slot. `slotIndex` maps back, turning "these two
transactions differ in `nullifier[1]`" into "their coefficient vectors differ at index
`k`", the hypothesis `polyEval_binding` needs.
-/

/-- The slots a `(nIn, nOut)` instance has. Indexed constructors are in range only
for the slots that exist. -/
def PISlot.InRange (nIn nOut : ℕ) : PISlot → Prop
  | .nullifier i | .inCvX i | .inCvY i => i < nIn
  | .outCm j | .outCvX j | .outCvY j | .outCvDepX j | .outCvDepY j => j < nOut
  | _ => True

/-- The coefficient index a slot occupies — the inverse of `piSlot` on in-range slots. -/
def slotIndex (nIn nOut : ℕ) : PISlot → ℕ
  | .merkleRoot => 0
  | .nullifier i => 1 + i
  | .outCm j => 1 + nIn + j
  | .publicAssetId => 1 + nIn + nOut
  | .publicIn => 1 + nIn + nOut + 1
  | .publicOut => 1 + nIn + nOut + 2
  | .inCvX i => 4 + nIn + nOut + 2 * i
  | .inCvY i => 4 + nIn + nOut + 2 * i + 1
  | .outCvX j => 4 + 3 * nIn + nOut + 2 * j
  | .outCvY j => 4 + 3 * nIn + nOut + 2 * j + 1
  | .outCvDepX j => 4 + 3 * nIn + 3 * nOut + 2 * j
  | .outCvDepY j => 4 + 3 * nIn + 3 * nOut + 2 * j + 1

theorem slotIndex_lt {nIn nOut : ℕ} {s : PISlot} (hs : s.InRange nIn nOut) :
    slotIndex nIn nOut s < piCount nIn nOut := by
  cases s <;> simp only [PISlot.InRange] at hs <;> simp only [slotIndex, piCount] <;> omega

/-- **`slotIndex` is a section of `piSlot`.** -/
theorem piSlot_slotIndex {nIn nOut : ℕ} {s : PISlot} (hs : s.InRange nIn nOut) :
    piSlot nIn nOut (slotIndex nIn nOut s) = s := by
  -- Peel `piSlot`'s if-chain one branch at a time; `omega` decides each condition from the
  -- range hypothesis. The surviving goal is the constructor equality, up to index arithmetic.
  cases s <;> simp only [PISlot.InRange] at hs <;>
    simp only [slotIndex, piSlot] <;>
    repeat' first
      | rfl
      | rw [if_neg (by omega)]
      | rw [if_pos (by omega)]
      | (congr 1; omega)

/-- **`slotIndex` is a retraction of `piSlot` too.** With `piSlot_slotIndex` this makes the
two a bijection between coefficient indices below `piCount` and in-range slots.

`piSlot_slotIndex` suffices to find the index of a named slot, which is all
`transact_pi_binding_slot` needs. This direction shows that no other index carries the
slot, which any statement about a single coefficient being free or pinned requires. -/
theorem slotIndex_piSlot (nIn nOut : ℕ) {k : ℕ} (hk : k < piCount nIn nOut) :
    slotIndex nIn nOut (piSlot nIn nOut k) = k := by
  -- `split_ifs` and `split` both exceed simp's step budget on the `ite` chain under
  -- `slotIndex`'s matcher, so the chain is peeled by hand. Each `rw` is syntactic and the
  -- resulting goal is one linear arithmetic fact, including the interleaved coordinate
  -- slots, where `omega` handles the `/ 2` and `% 2`.
  simp only [piCount] at hk
  simp only [piSlot]
  by_cases h1 : k = 0
  · rw [if_pos h1]; simp only [slotIndex]; omega
  rw [if_neg h1]
  by_cases h2 : k < 1 + nIn
  · rw [if_pos h2]; simp only [slotIndex]; omega
  rw [if_neg h2]
  by_cases h3 : k < 1 + nIn + nOut
  · rw [if_pos h3]; simp only [slotIndex]; omega
  rw [if_neg h3]
  by_cases h4 : k = 1 + nIn + nOut
  · rw [if_pos h4]; simp only [slotIndex]; omega
  rw [if_neg h4]
  by_cases h5 : k = 1 + nIn + nOut + 1
  · rw [if_pos h5]; simp only [slotIndex]; omega
  rw [if_neg h5]
  by_cases h6 : k = 1 + nIn + nOut + 2
  · rw [if_pos h6]; simp only [slotIndex]; omega
  rw [if_neg h6]
  by_cases h7 : k < 1 + nIn + nOut + 3 + 2 * nIn
  · rw [if_pos h7]
    by_cases h7a : (k - (1 + nIn + nOut + 3)) % 2 = 0
    · rw [if_pos h7a]; simp only [slotIndex]; omega
    · rw [if_neg h7a]; simp only [slotIndex]; omega
  rw [if_neg h7]
  by_cases h8 : k < 1 + nIn + nOut + 3 + 2 * nIn + 2 * nOut
  · rw [if_pos h8]
    by_cases h8a : (k - (1 + nIn + nOut + 3 + 2 * nIn)) % 2 = 0
    · rw [if_pos h8a]; simp only [slotIndex]; omega
    · rw [if_neg h8a]; simp only [slotIndex]; omega
  rw [if_neg h8]
  by_cases h9 : (k - (1 + nIn + nOut + 3 + 2 * nIn + 2 * nOut)) % 2 = 0
  · rw [if_pos h9]; simp only [slotIndex]; omega
  · rw [if_neg h9]; simp only [slotIndex]; omega

/-- **A slot occupies exactly one coefficient index.** -/
theorem piSlot_eq_iff {nIn nOut k : ℕ} (hk : k < piCount nIn nOut) {s : PISlot}
    (hs : s.InRange nIn nOut) : piSlot nIn nOut k = s ↔ k = slotIndex nIn nOut s := by
  constructor
  · intro h; rw [← slotIndex_piSlot nIn nOut hk, h]
  · rintro rfl; exact piSlot_slotIndex hs

/-- The coefficient at a slot's index is that slot's signal. -/
theorem txCoeffs_slotIndex {depth nIn nOut : ℕ} (w : TxWitness depth nIn nOut) {s : PISlot}
    (hs : s.InRange nIn nOut) : txCoeffs w (slotIndex nIn nOut s) = slotValue w s := by
  rw [txCoeffs, piSlot_slotIndex hs]

/-! ### Moving one slot

`txCoeffs_eq_update` turns "these two witnesses agree on every public input but one" into
"their coefficient vectors differ in exactly one place", the shape `polyEval_update` and
`polyEval_forge` consume. It uses both halves of the layout bijection: `piSlot_slotIndex`
to place the moved slot, `slotIndex_piSlot` to show no other index carries it.

It states what a free slot would allow an attacker. Every slot in this layout is pinned by
a constraint in `TransactSat`, so no satisfying witness pair differs at a single slot; that
is a property of the layout's membership, not of this lemma, and must be re-established
for any added slot.
-/

/-- Two witnesses agreeing on every slot but `s` have coefficient vectors related by a
single-point update. -/
theorem txCoeffs_eq_update {depth nIn nOut : ℕ} {w w' : TxWitness depth nIn nOut} {s : PISlot}
    (hs : s.InRange nIn nOut) (hother : ∀ s', s' ≠ s → slotValue w' s' = slotValue w s')
    {k : ℕ} (hk : k < piCount nIn nOut) :
    txCoeffs w' k = Function.update (txCoeffs w) (slotIndex nIn nOut s) (slotValue w' s) k := by
  rw [Function.update_apply]
  by_cases hks : k = slotIndex nIn nOut s
  · rw [if_pos hks, hks, txCoeffs, piSlot_slotIndex hs]
  · rw [if_neg hks, txCoeffs, txCoeffs]
    exact hother _ fun hcon => hks ((piSlot_eq_iff hk hs).mp hcon)

/-- The layout as a list of slot names, for `lean/scripts/dump-layout.sh`. -/
def layoutNames (nIn nOut : ℕ) : List String :=
  (List.range (piCount nIn nOut)).map (fun k => reprStr (piSlot nIn nOut k))

end Lelantos
