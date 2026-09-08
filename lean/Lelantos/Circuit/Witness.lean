import Lelantos.Circuit.Spent
import Lelantos.Circuit.Output

/-!
# `Transact` witness and public-input layout

The signal set of `Transact(DEPTH, N_IN, N_OUT)` and the coefficient layout that
`TransactCompressN` folds into the verifier-visible pair `(z, y)`. The constraint system
over these signals is in `Lelantos.Circuit.Transact`.

Keeping the layout in its own module has one purpose: it is the highest-risk piece of hand
transcription in the development, it is dumped and diffed by `lean/scripts/dump-layout.sh`,
and it should be reviewable without reading the soundness proofs.
-/

namespace Lelantos

/-- Number of `PolyEval` coefficients: `4 + 3·N_IN + 5·N_OUT`
(`src/lib/poly_eval.circom:65`). For `(2, 2)` this is 20, for `(4, 6)` it is 46.

**Membership rule.** A logical public input is a coefficient only if some
constraint outside `TransactCompressN` pins it. `PolyEval` is affine in each
coefficient and `z` is an input the prover reads first, so an unpinned
coefficient is one linear equation in one unknown — solve it and `y` is whatever
the contract asks for. The four address words, the FMD clue triples and the
payload digest carry no constraint at all, so they are not here; they are bound
by being hashed into the challenge instead (`PubInputs.TRANSACT_CHALLENGE_WORDS`,
69 words at the 4x6 shape). -/
def piCount (nIn nOut : ℕ) : ℕ := 4 + 3 * nIn + 5 * nOut

example : piCount 2 2 = 20 := by norm_num [piCount]
example : piCount 4 6 = 46 := by norm_num [piCount]

/-- Every signal of `Transact(depth, nIn, nOut)`. -/
structure TxWitness (depth nIn nOut : ℕ) where
  /-- The only verifier-visible pair. -/
  z : F
  y : F
  /-- Logical public inputs. -/
  merkleRoot : F
  publicAssetId : F
  publicIn : F
  publicOut : F
  /-- Per-slot sub-circuits. -/
  spent : ℕ → SpentSlot depth
  out : ℕ → OutputSlot
  /-- Deposit value commitments, forwarded to `tree_update_batch`. -/
  outCvDep : ℕ → Pt
  /-- Public-bucket signals. -/
  pubGen : Pt
  pubAssetBits : ℕ → F
  pubInBits : ℕ → F
  pubOutBits : ℕ → F
  pubInPt : Pt
  pubOutPt : Pt
  /-- `PerAssetValueBalance` intermediates. -/
  vbPubInv : ℕ → F
  vbPubEq : ℕ → F
  vbInInv : ℕ → ℕ → F
  vbInEq : ℕ → ℕ → F
  vbOutInv : ℕ → ℕ → F
  vbOutEq : ℕ → ℕ → F
  vbInTerm : ℕ → ℕ → F
  vbOutTerm : ℕ → ℕ → F
  vbLhs : ℕ → ℕ → F
  vbRhs : ℕ → ℕ → F
  /-- `PolyEval` accumulator. -/
  peAcc : ℕ → F
  /-- Running count of dummy input slots, and the `IsEqual` comparing it to `nIn`.
  `src/lib/transact.circom` rejects the all-dummy witness with it; see
  `TransactSat.not_all_dummy`. -/
  dummyAcc : ℕ → F
  dummyAllInv : F
  dummyAllOut : F

variable {depth nIn nOut : ℕ}

/-- Input asset ids, as `PerAssetValueBalance` sees them. -/
def inAsset (w : TxWitness depth nIn nOut) (i : ℕ) : F := (w.spent i).assetId
/-- Input values. -/
def inValue (w : TxWitness depth nIn nOut) (i : ℕ) : F := (w.spent i).value
/-- Output asset ids. -/
def outAsset (w : TxWitness depth nIn nOut) (j : ℕ) : F := (w.out j).assetId
/-- Output values. -/
def outValue (w : TxWitness depth nIn nOut) (j : ℕ) : F := (w.out j).value

/-! ## Public-input layout

The layout is defined once, as a map from coefficient index to a named slot; the field
value at an index is a separate lookup. Because the dumped names and the values the proofs
use come from the same definition, `lean/scripts/dump-layout.sh` is a cross-check against
the other implementations of this ordering — `contracts/src/libs/PubInputs.sol ::
compress(Transact, aux)` and `test/ref/compress.ts :: coeffs` — rather than a restatement
of a second copy.
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

/-- The layout of `TransactCompressN(nIn, nOut)` — `src/lib/poly_eval.circom:64-108`.
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

`piSlot` maps a coefficient index to a slot. `slotIndex` maps back, which is what turns
"these two transactions differ in `nullifier[1]`" into "their coefficient vectors differ at
index `k`" — the hypothesis `polyEval_binding` needs. Without it the binding theorem can
only be applied by someone who already knows the coefficient index.
-/

/-- The slots a `(nIn, nOut)` instance actually has. Indexed constructors are in range only
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

`piSlot_slotIndex` alone is enough to *find* the index of a named slot, which is all
`transact_pi_binding_slot` needs. This direction is what lets a proof go the other way —
"no index other than this one carries this slot" — which is what any statement about a
*single* coefficient being free or pinned requires. -/
theorem slotIndex_piSlot (nIn nOut : ℕ) {k : ℕ} (hk : k < piCount nIn nOut) :
    slotIndex nIn nOut (piSlot nIn nOut k) = k := by
  -- `split_ifs` and `split` both blow simp's step budget on the `ite` chain under
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

`txCoeffs_eq_update` is the bridge from "these two witnesses agree on every public input
but one" to "their coefficient vectors differ in exactly one place", which is the shape
`polyEval_update` and `polyEval_forge` consume. It needs both halves of the layout
bijection: `piSlot_slotIndex` to place the moved slot, `slotIndex_piSlot` to know no other
index carries it.

Kept as the standing statement of what a free slot would buy an attacker. Every slot in
this layout is pinned by a constraint in `TransactSat`, so no witness pair satisfying its
hypothesis exists at a single slot — but that is a property of the layout's membership, not
of this lemma, and it is the property a future slot addition has to re-establish.
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
