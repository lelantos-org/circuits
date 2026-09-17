import Lelantos.Circuit.BatchWitness

/-!
# The `BatchCompress` public-input layout

`BatchCompress(MAX_L)` (`src/lib/poly_eval.circom:149-191`) folds the batch's public inputs
into `(z, y)` with the same Horner chain `TransactCompressN` uses, so `polyEval_sound` and
`polyEval_binding` cover the evaluation. This module pins the order, and its dump is the
Lean anchor for `test/formal/batch_layout_parity.test.ts`.

All `4 + 6·MAX_L` batch words are coefficients. Transact evaluates only 46 of its 69 words
because the rest are not signals of `4x6.circom` and are bound through the challenge; the
batch has no such words, so every word must be evaluated, since hashing a signal into `z`
binds nothing against a prover that reads `z` first (`polyEval_forge`).

Split from the constraint system for the same reason `Lelantos.Circuit.Layout` is: the
layout is hand-transcribed and dumped by `lean/scripts/dump-layout.sh`, and reviewing it
needs the signal names, not the proofs.
-/

namespace Lelantos


/-- One coefficient position of `BatchCompress`. -/
inductive BatchPISlot where
  | oldRoot
  | newRoot
  | startIndex
  | actualCount
  | cms (k : ℕ)
  | cvDepX (k : ℕ)
  | cvDepY (k : ℕ)
  | leafAsset (k : ℕ)
  | leafPublicIn (k : ℕ)
  | isDeposit (k : ℕ)
deriving Repr, DecidableEq, Inhabited

/-- Number of `BatchCompress` coefficients: `4 + 6·MAX_L`
(`src/lib/poly_eval.circom:150`). At `MAX_L = 8` this is 52. -/
def batchPiCount (maxL : ℕ) : ℕ := 4 + 6 * maxL

example : batchPiCount 8 = 52 := by norm_num [batchPiCount]

/-- The layout of the `pe.coeffs` assignments — `src/lib/poly_eval.circom:166-190`.
Single source of truth, as `piSlot` is for the transact shapes. -/
def batchPiSlot (maxL : ℕ) (i : ℕ) : BatchPISlot :=
  let oCms := 4
  let oCv := oCms + maxL
  let oAsset := oCv + 2 * maxL
  let oPublicIn := oAsset + maxL
  let oDeposit := oPublicIn + maxL
  if i = 0 then .oldRoot
  else if i = 1 then .newRoot
  else if i = 2 then .startIndex
  else if i = 3 then .actualCount
  else if i < oCv then .cms (i - oCms)
  else if i < oAsset then
    (if (i - oCv) % 2 = 0 then .cvDepX ((i - oCv) / 2) else .cvDepY ((i - oCv) / 2))
  else if i < oPublicIn then .leafAsset (i - oAsset)
  else if i < oDeposit then .leafPublicIn (i - oPublicIn)
  else .isDeposit (i - oDeposit)

/-- The signal a batch slot names. -/
def batchSlotValue {depth maxL : ℕ} (w : BatchSignals depth maxL) : BatchPISlot → F
  | .oldRoot => w.oldRoot
  | .newRoot => w.newRoot
  | .startIndex => w.startIndex
  | .actualCount => w.actualCount
  | .cms k => w.cms k
  | .cvDepX k => (w.cvDep k).x
  | .cvDepY k => (w.cvDep k).y
  | .leafAsset k => w.leafAsset k
  | .leafPublicIn k => w.leafPublicIn k
  | .isDeposit k => w.isDeposit k

/-- The `PolyEval` coefficient vector of the batch circuit. The challenge and the
result are wired at `src/lib/poly_eval.circom:192-193`, and `y` reaches the circuit's
own output at `src/tree_update_batch.circom:275`. -/
def batchCoeffs {depth maxL : ℕ} (w : BatchSignals depth maxL) (i : ℕ) : F :=
  batchSlotValue w (batchPiSlot maxL i)

/-- The coefficient index a batch slot occupies — the inverse of `batchPiSlot`. -/
def batchSlotIndex (maxL : ℕ) : BatchPISlot → ℕ
  | .oldRoot => 0
  | .newRoot => 1
  | .startIndex => 2
  | .actualCount => 3
  | .cms k => 4 + k
  | .cvDepX k => 4 + maxL + 2 * k
  | .cvDepY k => 4 + maxL + 2 * k + 1
  | .leafAsset k => 4 + 3 * maxL + k
  | .leafPublicIn k => 4 + 4 * maxL + k
  | .isDeposit k => 4 + 5 * maxL + k

/-- The slots a `maxL` instance has. -/
def BatchPISlot.InRange (maxL : ℕ) : BatchPISlot → Prop
  | .cms k | .cvDepX k | .cvDepY k | .leafAsset k | .leafPublicIn k | .isDeposit k => k < maxL
  | _ => True

theorem batchSlotIndex_lt {maxL : ℕ} {s : BatchPISlot} (hs : s.InRange maxL) :
    batchSlotIndex maxL s < batchPiCount maxL := by
  cases s <;> simp only [BatchPISlot.InRange] at hs <;>
    simp only [batchSlotIndex, batchPiCount] <;> omega

/-- **`batchSlotIndex` is a section of `batchPiSlot`.** -/
theorem batchPiSlot_batchSlotIndex {maxL : ℕ} {s : BatchPISlot} (hs : s.InRange maxL) :
    batchPiSlot maxL (batchSlotIndex maxL s) = s := by
  cases s <;> simp only [BatchPISlot.InRange] at hs <;>
    simp only [batchSlotIndex, batchPiSlot] <;>
    repeat' first
      | rfl
      | rw [if_neg (by omega)]
      | rw [if_pos (by omega)]
      | (congr 1; omega)

/-- The layout as a list of slot names, for `lean/scripts/dump-layout.sh`. -/
def batchLayoutNames (maxL : ℕ) : List String :=
  (List.range (batchPiCount maxL)).map (fun i => reprStr (batchPiSlot maxL i))

end Lelantos
