import Lelantos.Circuit.BatchWitness

/-!
# The `BatchCompress` public-input layout

`BatchCompress(MAX_L)` (`src/lib/poly_eval.circom:199-250`) evaluates the batch's public
inputs into `y` with the same Horner chain `TransactCompressN` uses, and folds the same
words into `digest` with the same `CoeffDigest`, so `polyEval_sound`, `polyEval_binding`,
`coeffDigest_sound` and `digest_inj` cover both. This module pins the order, and its dump is
the Lean anchor for `test/formal/batch_layout_parity.test.ts`.

All `4 + 4·MAX_L` batch words are coefficients. Transact evaluates 13 of its 38 challenge
words: one more is the digest, and the remaining 24 are not signals of `4x6.circom` and
are bound through the challenge alone. The batch has no challenge-only words: every word
is a signal of the circuit, so every word is evaluated and digested. Its challenge preimage
is 37 words at `MAX_L = 8`, the 36 coefficients and the digest word.

The digest is not in this layout. It is a public output computed over these coefficients,
and is not evaluated into `y`. `new_root` is not used as the commitment, although every
active word reaches it: it is not injective in the coefficients, since a zero leaf is the
empty leaf and a run with a trailing zero leaf has the same roots as a shorter run.

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
  | leafAsset (k : ℕ)
  | leafPublicIn (k : ℕ)
  | isDeposit (k : ℕ)
deriving Repr, DecidableEq, Inhabited

/-- Number of `BatchCompress` coefficients: `4 + 4·MAX_L`
(`src/lib/poly_eval.circom:200`). At `MAX_L = 8` this is 36. -/
def batchPiCount (maxL : ℕ) : ℕ := 4 + 4 * maxL

example : batchPiCount 8 = 36 := by norm_num [batchPiCount]

/-- The layout of the `coeffs` assignments: the four scalar words, at
`src/lib/poly_eval.circom:216-219`, then the four per-slot arrays, at
`src/lib/poly_eval.circom:221-236`, in the order `cms`, `leaf_asset`, `leaf_public_in`,
`is_deposit`. Single source of truth, as `piSlot` is for the transact shapes. -/
def batchPiSlot (maxL : ℕ) (i : ℕ) : BatchPISlot :=
  let oCms := 4
  let oAsset := oCms + maxL
  let oPublicIn := oAsset + maxL
  let oDeposit := oPublicIn + maxL
  if i = 0 then .oldRoot
  else if i = 1 then .newRoot
  else if i = 2 then .startIndex
  else if i = 3 then .actualCount
  else if i < oAsset then .cms (i - oCms)
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
  | .leafAsset k => w.leafAsset k
  | .leafPublicIn k => w.leafPublicIn k
  | .isDeposit k => w.isDeposit k

/-- The coefficient vector of the batch circuit: the `coeffs` signal array, which feeds
both `CoeffDigest` and `PolyEval` (`src/lib/poly_eval.circom:238-247`), so the two cannot
disagree on order. -/
def batchCoeffs {depth maxL : ℕ} (w : BatchSignals depth maxL) (i : ℕ) : F :=
  batchSlotValue w (batchPiSlot maxL i)

/-- The coefficient index a batch slot occupies — the inverse of `batchPiSlot`. -/
def batchSlotIndex (maxL : ℕ) : BatchPISlot → ℕ
  | .oldRoot => 0
  | .newRoot => 1
  | .startIndex => 2
  | .actualCount => 3
  | .cms k => 4 + k
  | .leafAsset k => 4 + maxL + k
  | .leafPublicIn k => 4 + 2 * maxL + k
  | .isDeposit k => 4 + 3 * maxL + k

/-- The slots a `maxL` instance has. -/
def BatchPISlot.InRange (maxL : ℕ) : BatchPISlot → Prop
  | .cms k | .leafAsset k | .leafPublicIn k | .isDeposit k => k < maxL
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

/-- The coefficient at a slot's index is that slot's signal. -/
theorem batchCoeffs_slotIndex {depth maxL : ℕ} (w : BatchSignals depth maxL) {s : BatchPISlot}
    (hs : s.InRange maxL) : batchCoeffs w (batchSlotIndex maxL s) = batchSlotValue w s := by
  rw [batchCoeffs, batchPiSlot_batchSlotIndex hs]

/-- The layout as a list of slot names, for `lean/scripts/dump-layout.sh`. -/
def batchLayoutNames (maxL : ℕ) : List String :=
  (List.range (batchPiCount maxL)).map (fun i => reprStr (batchPiSlot maxL i))

end Lelantos
