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

/-- Number of `PolyEval` coefficients: `9 + 3·N_IN + 8·N_OUT`
(`src/lib/poly_eval.circom:43-44`). For `(2, 2)` this is 31. -/
def piCount (nIn nOut : ℕ) : ℕ := 9 + 3 * nIn + 8 * nOut

example : piCount 2 2 = 31 := by norm_num [piCount]

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
  recipient : F
  chainId : F
  payer : F
  relayer : F
  /-- Per-slot sub-circuits. -/
  spent : ℕ → SpentSlot depth
  out : ℕ → OutputSlot
  /-- Deposit value commitments, forwarded to `tree_update_batch`. -/
  outCvDep : ℕ → Pt
  /-- FMD clue fields — `PolyEval`-bound only, no other constraint. -/
  outClueRx : ℕ → F
  outClueRy : ℕ → F
  outClueBits : ℕ → F
  /-- Digest of the encrypted-note payload (`ephPub` and ciphertext, per output).
  `PolyEval`-bound only, exactly like the clue fields: the circuit carries it so that
  tampering with the payload in calldata changes `y`. That the digest is the *real* hash of
  the payload the contract received is a contract obligation, not a circuit property —
  see `ContractObligations` in `Lelantos.Circuit.Transact`. -/
  outAuxDigest : F
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
  /-- Group-level readings of the points `PerAssetPointBalance` sums. -/
  inCvG : ℕ → G
  outCvG : ℕ → G
  inRHG : ℕ → G
  outRHG : ℕ → G
  pubInG : G
  pubOutG : G
  /-- `PolyEval` accumulator. -/
  peAcc : ℕ → F

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
the other implementations of this ordering — `contracts/src/lib/PubInputs.sol ::
compress(Transact, aux)` and `sdk/src/bundle/snark-compression.ts :: flatten` — rather than
a restatement of a second copy.
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
  | recipient
  | chainId
  | payer
  | relayer
  | outCvDepX (j : ℕ)
  | outCvDepY (j : ℕ)
  | clueRx (j : ℕ)
  | clueRy (j : ℕ)
  | clueBits (j : ℕ)
  | auxDigest
deriving Repr, DecidableEq, Inhabited

/-- The layout of `TransactCompressN(nIn, nOut)` — `src/lib/poly_eval.circom:68-109`.
Single source of truth. -/
def piSlot (nIn nOut : ℕ) (k : ℕ) : PISlot :=
  let oNf := 1
  let oCm := oNf + nIn
  let oPub := oCm + nOut
  let oInCv := oPub + 3
  let oOutCv := oInCv + 2 * nIn
  let oAddr := oOutCv + 2 * nOut
  let oDep := oAddr + 4
  let oClue := oDep + 2 * nOut
  let oAux := oClue + 3 * nOut
  if k = 0 then .merkleRoot
  else if k < oCm then .nullifier (k - oNf)
  else if k < oPub then .outCm (k - oCm)
  else if k = oPub then .publicAssetId
  else if k = oPub + 1 then .publicIn
  else if k = oPub + 2 then .publicOut
  else if k < oOutCv then
    (if (k - oInCv) % 2 = 0 then .inCvX ((k - oInCv) / 2) else .inCvY ((k - oInCv) / 2))
  else if k < oAddr then
    (if (k - oOutCv) % 2 = 0 then .outCvX ((k - oOutCv) / 2) else .outCvY ((k - oOutCv) / 2))
  else if k = oAddr then .recipient
  else if k = oAddr + 1 then .chainId
  else if k = oAddr + 2 then .payer
  else if k = oAddr + 3 then .relayer
  else if k < oClue then
    (if (k - oDep) % 2 = 0 then .outCvDepX ((k - oDep) / 2) else .outCvDepY ((k - oDep) / 2))
  else if oAux ≤ k then .auxDigest
  else if (k - oClue) % 3 = 0 then .clueRx ((k - oClue) / 3)
  else if (k - oClue) % 3 = 1 then .clueRy ((k - oClue) / 3)
  else .clueBits ((k - oClue) / 3)

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
  | .recipient => w.recipient
  | .chainId => w.chainId
  | .payer => w.payer
  | .relayer => w.relayer
  | .outCvDepX j => (w.outCvDep j).x
  | .outCvDepY j => (w.outCvDep j).y
  | .clueRx j => w.outClueRx j
  | .clueRy j => w.outClueRy j
  | .clueBits j => w.outClueBits j
  | .auxDigest => w.outAuxDigest

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
  | .outCm j | .outCvX j | .outCvY j | .outCvDepX j | .outCvDepY j
  | .clueRx j | .clueRy j | .clueBits j => j < nOut
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
  | .recipient => 4 + 3 * nIn + 3 * nOut
  | .chainId => 4 + 3 * nIn + 3 * nOut + 1
  | .payer => 4 + 3 * nIn + 3 * nOut + 2
  | .relayer => 4 + 3 * nIn + 3 * nOut + 3
  | .outCvDepX j => 8 + 3 * nIn + 3 * nOut + 2 * j
  | .outCvDepY j => 8 + 3 * nIn + 3 * nOut + 2 * j + 1
  | .clueRx j => 8 + 3 * nIn + 5 * nOut + 3 * j
  | .clueRy j => 8 + 3 * nIn + 5 * nOut + 3 * j + 1
  | .clueBits j => 8 + 3 * nIn + 5 * nOut + 3 * j + 2
  | .auxDigest => 8 + 3 * nIn + 8 * nOut

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

/-- The coefficient at a slot's index is that slot's signal. -/
theorem txCoeffs_slotIndex {depth nIn nOut : ℕ} (w : TxWitness depth nIn nOut) {s : PISlot}
    (hs : s.InRange nIn nOut) : txCoeffs w (slotIndex nIn nOut s) = slotValue w s := by
  rw [txCoeffs, piSlot_slotIndex hs]

/-- The layout as a list of slot names, for `lean/scripts/dump-layout.sh`. -/
def layoutNames (nIn nOut : ℕ) : List String :=
  (List.range (piCount nIn nOut)).map (fun k => reprStr (piSlot nIn nOut k))

end Lelantos
