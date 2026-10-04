import Lelantos.Circuit.Witness

/-!
# The `Transact` public-input layout

The coefficient layout `TransactCompressN` evaluates into `y` and folds into `digest`: a map
from coefficient index to a named slot (`piSlot`), the value lookup at a slot (`slotValue`),
and the inverse (`slotIndex`) that turns a difference in a named field into a difference at
a coefficient index.

The digest is not in this layout. It is a public output of the circuit, computed over these
coefficients, and is not itself evaluated into `y`. The verifier's public signals are
`(y, digest, z)`.

It is its own module because it is hand-transcribed, is dumped and diffed against the SDK
and the contract by `lean/scripts/dump-layout.sh`, and should be reviewable without reading
either the signal set or the soundness proofs. `Lelantos.Circuit.BatchLayout` is the same
module for `tree_update_batch.circom`.
-/

namespace Lelantos

variable {depth nIn nOut : ℕ}

/-- Number of `PolyEval` coefficients: `N = 3 + N_IN + N_OUT`
(`src/lib/poly_eval.circom:136`). For `(2, 2)` this is 7, for `(4, 6)` it is 13. The same
`N` words, in the same order, are the input of `CoeffDigest`.

**Membership rule.** A logical public input is a coefficient only if it is a signal of the
circuit. The five address and chain words, the FMD clue triples and the payload digest are
not signals, so they are excluded; they are bound by being hashed into the challenge
instead. The challenge preimage is 38 words at the 4x6 shape (`src/4x6.circom:20-33`): these
13 coefficients, the digest word, and 24 challenge-only words.

The digest word is hashed into the challenge and is not a coefficient. A new coefficient is
wired in through `prefix`, so the digest absorbs it. -/
def piCount (nIn nOut : ℕ) : ℕ := 3 + nIn + nOut

example : piCount 2 2 = 7 := by norm_num [piCount]
example : piCount 4 6 = 13 := by norm_num [piCount]

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
  | publicOut
deriving Repr, DecidableEq, Inhabited

/-- The layout of `TransactCompressN(nIn, nOut)`: the ordered `prefix`, filled at
`src/lib/poly_eval.circom:151-163`. Single source of truth. -/
def piSlot (nIn nOut : ℕ) (k : ℕ) : PISlot :=
  let oNf := 1
  let oCm := oNf + nIn
  let oPub := oCm + nOut
  if k = 0 then .merkleRoot
  else if k < oCm then .nullifier (k - oNf)
  else if k < oPub then .outCm (k - oCm)
  else if k = oPub then .publicAssetId
  else .publicOut

/-- The signal a slot names. -/
def slotValue (w : TxWitness depth nIn nOut) : PISlot → F
  | .merkleRoot => w.merkleRoot
  | .nullifier i => (w.spent i).nullifier
  | .outCm j => (w.out j).cm
  | .publicAssetId => w.publicAssetId
  | .publicOut => w.publicOut

/-- The coefficient vector: the `prefix` signal array, which feeds both `CoeffDigest` and
`PolyEval` (`src/lib/poly_eval.circom:165-174`), so the two cannot disagree on order. -/
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
  | .nullifier i => i < nIn
  | .outCm j => j < nOut
  | _ => True

/-- The coefficient index a slot occupies — the inverse of `piSlot` on in-range slots. -/
def slotIndex (nIn nOut : ℕ) : PISlot → ℕ
  | .merkleRoot => 0
  | .nullifier i => 1 + i
  | .outCm j => 1 + nIn + j
  | .publicAssetId => 1 + nIn + nOut
  | .publicOut => 1 + nIn + nOut + 1

theorem slotIndex_lt {nIn nOut : ℕ} {s : PISlot} (hs : s.InRange nIn nOut) :
    slotIndex nIn nOut s < piCount nIn nOut := by
  cases s <;> simp only [PISlot.InRange] at hs <;>
    simp only [slotIndex, piCount] <;> omega

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
  -- The `ite` chain is peeled by hand. Each `rw` is syntactic and the resulting goal is one
  -- linear arithmetic fact.
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
  rw [if_neg h4]; simp only [slotIndex]; omega

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

It states how `y` moves when one slot does. Two satisfying witnesses that differ at a slot
have different public digests unless Poseidon collides (`txCoeffs_determined_by_digest`);
that is a property of `TransactSat`, not of this lemma.
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
