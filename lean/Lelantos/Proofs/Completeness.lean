import Lelantos.Circuit.Transact

/-!
# Non-vacuity: `TransactSat` is satisfiable

`transact_sound` has the shape `TransactSat w → TxWellFormed w`, which is vacuous if
`TransactSat` is unsatisfiable. This file constructs satisfying assignments that discharge
every constraint rather than avoiding them with `nIn = nOut = 0`.

| Witness | What it rules out |
|---|---|
| `minTx` | the whole system being unsatisfiable, and `spentNote_sound`'s `is_dummy = 0` branch being unreachable. Written for an arbitrary shape, so it also inhabits `Transact(11, 4, 6)` |
| `withdrawTx` | the transparent bucket being satisfiable only when empty |
| `dualTx` | the per-asset balance being satisfiable only when one asset carries value, and membership only at position `0` over zero siblings |

`ofParts` assembles all three from the parts that differ and fills in every derived signal.

This is not a completeness theorem about the SDK's witness generator, nor a claim that
every legal transaction is satisfiable.
-/

namespace Lelantos
namespace Witness

/-! ## Bit arrays -/

def zeroBits : ℕ → F := fun _ => 0

theorem num2Bits_zero (n : ℕ) : Num2BitsSat n 0 zeroBits := by
  refine ⟨fun i _ => by simp [zeroBits, IsBit], ?_⟩
  simp [zeroBits]

def oneBits : ℕ → F := fun i => if i = 0 then 1 else 0

theorem num2Bits_one {n : ℕ} (hn : 0 < n) : Num2BitsSat n 1 oneBits := by
  refine ⟨fun i _ => by unfold oneBits; split <;> simp [IsBit], ?_⟩
  unfold oneBits
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb; simp [hb]
  · intro hmem; exact absurd (Finset.mem_range.mpr hn) hmem

/-- Asset id `2` is non-zero in the field, as an output slot requires. -/
theorem two_ne_zero_F : (2 : F) ≠ 0 := by
  simpa using natCast_ne_of_lt (m := 2) (n := 0) two_lt_p p_pos (by norm_num)

def twoBits : ℕ → F := fun i => if i = 1 then 1 else 0

theorem num2Bits_two {n : ℕ} (hn : 1 < n) : Num2BitsSat n 2 twoBits := by
  refine ⟨fun i _ => by unfold twoBits; split <;> simp [IsBit], ?_⟩
  unfold twoBits
  rw [Finset.sum_eq_single 1]
  · norm_num
  · intro b _ hb; simp [hb]
  · intro hmem; exact absurd (Finset.mem_range.mpr hn) hmem

/-! ## Generic witness builders

Each definition produces the signals one gadget expects, with the proof that they satisfy it.
-/

/-- `IsZero`'s witness hint, as circomlib computes it. -/
noncomputable def isZeroInv (x : F) : F := if x = 0 then 0 else x⁻¹

/-- `IsZero`'s output. -/
noncomputable def isZeroOut (x : F) : F := if x = 0 then 1 else 0

theorem isZero_witness (x : F) : IsZeroSat x (isZeroInv x) (isZeroOut x) := by
  unfold isZeroInv isZeroOut
  by_cases hx : x = 0
  · subst hx
    exact ⟨by simp, by simp⟩
  · refine ⟨?_, by simp [hx]⟩
    rw [if_neg hx, if_neg hx, neg_mul, mul_inv_cancel₀ hx]
    ring

/-- `IsEqual`'s witness hint. -/
noncomputable def eqInv (a b : F) : F := if b - a = 0 then 0 else (b - a)⁻¹

/-- `IsEqual`'s output. -/
noncomputable def eqOut (a b : F) : F := if a = b then 1 else 0

theorem isEqual_witness (a b : F) : IsEqualSat a b (eqInv a b) (eqOut a b) := by
  unfold IsEqualSat eqInv eqOut
  by_cases hab : a = b
  · subst hab
    exact ⟨by simp, by simp⟩
  · have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    refine ⟨?_, by simp [hab]⟩
    rw [if_neg hab, if_neg hne, neg_mul, mul_inv_cancel₀ hne]
    ring

/-- The running sum an accumulator chain computes. -/
def accOf (init : F) (t : ℕ → F) : ℕ → F
  | 0 => init
  | i + 1 => accOf init t i + t i

theorem accChain_witness (n : ℕ) (init : F) (t : ℕ → F) :
    AccChainSat n init t (accOf init t) :=
  ⟨rfl, fun _ _ => rfl⟩

/-! ### Two-slot vectors

`pair` describes both the input and the output side of a witness; `pair_forall` /
`pair_cases` discharge the per-slot obligations.
-/

/-- The slot vector holding `hd` at index `0` and `tl i` elsewhere. -/
def pair {α : Type} (hd : α) (tl : ℕ → α) (i : ℕ) : α := if i = 0 then hd else tl i

/-- An accumulator whose only non-zero term sits at index `0` equals that term. -/
theorem accOf_single {t : ℕ → F} (ht : ∀ i, i ≠ 0 → t i = 0) :
    ∀ n, 0 < n → accOf 0 t n = t 0 := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ m ih =>
    intro _
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp [accOf]
    · rw [accOf, ih hm, ht m (by omega), add_zero]

theorem pair_zero {α : Type} (hd : α) (tl : ℕ → α) : pair hd tl 0 = hd := rfl

theorem pair_succ {α : Type} {hd : α} {tl : ℕ → α} {i : ℕ} (h : i ≠ 0) :
    pair hd tl i = tl i := by simp [pair, h]

/-- An index-independent property of both components holds of every slot. -/
theorem pair_forall {α : Type} {P : α → Prop} {hd : α} {tl : ℕ → α}
    (h0 : P hd) (h1 : ∀ i, P (tl i)) (i : ℕ) : P (pair hd tl i) := by
  unfold pair; split
  · exact h0
  · exact h1 i

/-- …and an index-dependent one, given the two cases separately. -/
theorem pair_cases {α : Type} {motive : ℕ → α → Prop} {hd : α} {tl : ℕ → α}
    (h0 : motive 0 hd) (h1 : ∀ i, i ≠ 0 → motive i (tl i)) (i : ℕ) :
    motive i (pair hd tl i) := by
  by_cases h : i = 0
  · subst h; exact h0
  · rw [pair_succ h]; exact h1 i h

/-! ### Merkle chains

Every slot takes position `0` at every level with all-zero siblings, which is a legal path:
`MerkleRoot` does not require the leaf to be at any particular index.
-/

/-- The selector signals for position `0`. -/
def selZero : ℕ → F := fun k => if k = 0 then 1 else 0

theorem pathIndexSelectors_zero : PathIndexSelectorsSat 0 zeroBits selZero := by
  refine ⟨num2Bits_zero 2, ?_, ?_, ?_, ?_⟩ <;> simp [selZero, zeroBits]

theorem merkleLevel4_zero (cur : F) :
    MerkleLevel4Sat cur zeroBits 0 zeroBits selZero (slots 0 cur zeroBits)
      (merkleNode (slots 0 cur zeroBits)) := by
  refine ⟨pathIndexSelectors_zero, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp [slots, selZero, zeroBits]

/-- The hash chain above a leaf. -/
noncomputable def chainFrom (leaf : F) : ℕ → F
  | 0 => leaf
  | d + 1 => merkleNode (slots 0 (chainFrom leaf d) zeroBits)

/-- The root a leaf is opened against, at tree depth `d`. The depth is a parameter because
the deployed shape is `Transact(11, 4, 6)` while the concrete witnesses below sit at
depth 10. -/
noncomputable def rootFrom (d : ℕ) (leaf : F) : F := chainFrom leaf d

theorem merkleRoot_chain (d : ℕ) (leaf : F) :
    MerkleRootSat d leaf (fun _ => zeroBits) (fun _ => 0)
      (fun _ => zeroBits) (fun _ => selZero) (fun d => slots 0 (chainFrom leaf d) zeroBits)
      (chainFrom leaf) (rootFrom d leaf) :=
  ⟨rfl, fun d _ => merkleLevel4_zero (chainFrom leaf d), rfl⟩

/-- A real (non-dummy) membership proof: the recomputed root equals the advertised one. -/
theorem merkleProofOrDummy_real (d : ℕ) (leaf : F) :
    MerkleProofOrDummySat d leaf (fun _ => zeroBits) (fun _ => 0) (rootFrom d leaf) 0
      0 (rootFrom d leaf) (fun _ => zeroBits) (fun _ => selZero)
      (fun d => slots 0 (chainFrom leaf d) zeroBits) (chainFrom leaf) :=
  ⟨by simp [IsBit], merkleRoot_chain d leaf, by ring, by ring⟩

/-- A dummy membership proof: the path is unconstrained, so the advertised `root` is a
parameter. -/
theorem merkleProofOrDummy_dummy (d : ℕ) (leaf root : F) :
    MerkleProofOrDummySat d leaf (fun _ => zeroBits) (fun _ => 0) root 1
      (rootFrom d leaf - root) (rootFrom d leaf) (fun _ => zeroBits) (fun _ => selZero)
      (fun d => slots 0 (chainFrom leaf d) zeroBits) (chainFrom leaf) :=
  ⟨by simp [IsBit], merkleRoot_chain d leaf, rfl, by ring⟩

/-! ## The padding input slot -/

/-- Padding notes commit to the all-zero note. The commitment is also the leaf. -/
noncomputable def padCm : F := noteCm 0 0 0 0 0

/-- One padding input slot. Its `nsk` is `0`, so its nullifier is that of the all-zero note,
an instance of the prover-chosen value described by `dummy_nullifier_unconstrained`. Its
asset id is `0`, which a dummy slot may carry. -/
noncomputable def padSlot (d : ℕ) (root : F) : SpentSlot d where
  assetId := 0
  value := 0
  pk := 0
  rho := 0
  rcm := 0
  nsk := 0
  d := 0
  isDummy := 1
  root := root
  nullifier := nullifierOf (deriveNk 0) 0 padCm
  ivk := deriveIvk 0
  pkDerived := derivePk (deriveIvk 0) 0
  nk := deriveNk 0
  inner := noteInner 0 0 0
  cm := padCm
  valueBits := zeroBits
  assetBits := zeroBits
  assetInv := 0
  assetIsZero := 1
  pathElements := fun _ => zeroBits
  pathIndices := fun _ => 0
  mpB := fun _ => zeroBits
  mpS := fun _ => selZero
  mpC := fun d => slots 0 (chainFrom padCm d) zeroBits
  mpChain := chainFrom padCm
  mpComputed := rootFrom d padCm
  mpDiff := rootFrom d padCm - root

theorem padSlot_sat (d : ℕ) (root : F) : SpentNoteSat (padSlot d root) := by
  refine ⟨rfl, rfl, ?_, num2Bits_zero 64, num2Bits_zero 64, rfl, rfl,
    merkleProofOrDummy_dummy d padCm root, rfl, rfl, ⟨?_, ?_⟩, ?_⟩ <;> simp [padSlot]

theorem padSlot_dummy (d : ℕ) (root : F) :
    IsBit (padSlot d root).isDummy ∧ (padSlot d root).isDummy * (padSlot d root).value = 0 :=
  ⟨by simp [padSlot, IsBit], by simp [padSlot]⟩

/-! ## Output slots

Outputs must carry a non-zero asset id even when their value is zero. Their `rho` is the
Orchard-style derivation from the first input's nullifier.
-/

/-- An output slot carrying `value` of asset `asset`, with `abits` and `bits` the 64-bit
decompositions of the two. -/
noncomputable def outSlotOf (nf0 asset value : F) (abits bits : ℕ → F) (j : ℕ) :
    OutputSlot where
  assetId := asset
  value := value
  pk := 0
  rho := deriveRho nf0 (j : F)
  rcm := 0
  cm := noteCm asset value 0 (deriveRho nf0 (j : F)) 0
  inner := noteInner 0 (deriveRho nf0 (j : F)) 0
  valueBits := bits
  assetBits := abits
  assetInv := asset⁻¹
  assetIsZero := 0

theorem outSlotOf_sat {asset value : F} {abits bits : ℕ → F} (hnz : asset ≠ 0)
    (habits : Num2BitsSat 64 asset abits) (hbits : Num2BitsSat 64 value bits)
    (nf0 : F) (j : ℕ) : OutputNoteSat (outSlotOf nf0 asset value abits bits j) := by
  refine ⟨hbits, habits, ⟨?_, ?_⟩, rfl, rfl, rfl⟩
  · show (0 : F) = -asset * asset⁻¹ + 1
    rw [neg_mul, mul_inv_cancel₀ hnz]
    ring
  · show asset * 0 = 0
    ring

/-! ## A real (non-dummy) spent slot

Inhabits `SpentReal`, the conclusion of `spentNote_sound` under `is_dummy = 0`: one unit of
asset `1`, owned by `nsk = 0` under the diversifier `1`, opened against a root its own path
reaches.
-/

/-- The spender's key, at diversifier `1`. `pk` must equal the derived key, since the
ownership constraint is active for a real slot. -/
noncomputable def realPk : F := pkOfNsk 0 1

/-- One unit of asset `1`, committed. The commitment is the leaf. -/
noncomputable def realCm : F := noteCm 1 1 realPk 0 0

/-- The root this note is opened against, at the shape's depth. -/
noncomputable def realRoot (d : ℕ) : F := rootFrom d realCm

/-- A real spent slot: `is_dummy = 0`, so ownership, the non-zero asset id and Merkle
membership are all enforced. -/
noncomputable def realSlot (d : ℕ) : SpentSlot d where
  assetId := 1
  value := 1
  pk := realPk
  rho := 0
  rcm := 0
  nsk := 0
  d := 1
  isDummy := 0
  root := realRoot d
  nullifier := nullifierOf (deriveNk 0) 0 realCm
  ivk := deriveIvk 0
  pkDerived := derivePk (deriveIvk 0) 1
  nk := deriveNk 0
  inner := noteInner realPk 0 0
  cm := realCm
  valueBits := oneBits
  assetBits := oneBits
  assetInv := 1
  assetIsZero := 0
  pathElements := fun _ => zeroBits
  pathIndices := fun _ => 0
  mpB := fun _ => zeroBits
  mpS := fun _ => selZero
  mpC := fun d => slots 0 (chainFrom realCm d) zeroBits
  mpChain := chainFrom realCm
  mpComputed := realRoot d
  mpDiff := 0

theorem realSlot_sat (d : ℕ) : SpentNoteSat (realSlot d) := by
  refine ⟨rfl, rfl, ?_, num2Bits_one (by norm_num), num2Bits_one (by norm_num), rfl, rfl,
    merkleProofOrDummy_real d realCm, rfl, rfl, ⟨?_, ?_⟩, ?_⟩ <;>
    simp [realSlot, realPk, pkOfNsk]

/-! ## Assembling a transaction

`ofParts` derives the comparator witnesses, the accumulator chains, the digest and the
Horner accumulator from the slots and the transparent bucket.
-/

/-- The parts of a witness that differ between transactions. -/
structure Parts (depth nIn nOut : ℕ) where
  spent : ℕ → SpentSlot depth
  out : ℕ → OutputSlot
  /-- The advertised Merkle root. -/
  root : F
  /-- The transparent bucket: its asset, the amount withdrawn, and their bit
  decompositions. -/
  pubAsset : F
  pubOut : F
  pubAssetBits : ℕ → F
  pubOutBits : ℕ → F

/-- The candidate asset set a witness's balance check iterates over. -/
noncomputable def candOf {depth nIn nOut : ℕ} (w : TxWitness depth nIn nOut) (c : ℕ) : F :=
  candAt nIn nOut (inAsset w) (outAsset w) w.publicAssetId c

/-- `in_term[c][i] = in_value[i] · in_eq[c][i].out`. -/
noncomputable def inTermOf {depth nIn nOut : ℕ} (w : TxWitness depth nIn nOut) (c i : ℕ) : F :=
  inValue w i * eqOut (inAsset w i) (candOf w c)

/-- `out_term[c][j] = out_value[j] · out_eq[c][j].out`. -/
noncomputable def outTermOf {depth nIn nOut : ℕ} (w : TxWitness depth nIn nOut) (c j : ℕ) : F :=
  outValue w j * eqOut (outAsset w j) (candOf w c)

/-- The `lhs[c][·]` accumulator: from `0` up through the input terms. -/
noncomputable def lhsOf {depth nIn nOut : ℕ} (w : TxWitness depth nIn nOut) (c : ℕ) : ℕ → F :=
  accOf 0 (inTermOf w c)

/-- The `rhs[c][·]` accumulator: from the transparent bucket up through the output terms. -/
noncomputable def rhsOf {depth nIn nOut : ℕ} (w : TxWitness depth nIn nOut) (c : ℕ) : ℕ → F :=
  accOf (w.publicOut * eqOut w.publicAssetId (candOf w c)) (outTermOf w c)

/-- The chosen signals, with every derived one left at zero. The challenge is `1`: the
circuit rejects `z = 0`. -/
noncomputable def baseOf {depth nIn nOut : ℕ} (p : Parts depth nIn nOut) :
    TxWitness depth nIn nOut where
  z := 1
  y := 0
  merkleRoot := p.root
  publicAssetId := p.pubAsset
  publicOut := p.pubOut
  digest := 0
  spent := p.spent
  out := p.out
  pubAssetBits := p.pubAssetBits
  pubOutBits := p.pubOutBits
  pubOutInv := isZeroInv p.pubOut
  pubOutIsZero := isZeroOut p.pubOut
  vbPubInv := fun _ => 0
  vbPubEq := fun _ => 0
  vbInInv := fun _ _ => 0
  vbInEq := fun _ _ => 0
  vbOutInv := fun _ _ => 0
  vbOutEq := fun _ _ => 0
  vbInTerm := fun _ _ => 0
  vbOutTerm := fun _ _ => 0
  vbLhs := fun _ _ => 0
  vbRhs := fun _ _ => 0
  dgBlock := fun _ => 0
  peAcc := fun _ => 0
  -- `IsZero(1)`: `inv = 1`, `out = 0`.
  zInv := 1
  zIsZero := 0
  -- The dummy count and the all-dummy comparator. With some slot real, `nIn - count` is
  -- non-zero, so its inverse and `out = 0` satisfy `IsZero`.
  dummyAcc := accOf 0 (fun i => (p.spent i).isDummy)
  dummyAllInv := isZeroInv ((nIn : F) - accOf 0 (fun i => (p.spent i).isDummy) nIn)
  dummyAllOut := 0

/-- The full assignment: the digest and the Horner accumulator are computed from the base's
coefficient vector, which they leave unchanged (`baseOf_coeffs`). -/
noncomputable def ofParts {depth nIn nOut : ℕ} (p : Parts depth nIn nOut) :
    TxWitness depth nIn nOut :=
  let base := baseOf p
  let mid : TxWitness depth nIn nOut :=
    { base with
      digest := coeffDigest (txCoeffs base) (piCount nIn nOut)
      dgBlock := digestBlock (txCoeffs base) (piCount nIn nOut)
      vbPubInv := fun c => eqInv base.publicAssetId (candOf base c)
      vbPubEq := fun c => eqOut base.publicAssetId (candOf base c)
      vbInInv := fun c i => eqInv (inAsset base i) (candOf base c)
      vbInEq := fun c i => eqOut (inAsset base i) (candOf base c)
      vbOutInv := fun c j => eqInv (outAsset base j) (candOf base c)
      vbOutEq := fun c j => eqOut (outAsset base j) (candOf base c)
      vbInTerm := inTermOf base
      vbOutTerm := outTermOf base
      vbLhs := lhsOf base
      vbRhs := rhsOf base }
  { mid with
    peAcc := hornerAcc (txCoeffs mid) (piCount nIn nOut) mid.z
    y := hornerAcc (txCoeffs mid) (piCount nIn nOut) mid.z (piCount nIn nOut) }

@[simp] theorem ofParts_spent {depth nIn nOut : ℕ} (p : Parts depth nIn nOut) : (ofParts p).spent = p.spent := rfl
@[simp] theorem ofParts_out {depth nIn nOut : ℕ} (p : Parts depth nIn nOut) : (ofParts p).out = p.out := rfl
@[simp] theorem ofParts_root {depth nIn nOut : ℕ} (p : Parts depth nIn nOut) : (ofParts p).merkleRoot = p.root := rfl
@[simp] theorem ofParts_pubAsset {depth nIn nOut : ℕ} (p : Parts depth nIn nOut) : (ofParts p).publicAssetId = p.pubAsset := rfl
@[simp] theorem ofParts_pubOut {depth nIn nOut : ℕ} (p : Parts depth nIn nOut) : (ofParts p).publicOut = p.pubOut := rfl

/-- The balance intermediates are the canonical ones, so the only obligation left is the
`lhs[c][N_IN] === rhs[c][N_OUT]` equation itself. -/
theorem valueBalance_ofParts {depth nIn nOut : ℕ} (p : Parts depth nIn nOut)
    (hbal : ∀ c, c < nIn + nOut + 1 → lhsOf (ofParts p) c nIn = rhsOf (ofParts p) c nOut) :
    PerAssetValueBalanceSat nIn nOut (inAsset (ofParts p)) (inValue (ofParts p))
      (outAsset (ofParts p)) (outValue (ofParts p)) (ofParts p).publicAssetId
      (ofParts p).publicOut (ofParts p).vbPubInv (ofParts p).vbPubEq
      (ofParts p).vbInInv (ofParts p).vbInEq (ofParts p).vbOutInv (ofParts p).vbOutEq
      (ofParts p).vbInTerm (ofParts p).vbOutTerm (ofParts p).vbLhs (ofParts p).vbRhs where
  pubEq_sat _ _ := isEqual_witness _ _
  inEq_sat _ _ _ _ := isEqual_witness _ _
  outEq_sat _ _ _ _ := isEqual_witness _ _
  inTerm_def _ _ _ _ := rfl
  outTerm_def _ _ _ _ := rfl
  lhs_chain _ _ := accChain_witness _ _ _
  rhs_chain _ _ := accChain_witness _ _ _
  balanced c hc := hbal c hc

/-- The base and the full assignment have the same coefficient vector: no derived signal,
the digest included, is a coefficient. -/
theorem baseOf_coeffs {depth nIn nOut : ℕ} (p : Parts depth nIn nOut) (k : ℕ) :
    txCoeffs (baseOf p) k = txCoeffs (ofParts p) k := by
  unfold txCoeffs
  cases piSlot nIn nOut k <;> rfl

/-- **The constraint system, reduced to what is specific to a transaction.** The comparator
and accumulator witnesses, the digest fold and the `PolyEval` chain are discharged here; the
hypotheses are the facts that depend on which notes the transaction moves. -/
theorem transactSat_ofParts {depth nIn nOut : ℕ} (p : Parts depth nIn nOut)
    (hspent : ∀ i, SpentNoteSat (p.spent i))
    (hroot : ∀ i, (p.spent i).root = p.root)
    (hdummy : ∀ i, IsBit (p.spent i).isDummy ∧ (p.spent i).isDummy * (p.spent i).value = 0)
    (hrho : ∀ j, (p.out j).rho = deriveRho (p.spent 0).nullifier (j : F))
    (hout : ∀ j, OutputNoteSat (p.out j))
    (hpubAsset : Num2BitsSat 64 p.pubAsset p.pubAssetBits)
    (hpubOut : Num2BitsSat 64 p.pubOut p.pubOutBits)
    (hbucket : isZeroOut p.pubOut * p.pubAsset = 0)
    (hbal : ∀ c, c < nIn + nOut + 1 → lhsOf (ofParts p) c nIn = rhsOf (ofParts p) c nOut)
    (hnotAllDummy : (nIn : F) - accOf 0 (fun i => (p.spent i).isDummy) nIn ≠ 0) :
    TransactSat (ofParts p) where
  spent_sat i _ := hspent i
  spent_root i _ := hroot i
  dummy_zero i _ := hdummy i
  dummy_acc_base := rfl
  dummy_acc_step _ _ := rfl
  dummy_all_eq := by
    -- `IsEqualSat a b inv out` is `IsZeroSat (b - a) inv out`, and `hnotAllDummy` says that
    -- difference is non-zero.
    show IsZeroSat ((nIn : F) - accOf 0 (fun i => (p.spent i).isDummy) nIn) (isZeroInv _) 0
    refine ⟨?_, by ring⟩
    rw [isZeroInv, if_neg hnotAllDummy, neg_mul, mul_inv_cancel₀ hnotAllDummy]
    ring
  not_all_dummy := rfl
  rho_derived j _ := hrho j
  out_sat j _ := hout j
  pub_asset_range := hpubAsset
  pub_out_range := hpubOut
  pub_out_isZero := isZero_witness p.pubOut
  transfer_names_no_asset := hbucket
  value_balance := valueBalance_ofParts p hbal
  digest_def := coeffDigestSat_witness fun k _ => baseOf_coeffs p k
  compress :=
    polyEvalSat_of_acc (show IsZeroSat (1 : F) 1 0 from ⟨by ring, by ring⟩) rfl
      (fun _ => rfl) rfl

/-- The dummy count of a slot vector whose head is real and whose tail is all padding. -/
private theorem accOf_dummies {t : ℕ → F} (h0 : t 0 = 0) (h1 : ∀ i, i ≠ 0 → t i = 1) :
    ∀ n, 0 < n → accOf 0 t n = ((n - 1 : ℕ) : F) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ m ih =>
    intro _
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp [accOf, h0]
    · rw [accOf, ih hm, h1 m (by omega)]
      have hcast : ((m - 1 : ℕ) : F) = (m : F) - 1 := by
        rw [Nat.cast_sub hm]; norm_num
      rw [hcast, show m + 1 - 1 = m from rfl]
      ring

/-- …hence the comparator input `nIn - count` is 1, and in particular non-zero. -/
private theorem notAllDummy_of_head {nIn : ℕ} (hn : 0 < nIn) {t : ℕ → F} (h0 : t 0 = 0)
    (h1 : ∀ i, i ≠ 0 → t i = 1) : (nIn : F) - accOf 0 t nIn ≠ 0 := by
  have hone : (nIn : F) - accOf 0 t nIn = 1 := by
    rw [accOf_dummies h0 h1 nIn hn, Nat.cast_sub hn]
    norm_num
  rw [hone]
  exact one_ne_zero

/-! ## The minimal transaction

Slot `0` spends the real note of asset `1`; every other input slot is padding opened
against the same root. Output `0` receives that unit; every other output is an empty note
of asset `1`. Nothing is withdrawn, so the transparent bucket names asset `0`.

`src/lib/transact.circom` rejects an all-padding witness, so the smallest satisfying
assignment carries one real spend. `TransactSat.not_all_dummy` is the modelled constraint
and `notAllDummy_of_head` discharges it here.

Stated for an arbitrary shape, so it serves both `Transact(10, 2, 2)` and the deployed
`Transact(11, 4, 6)`.
-/

noncomputable def minIn (depth : ℕ) : ℕ → SpentSlot depth :=
  pair (realSlot depth) (fun _ => padSlot depth (realRoot depth))

theorem minIn_sat (depth : ℕ) (i : ℕ) : SpentNoteSat (minIn depth i) :=
  pair_forall (realSlot_sat depth) (fun _ => padSlot_sat depth _) i

theorem minIn_root (depth : ℕ) (i : ℕ) : (minIn depth i).root = realRoot depth :=
  pair_cases (motive := fun (_ : ℕ) (s : SpentSlot depth) => s.root = realRoot depth)
    rfl (fun _ _ => rfl) i

theorem minIn_dummy (depth : ℕ) (i : ℕ) :
    IsBit (minIn depth i).isDummy ∧ (minIn depth i).isDummy * (minIn depth i).value = 0 :=
  pair_forall (P := fun s : SpentSlot depth => IsBit s.isDummy ∧ s.isDummy * s.value = 0)
    ⟨by simp [realSlot, IsBit], by simp [realSlot]⟩ (fun _ => padSlot_dummy depth _) i

theorem minIn_isDummy_head (depth : ℕ) : (minIn depth 0).isDummy = 0 := rfl

theorem minIn_isDummy_tail (depth : ℕ) : ∀ i, i ≠ 0 → (minIn depth i).isDummy = 1 := by
  intro i hi
  simp [minIn, pair, hi, padSlot]

/-- The nullifier the outputs anchor their `rho` on. -/
noncomputable def spendNf0 : F := nullifierOf (deriveNk 0) 0 realCm

noncomputable def minOut : ℕ → OutputSlot :=
  pair (outSlotOf spendNf0 1 1 oneBits oneBits 0) (outSlotOf spendNf0 1 0 oneBits zeroBits)

theorem minOut_sat (j : ℕ) : OutputNoteSat (minOut j) :=
  pair_forall
    (outSlotOf_sat one_ne_zero (num2Bits_one (by norm_num)) (num2Bits_one (by norm_num)) _ _)
    (fun _ => outSlotOf_sat one_ne_zero (num2Bits_one (by norm_num)) (num2Bits_zero 64) _ _) j

theorem minOut_rho (j : ℕ) : (minOut j).rho = deriveRho spendNf0 (j : F) :=
  pair_cases (motive := fun (j : ℕ) (o : OutputSlot) => o.rho = deriveRho spendNf0 (j : F))
    rfl (fun _ _ => rfl) j

noncomputable def minParts (depth nIn nOut : ℕ) : Parts depth nIn nOut where
  spent := minIn depth
  out := minOut
  root := realRoot depth
  pubAsset := 0
  pubOut := 0
  pubAssetBits := zeroBits
  pubOutBits := zeroBits

noncomputable def minTx (depth nIn nOut : ℕ) : TxWitness depth nIn nOut :=
  ofParts (minParts depth nIn nOut)

theorem minTx_sat (depth nIn nOut : ℕ) (hnIn : 0 < nIn) (hnOut : 0 < nOut) :
    TransactSat (minTx depth nIn nOut) :=
  transactSat_ofParts (minParts depth nIn nOut)
    (minIn_sat depth) (minIn_root depth) (minIn_dummy depth) minOut_rho minOut_sat
    (num2Bits_zero 64) (num2Bits_zero 64)
    (by simp [minParts])
    -- Only slot 0 carries value on either side, and both carry one unit of asset `1`, so
    -- each accumulator collapses to `1 · [asset 1 = cand c]`.
    (fun c _ => by
      have hin : ∀ i, i ≠ 0 → inTermOf (ofParts (minParts depth nIn nOut)) c i = 0 := by
        intro i hi
        simp [inTermOf, inValue, minParts, minIn, pair, hi, padSlot]
      have hout : ∀ j, j ≠ 0 → outTermOf (ofParts (minParts depth nIn nOut)) c j = 0 := by
        intro j hj
        simp [outTermOf, outValue, minParts, minOut, pair, hj, outSlotOf]
      have hpubOut : (minParts depth nIn nOut).pubOut = 0 := rfl
      simp only [lhsOf, rhsOf, ofParts_pubOut, hpubOut, zero_mul]
      rw [accOf_single hin nIn hnIn, accOf_single hout nOut hnOut]
      simp [inTermOf, outTermOf, inAsset, inValue, outAsset, outValue, ofParts_spent,
        ofParts_out, minParts, minIn, minOut, pair, realSlot, outSlotOf])
    (notAllDummy_of_head hnIn (minIn_isDummy_head depth) (minIn_isDummy_tail depth))

/-! ## The two-in/two-out instance of it

`spendTx` is `minTx 10 2 2`. The withdrawal is stated over the abbreviations below.
-/

noncomputable abbrev spendIn : ℕ → SpentSlot 10 := minIn 10

theorem spendIn_sat (i : ℕ) : SpentNoteSat (spendIn i) := minIn_sat 10 i

theorem spendIn_root (i : ℕ) : (spendIn i).root = realRoot 10 := minIn_root 10 i

theorem spendIn_dummy (i : ℕ) :
    IsBit (spendIn i).isDummy ∧ (spendIn i).isDummy * (spendIn i).value = 0 :=
  minIn_dummy 10 i

noncomputable def spendTx : TxWitness 10 2 2 := minTx 10 2 2

/-- **A value-moving transaction satisfies the constraint system.** -/
theorem spendTx_sat : TransactSat spendTx := minTx_sat 10 2 2 (by norm_num) (by norm_num)

/-! ## A withdrawal

Spends the shielded asset-`1` note and withdraws its unit through the bucket, which
therefore names asset `1` with `IsZero(public_out) = 0`. Its two outputs are empty notes of
assets `1` and `2`, so the five balance candidates are `1, 0, 1, 2, 1`.
-/

noncomputable def withdrawOut : ℕ → OutputSlot :=
  pair (outSlotOf spendNf0 1 0 oneBits zeroBits 0) (outSlotOf spendNf0 2 0 twoBits zeroBits)

theorem withdrawOut_sat (j : ℕ) : OutputNoteSat (withdrawOut j) :=
  pair_forall
    (outSlotOf_sat one_ne_zero (num2Bits_one (by norm_num)) (num2Bits_zero 64) _ _)
    (fun _ => outSlotOf_sat two_ne_zero_F (num2Bits_two (by norm_num))
      (num2Bits_zero 64) _ _) j

theorem withdrawOut_rho (j : ℕ) : (withdrawOut j).rho = deriveRho spendNf0 (j : F) :=
  pair_cases (motive := fun (j : ℕ) (o : OutputSlot) => o.rho = deriveRho spendNf0 (j : F))
    rfl (fun _ _ => rfl) j

noncomputable def withdrawParts : Parts 10 2 2 where
  spent := spendIn
  out := withdrawOut
  root := realRoot 10
  pubAsset := 1
  pubOut := 1
  pubAssetBits := oneBits
  pubOutBits := oneBits

noncomputable def withdrawTx : TxWitness 10 2 2 := ofParts withdrawParts

/-- **A withdrawal satisfies the constraint system.** -/
theorem withdrawTx_sat : TransactSat withdrawTx :=
  transactSat_ofParts withdrawParts
    spendIn_sat spendIn_root spendIn_dummy withdrawOut_rho withdrawOut_sat
    (num2Bits_one (by norm_num)) (num2Bits_one (by norm_num))
    (by simp [withdrawParts, isZeroOut])
    -- Left: the spent unit of asset `1`. Right: the same unit, leaving through the bucket;
    -- both outputs are empty.
    (fun _ _ => by
      simp only [lhsOf, rhsOf, accOf, inTermOf, outTermOf, inAsset, inValue, outAsset,
        outValue, ofParts_pubOut, ofParts_pubAsset]
      norm_num [ofParts_spent, ofParts_out, withdrawParts, spendIn, minIn, withdrawOut, pair,
        realSlot, padSlot, outSlotOf])
    (notAllDummy_of_head (by norm_num) (minIn_isDummy_head 10) (minIn_isDummy_tail 10))

/-! ## Two real inputs, two assets

Opens two real notes, of assets `1` and `2`, at positions `0` and `1` under the same level-0
node, and pays each out as a note. Both sides of the balance are non-zero for two different
candidates, and the second slot takes a path index other than `0`, with a non-zero sibling.
-/

/-- The selector signals for position `1`. -/
def selOne : ℕ → F := fun k => if k = 1 then 1 else 0

theorem pathIndexSelectors_one : PathIndexSelectorsSat 1 oneBits selOne := by
  refine ⟨num2Bits_one (by norm_num), ?_, ?_, ?_, ?_⟩ <;> simp [selOne, oneBits]

/-- A level whose node sits at position `0`, over arbitrary siblings. -/
theorem merkleLevel4_at0 (cur : F) (sib : ℕ → F) :
    MerkleLevel4Sat cur sib 0 zeroBits selZero (slots 0 cur sib)
      (merkleNode (slots 0 cur sib)) := by
  refine ⟨pathIndexSelectors_zero, ?_, ?_, ?_, ?_, rfl⟩ <;> simp [slots, selZero]

/-- A level whose node sits at position `1`, over arbitrary siblings. -/
theorem merkleLevel4_at1 (cur : F) (sib : ℕ → F) :
    MerkleLevel4Sat cur sib 1 oneBits selOne (slots 1 cur sib)
      (merkleNode (slots 1 cur sib)) := by
  refine ⟨pathIndexSelectors_one, ?_, ?_, ?_, ?_, rfl⟩ <;> simp [slots, selOne]

/-- A per-level signal: `x0` at level `0`, `rest` at every level above. -/
def lvl {α : Type} (x0 rest : α) : ℕ → α
  | 0 => x0
  | _ + 1 => rest

/-- The chain of a leaf whose level-0 parent is `node0`, with an all-zero path above it. -/
noncomputable def chainVia (leaf node0 : F) : ℕ → F
  | 0 => leaf
  | d + 1 => chainFrom node0 d

/-- The child arrays along that chain. -/
noncomputable def childrenVia (c0 : ℕ → F) (node0 : F) : ℕ → ℕ → F
  | 0 => c0
  | d + 1 => slots 0 (chainFrom node0 d) zeroBits

/-- A path that takes an arbitrary first step and then position `0` with zero siblings. -/
theorem merkleRoot_via {leaf idx node0 : F} {sib b s c0 : ℕ → F}
    (h0 : MerkleLevel4Sat leaf sib idx b s c0 node0) (D : ℕ) :
    MerkleRootSat (D + 1) leaf (lvl sib zeroBits) (lvl idx 0) (lvl b zeroBits)
      (lvl s selZero) (childrenVia c0 node0) (chainVia leaf node0) (chainFrom node0 D) where
  base := rfl
  level d _ := by
    cases d with
    | zero => exact h0
    | succ d => exact merkleLevel4_zero (chainFrom node0 d)
  top := rfl

/-- One unit of asset `2`, owned by the same key. -/
noncomputable def cmB : F := noteCm 2 1 realPk 0 0

/-- Level-0 siblings holding `x` in the first sibling slot. -/
def sibOf (x : F) : ℕ → F := fun k => if k = 0 then x else 0

/-- The level-0 node as the first note's path computes it… -/
noncomputable def nodeA : F := merkleNode (slots 0 realCm (sibOf cmB))

/-- …and as the second note's path does. -/
noncomputable def nodeB : F := merkleNode (slots 1 cmB (sibOf realCm))

/-- Both paths rebuild the same four children. -/
theorem nodeA_eq_nodeB : nodeA = nodeB :=
  merkleNode_congr fun k hk => by interval_cases k <;> simp [slots, sibOf]

/-- The root both notes are opened against, at depth `D + 1`. -/
noncomputable def pairRoot (D : ℕ) : F := chainFrom nodeA D

/-- The asset-`1` note, at position `0`. -/
noncomputable def slotA (D : ℕ) : SpentSlot (D + 1) where
  assetId := 1
  value := 1
  pk := realPk
  rho := 0
  rcm := 0
  nsk := 0
  d := 1
  isDummy := 0
  root := pairRoot D
  nullifier := nullifierOf (deriveNk 0) 0 realCm
  ivk := deriveIvk 0
  pkDerived := derivePk (deriveIvk 0) 1
  nk := deriveNk 0
  inner := noteInner realPk 0 0
  cm := realCm
  valueBits := oneBits
  assetBits := oneBits
  assetInv := 1
  assetIsZero := 0
  pathElements := lvl (sibOf cmB) zeroBits
  pathIndices := lvl 0 0
  mpB := lvl zeroBits zeroBits
  mpS := lvl selZero selZero
  mpC := childrenVia (slots 0 realCm (sibOf cmB)) nodeA
  mpChain := chainVia realCm nodeA
  mpComputed := pairRoot D
  mpDiff := 0

theorem slotA_sat (D : ℕ) : SpentNoteSat (slotA D) where
  ivk_def := rfl
  pk_derived := rfl
  owns := by simp [slotA, realPk, pkOfNsk]
  value_range := num2Bits_one (by norm_num)
  asset_range := num2Bits_one (by norm_num)
  inner_def := rfl
  cm_def := rfl
  membership :=
    ⟨by simp [slotA, IsBit], merkleRoot_via (merkleLevel4_at0 realCm (sibOf cmB)) D,
      (sub_self _).symm, by simp [slotA]⟩
  nk_def := rfl
  nf_def := rfl
  asset_isZero := ⟨by simp [slotA], by simp [slotA]⟩
  asset_nonzero_real := by simp [slotA]

/-- The asset-`2` note, at position `1` of the same node. -/
noncomputable def slotB (D : ℕ) : SpentSlot (D + 1) where
  assetId := 2
  value := 1
  pk := realPk
  rho := 0
  rcm := 0
  nsk := 0
  d := 1
  isDummy := 0
  root := pairRoot D
  nullifier := nullifierOf (deriveNk 0) 0 cmB
  ivk := deriveIvk 0
  pkDerived := derivePk (deriveIvk 0) 1
  nk := deriveNk 0
  inner := noteInner realPk 0 0
  cm := cmB
  valueBits := oneBits
  assetBits := twoBits
  assetInv := (2 : F)⁻¹
  assetIsZero := 0
  pathElements := lvl (sibOf realCm) zeroBits
  pathIndices := lvl 1 0
  mpB := lvl oneBits zeroBits
  mpS := lvl selOne selZero
  mpC := childrenVia (slots 1 cmB (sibOf realCm)) nodeB
  mpChain := chainVia cmB nodeB
  mpComputed := chainFrom nodeB D
  mpDiff := 0

theorem slotB_sat (D : ℕ) : SpentNoteSat (slotB D) where
  ivk_def := rfl
  pk_derived := rfl
  owns := by simp [slotB, realPk, pkOfNsk]
  value_range := num2Bits_one (by norm_num)
  asset_range := num2Bits_two (by norm_num)
  inner_def := rfl
  cm_def := rfl
  membership :=
    ⟨by simp [slotB, IsBit], merkleRoot_via (merkleLevel4_at1 cmB (sibOf realCm)) D, by
      show (0 : F) = chainFrom nodeB D - pairRoot D
      rw [pairRoot, nodeA_eq_nodeB, sub_self], by simp [slotB]⟩
  nk_def := rfl
  nf_def := rfl
  asset_isZero := by
    refine ⟨?_, ?_⟩
    · show (0 : F) = -2 * (2 : F)⁻¹ + 1
      rw [neg_mul, mul_inv_cancel₀ two_ne_zero_F]
      ring
    · show (2 : F) * 0 = 0
      ring
  asset_nonzero_real := by simp [slotB]

noncomputable def dualIn : ℕ → SpentSlot 10 := pair (slotA 9) (fun _ => slotB 9)

theorem dualIn_sat (i : ℕ) : SpentNoteSat (dualIn i) :=
  pair_forall (slotA_sat 9) (fun _ => slotB_sat 9) i

theorem dualIn_root (i : ℕ) : (dualIn i).root = pairRoot 9 :=
  pair_cases (motive := fun (_ : ℕ) (s : SpentSlot 10) => s.root = pairRoot 9)
    rfl (fun _ _ => rfl) i

theorem dualIn_dummy (i : ℕ) :
    IsBit (dualIn i).isDummy ∧ (dualIn i).isDummy * (dualIn i).value = 0 :=
  pair_forall (P := fun s : SpentSlot 10 => IsBit s.isDummy ∧ s.isDummy * s.value = 0)
    ⟨by simp [slotA, IsBit], by simp [slotA]⟩
    (fun _ => ⟨by simp [slotB, IsBit], by simp [slotB]⟩) i

noncomputable def dualOut : ℕ → OutputSlot :=
  pair (outSlotOf spendNf0 1 1 oneBits oneBits 0) (outSlotOf spendNf0 2 1 twoBits oneBits)

theorem dualOut_sat (j : ℕ) : OutputNoteSat (dualOut j) :=
  pair_forall
    (outSlotOf_sat one_ne_zero (num2Bits_one (by norm_num)) (num2Bits_one (by norm_num)) _ _)
    (fun _ => outSlotOf_sat two_ne_zero_F (num2Bits_two (by norm_num))
      (num2Bits_one (by norm_num)) _ _) j

theorem dualOut_rho (j : ℕ) : (dualOut j).rho = deriveRho spendNf0 (j : F) :=
  pair_cases (motive := fun (j : ℕ) (o : OutputSlot) => o.rho = deriveRho spendNf0 (j : F))
    rfl (fun _ _ => rfl) j

noncomputable def dualParts : Parts 10 2 2 where
  spent := dualIn
  out := dualOut
  root := pairRoot 9
  pubAsset := 0
  pubOut := 0
  pubAssetBits := zeroBits
  pubOutBits := zeroBits

noncomputable def dualTx : TxWitness 10 2 2 := ofParts dualParts

/-- **A two-asset transaction satisfies the constraint system.** -/
theorem dualTx_sat : TransactSat dualTx :=
  transactSat_ofParts dualParts
    dualIn_sat dualIn_root dualIn_dummy dualOut_rho dualOut_sat
    (num2Bits_zero 64) (num2Bits_zero 64)
    (by simp [dualParts])
    -- Left: one unit of asset `1` and one of asset `2`. Right: the same two units as notes;
    -- the bucket is empty.
    (fun _ _ => by
      simp only [lhsOf, rhsOf, accOf, inTermOf, outTermOf, inAsset, inValue, outAsset,
        outValue, ofParts_pubOut, ofParts_pubAsset]
      norm_num [ofParts_spent, ofParts_out, dualParts, dualIn, dualOut, pair, slotA, slotB,
        outSlotOf])
    (by simpa [dualParts, dualIn, accOf, pair, slotA, slotB] using two_ne_zero_F)

end Witness

/-- **`transact_sound` is not vacuous.** There is an assignment satisfying the whole
constraint system, at `TxWitness 10 2 2`; the deployed `Transact(11, 4, 6)` has its own
witness below. -/
theorem transactSat_satisfiable : ∃ w : TxWitness 10 2 2, TransactSat w :=
  ⟨Witness.minTx 10 2 2, Witness.minTx_sat 10 2 2 (by norm_num) (by norm_num)⟩

/-- The conclusion is derivable for it. -/
theorem transact_wellFormed_witness : TxWellFormed (Witness.minTx 10 2 2) :=
  transact_sound (by norm_num) (by norm_num) (Witness.minTx_sat 10 2 2 (by norm_num) (by norm_num))

/-- **`transact4x6_sound` is not vacuous.** The deployed shape, `Transact(11, 4, 6)`.
`Transact4x6` is a distinct type from the one above, so this does not follow from
`transactSat_satisfiable`. -/
theorem transact4x6Sat_satisfiable : ∃ w : Transact4x6, TransactSat w :=
  ⟨Witness.minTx 11 4 6, Witness.minTx_sat 11 4 6 (by norm_num) (by norm_num)⟩

/-- The conclusion is derivable at the target shape. -/
theorem transact4x6_wellFormed_witness : TxWellFormed (Witness.minTx 11 4 6) :=
  transact4x6_sound (Witness.minTx_sat 11 4 6 (by norm_num) (by norm_num))

/-- **`SpentReal` is inhabited.** `spentNote_sound` concludes `SpentReal` from
`is_dummy = 0`; this exhibits a slot satisfying `SpentNoteSat` with the flag clear, so that
case is reachable. -/
theorem spentNoteSat_real_satisfiable : ∃ s : SpentSlot 10, SpentNoteSat s ∧ s.isDummy = 0 :=
  ⟨Witness.realSlot 10, Witness.realSlot_sat 10, rfl⟩

/-- The ownership, non-zero asset and membership conclusions are derivable for it. -/
theorem spentReal_witness : SpentReal (Witness.realSlot 10) :=
  spentNote_sound (Witness.realSlot_sat 10) rfl

/-- **A transaction that moves value is satisfiable.** The witness spends one unit of asset
`1` through a non-dummy input slot into an output note, and withdraws nothing. -/
theorem transactSat_spend_satisfiable :
    ∃ w : TxWitness 10 2 2, TransactSat w ∧ (w.spent 0).isDummy = 0 ∧ (w.out 0).value = 1 ∧
      w.publicOut = 0 ∧ w.publicAssetId = 0 :=
  ⟨Witness.spendTx, Witness.spendTx_sat, rfl, rfl, rfl, rfl⟩

/-- Its well-formedness conclusion, including per-asset conservation of a non-zero
amount. -/
theorem transact_wellFormed_spend : TxWellFormed Witness.spendTx :=
  transact_sound (by norm_num) (by norm_num) Witness.spendTx_sat

/-- **A withdrawal is satisfiable.** The bucket names a non-zero asset with a non-zero
amount, and the outputs carry two different asset ids, so the balance candidates do not all
agree. -/
theorem transactSat_withdraw_satisfiable :
    ∃ w : TxWitness 10 2 2, TransactSat w ∧
      w.publicAssetId = 1 ∧ w.publicOut = 1 ∧ outAsset w 0 ≠ outAsset w 1 :=
  ⟨Witness.withdrawTx, Witness.withdrawTx_sat, rfl, rfl, by
    show (1 : F) ≠ 2
    simpa using natCast_ne_of_lt (m := 1) (n := 2) one_lt_p two_lt_p (by norm_num)⟩

theorem transact_wellFormed_withdraw : TxWellFormed Witness.withdrawTx :=
  transact_sound (by norm_num) (by norm_num) Witness.withdrawTx_sat

/-- **A transaction moving two distinct assets is satisfiable.** Both input slots are real,
opened at different positions under one root, and carry one unit each of assets `1` and
`2`; each unit leaves as an output note, so the per-asset balance is satisfied with
non-zero sums for two different candidates. -/
theorem transactSat_twoAsset_satisfiable :
    ∃ w : TxWitness 10 2 2, TransactSat w ∧
      (w.spent 0).isDummy = 0 ∧ (w.spent 1).isDummy = 0 ∧
      inAsset w 0 ≠ inAsset w 1 ∧ inValue w 0 = 1 ∧ inValue w 1 = 1 ∧
      outValue w 0 = 1 ∧ outValue w 1 = 1 :=
  ⟨Witness.dualTx, Witness.dualTx_sat, rfl, rfl, by
    show (1 : F) ≠ 2
    simpa using natCast_ne_of_lt (m := 1) (n := 2) one_lt_p two_lt_p (by norm_num),
    rfl, rfl, rfl, rfl⟩

theorem transact_wellFormed_twoAsset : TxWellFormed Witness.dualTx :=
  transact_sound (by norm_num) (by norm_num) Witness.dualTx_sat

end Lelantos
