import Lelantos.Circuit.Transact

/-!
# Non-vacuity: `TransactSat` is satisfiable

`transact_sound` has the shape `TransactSat w → TxWellFormed w`, which is vacuously true if
`TransactSat` is unsatisfiable. This file rules that out by constructing satisfying
assignments for the deployed instance `Transact(10, 2, 2)`. Each discharges every constraint
— key chain, commitment, range checks, the full ten-level Merkle chain, nullifier, both
value commitments, all five balance candidates, the point balance and the thirty-coefficient
Horner evaluation — rather than dodging them with `nIn = nOut = 0`.

Three transactions, each ruling out a different way for the theorem to be empty:

| Witness | What it rules out |
|---|---|
| `padTx` | the whole system being unsatisfiable |
| `spendTx` | `spentNote_sound`'s `is_dummy = 0` branch being unreachable |
| `dualTx` | the per-asset balance being exercised only where all candidates agree |

`ofParts` assembles all three from the parts that differ; everything derived — comparator
witnesses, accumulator chains, the Horner accumulator — is filled in once.

What this is *not*: a completeness theorem about the SDK's witness generator, and not a
claim that every legal transaction is satisfiable.
-/

namespace Lelantos
namespace Witness

/-! ## Bit arrays -/

/-- The all-zero bit array. -/
def zeroBits : ℕ → F := fun _ => 0

theorem num2Bits_zero (n : ℕ) : Num2BitsSat n 0 zeroBits := by
  refine ⟨fun i _ => by simp [zeroBits, IsBit], ?_⟩
  simp [zeroBits]

theorem bitsNat_zeroBits (n : ℕ) : bitsNat zeroBits n = 0 := by
  simp [bitsNat, zeroBits, bitNat]

/-- The bit array of the value `1`. -/
def oneBits : ℕ → F := fun i => if i = 0 then 1 else 0

theorem num2Bits_one {n : ℕ} (hn : 0 < n) : Num2BitsSat n 1 oneBits := by
  refine ⟨fun i _ => by unfold oneBits; split <;> simp [IsBit], ?_⟩
  unfold oneBits
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb; simp [hb]
  · intro hmem; exact absurd (Finset.mem_range.mpr hn) hmem

/-- Asset id `2` is non-zero in the field — needed by the two-asset witness, where it is the
public bucket's asset. -/
theorem two_ne_zero_F : (2 : F) ≠ 0 := by
  simpa using natCast_ne_of_lt (m := 2) (n := 0) two_lt_p p_pos (by norm_num)

/-- The bit array of the value `2`. -/
def twoBits : ℕ → F := fun i => if i = 1 then 1 else 0

theorem num2Bits_two {n : ℕ} (hn : 1 < n) : Num2BitsSat n 2 twoBits := by
  refine ⟨fun i _ => by unfold twoBits; split <;> simp [IsBit], ?_⟩
  unfold twoBits
  rw [Finset.sum_eq_single 1]
  · norm_num
  · intro b _ hb; simp [hb]
  · intro hmem; exact absurd (Finset.mem_range.mpr hn) hmem

/-! ## Generic witness builders

Each definition here produces the signals one gadget expects, together with the proof that
they satisfy it. The two transactions below are assembled from these, so the constraints are
discharged by the same construction the circuit performs rather than side-stepped.
-/

/-- The generator for asset `a`. -/
noncomputable def gen (a : F) : Pt := coords (assetGen a)

/-- `value · V^a`, for the value the bit array denotes. -/
noncomputable def vTOf (bits : ℕ → F) (a : F) : Pt := escalarMul (bitsNat bits 64) (gen a)

/-- `rcv · H` for `rcv = 0`. Every witness here uses zero blinding. -/
noncomputable def rH : Pt := escalarMul (bitsNat zeroBits 253) (coords H)

/-- The resulting value commitment. -/
noncomputable def cvOf (bits : ℕ → F) (a : F) : Pt := babyAdd (vTOf bits a) rH

theorem rH_eq : rH = coords 0 := by
  rw [rH, bitsNat_zeroBits, escalarMul_spec]
  simp

theorem bitsNat_oneBits {n : ℕ} (hn : 0 < n) : bitsNat oneBits n = 1 := by
  unfold bitsNat oneBits
  rw [Finset.sum_eq_single 0]
  · simp [bitNat]
  · intro b _ hb; simp [bitNat, hb]
  · intro hmem; exact absurd (Finset.mem_range.mpr hn) hmem

theorem vTOf_zero (a : F) : vTOf zeroBits a = coords 0 := by
  rw [vTOf, gen, bitsNat_zeroBits, escalarMul_spec]
  simp

theorem cvOf_zero (a : F) : cvOf zeroBits a = coords 0 := by
  rw [cvOf, vTOf_zero, rH_eq, babyAdd_spec]
  simp

theorem valueCommit_witness (bits : ℕ → F) (a : F) :
    ValueCommitSat bits (gen a) 0 zeroBits (vTOf bits a) rH (cvOf bits a) :=
  ⟨rfl, ⟨num2Bits_zero 253, rfl⟩, rfl⟩

/-- The subgroup element a value commitment opens to, for zero blinding. -/
noncomputable def cvG (bits : ℕ → F) (a : F) : G :=
  valScalar bits • assetGen a + blindScalar zeroBits • H

theorem cvOf_eq_coords (bits : ℕ → F) (a : F) : cvOf bits a = coords (cvG bits a) :=
  (valueCommit_group (valueCommit_witness bits a)).1

theorem blindScalar_zero : blindScalar zeroBits = 0 := by
  unfold blindScalar; rw [bitsNat_zeroBits]; simp

theorem valScalar_zeroBits : valScalar zeroBits = 0 := by
  unfold valScalar; rw [bitsNat_zeroBits]; simp

theorem valScalar_oneBits : valScalar oneBits = 1 := by
  unfold valScalar; rw [bitsNat_oneBits (by norm_num)]; simp

/-- With zero blinding, a commitment to one unit is the asset generator itself, and a
commitment to nothing is the identity. These are the only two openings the witnesses use. -/
theorem cvG_one (a : F) : cvG oneBits a = assetGen a := by
  simp [cvG, valScalar_oneBits, blindScalar_zero]

theorem cvG_zero (a : F) : cvG zeroBits a = 0 := by
  simp [cvG, valScalar_zeroBits, blindScalar_zero]

theorem cvOf_one_coords (a : F) : cvOf oneBits a = coords (assetGen a) := by
  rw [cvOf_eq_coords, cvG_one]

theorem cvOf_zero_coords (a : F) : cvOf zeroBits a = coords 0 := by
  rw [cvOf_eq_coords, cvG_zero]

theorem vTOf_one (a : F) : vTOf oneBits a = coords (assetGen a) := by
  rw [vTOf, gen, escalarMul_spec, bitsNat_oneBits (by norm_num)]
  simp

/-- `IsZero`'s witness hint, as circomlib computes it. -/
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

Both the input and the output side of a `Transact(10, 2, 2)` witness are described by "this
slot at index `0`, that one everywhere else". `pair` names the shape once and
`pair_forall` / `pair_cases` discharge the per-slot obligations in one line each.
-/

/-- The slot vector holding `hd` at index `0` and `tl i` elsewhere. -/
def pair {α : Type} (hd : α) (tl : ℕ → α) (i : ℕ) : α := if i = 0 then hd else tl i

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

/-- The root a leaf is opened against. -/
noncomputable def rootFrom (leaf : F) : F := chainFrom leaf 10

theorem merkleRoot_chain (leaf : F) :
    MerkleRootSat 10 leaf (fun _ => zeroBits) (fun _ => 0)
      (fun _ => zeroBits) (fun _ => selZero) (fun d => slots 0 (chainFrom leaf d) zeroBits)
      (chainFrom leaf) (rootFrom leaf) :=
  ⟨rfl, fun d _ => merkleLevel4_zero (chainFrom leaf d), rfl⟩

/-- A real (non-dummy) membership proof: the recomputed root equals the advertised one. -/
theorem merkleProofOrDummy_real (leaf : F) :
    MerkleProofOrDummySat 10 leaf (fun _ => zeroBits) (fun _ => 0) (rootFrom leaf) 0
      0 (rootFrom leaf) (fun _ => zeroBits) (fun _ => selZero)
      (fun d => slots 0 (chainFrom leaf d) zeroBits) (chainFrom leaf) :=
  ⟨by simp [IsBit], merkleRoot_chain leaf, by ring, by ring⟩

/-- A dummy membership proof: the path is unconstrained, so the advertised `root` is a
parameter and the difference is left non-zero. -/
theorem merkleProofOrDummy_dummy (leaf root : F) :
    MerkleProofOrDummySat 10 leaf (fun _ => zeroBits) (fun _ => 0) root 1
      (rootFrom leaf - root) (rootFrom leaf) (fun _ => zeroBits) (fun _ => selZero)
      (fun d => slots 0 (chainFrom leaf d) zeroBits) (chainFrom leaf) :=
  ⟨by simp [IsBit], merkleRoot_chain leaf, rfl, by ring⟩

/-! ## The padding input slot -/

/-- Padding notes commit to the all-zero note. -/
noncomputable def padCm : F := noteCommitment 0 0 0 0 0

/-- …whose leaf hashes its (identity) deposit commitment. -/
noncomputable def padLeaf : F := leafHash padCm (cvOf zeroBits 0).x (cvOf zeroBits 0).y

/-- One padding input slot. Its `nsk` is `0`, so its nullifier is the honest nullifier of
the all-zero note — which is exactly the prover-chosen value
`dummy_nullifier_unconstrained` warns about. -/
noncomputable def padSlot (root : F) : SpentSlot 10 where
  assetId := 0
  value := 0
  pk := 0
  rho := 0
  rcm := 0
  nsk := 0
  rcv := 0
  rcvDep := 0
  isDummy := 1
  root := root
  nullifier := nullifierOf (deriveNk 0) 0 padCm
  cv := cvOf zeroBits 0
  cvDep := cvOf zeroBits 0
  rH := rH
  ivk := deriveIvk 0
  pkDerived := derivePk (deriveIvk 0)
  nk := deriveNk 0
  cm := padCm
  leaf := padLeaf
  valueBits := zeroBits
  assetBits := zeroBits
  rcvBits := zeroBits
  rcvDepBits := zeroBits
  gen := gen 0
  vT := vTOf zeroBits 0
  vTDep := vTOf zeroBits 0
  rHDep := rH
  assetInv := 0
  assetIsZero := 1
  pathElements := fun _ => zeroBits
  pathIndices := fun _ => 0
  mpB := fun _ => zeroBits
  mpS := fun _ => selZero
  mpC := fun d => slots 0 (chainFrom padLeaf d) zeroBits
  mpChain := chainFrom padLeaf
  mpComputed := rootFrom padLeaf
  mpDiff := rootFrom padLeaf - root

theorem padSlot_sat (root : F) : SpentNoteSat (padSlot root) := by
  refine ⟨rfl, rfl, ?_, rfl, num2Bits_zero 64, num2Bits_zero 64, rfl,
    valueCommit_witness zeroBits 0, rfl, merkleProofOrDummy_dummy padLeaf root, rfl, rfl,
    ⟨?_, ?_⟩,
    ?_, valueCommit_witness zeroBits 0⟩ <;> simp [padSlot]

theorem padSlot_dummy (root : F) :
    IsBit (padSlot root).isDummy ∧ (padSlot root).isDummy * (padSlot root).value = 0 :=
  ⟨by simp [padSlot, IsBit], by simp [padSlot]⟩

/-! ## Output slots

Outputs must carry a non-zero asset id even when their value is zero, so they use asset
`1`. Their `rho` is the Orchard-style derivation from the first input's nullifier.
-/

/-- The nullifier the output `rho`s are anchored on. -/
noncomputable def padNf0 : F := nullifierOf (deriveNk 0) 0 padCm

/-- An output slot carrying `value` of asset `asset`, with `abits` and `bits` the 64-bit
decompositions of the two. -/
noncomputable def outSlotOf (nf0 asset value : F) (abits bits : ℕ → F) (j : ℕ) :
    OutputSlot where
  assetId := asset
  value := value
  pk := 0
  rho := deriveRho nf0 (j : F)
  rcm := 0
  rcv := 0
  rcvDep := 0
  cm := noteCommitment asset value 0 (deriveRho nf0 (j : F)) 0
  cv := cvOf bits asset
  cvDep := cvOf bits asset
  rH := rH
  valueBits := bits
  assetBits := abits
  rcvBits := zeroBits
  rcvDepBits := zeroBits
  gen := gen asset
  vT := vTOf bits asset
  vTDep := vTOf bits asset
  rHDep := rH
  assetInv := asset⁻¹
  assetIsZero := 0

theorem outSlotOf_sat {asset value : F} {abits bits : ℕ → F} (hnz : asset ≠ 0)
    (habits : Num2BitsSat 64 asset abits) (hbits : Num2BitsSat 64 value bits)
    (nf0 : F) (j : ℕ) : OutputNoteSat (outSlotOf nf0 asset value abits bits j) := by
  refine ⟨rfl, hbits, ⟨?_, ?_⟩, rfl, habits, rfl, valueCommit_witness bits asset,
    valueCommit_witness bits asset⟩
  · show (0 : F) = -asset * asset⁻¹ + 1
    rw [neg_mul, mul_inv_cancel₀ hnz]
    ring
  · show asset * 0 = 0
    ring

/-- The padding transaction's output slots: asset `1`, value `0`. -/
noncomputable def padOut (j : ℕ) : OutputSlot := outSlotOf padNf0 1 0 oneBits zeroBits j

theorem padOut_sat (j : ℕ) : OutputNoteSat (padOut j) :=
  outSlotOf_sat one_ne_zero (num2Bits_one (by norm_num)) (num2Bits_zero 64) padNf0 j

/-! ## A real (non-dummy) spent slot

Every slot above is padding, so on its own this file would leave `SpentReal` — the
conclusion of `spentNote_sound` — without a single inhabitant, and the theorem's hypothesis
`is_dummy = 0` unshown to be satisfiable. This slot closes that: one unit of asset `1`,
owned by `nsk = 0`, opened against a root its own path reaches.
-/

/-- The spender's key. `pk` must equal the derived key, since the ownership constraint is
active for a real slot. -/
noncomputable def realPk : F := pkOfNsk 0

/-- One unit of asset `1`, committed. -/
noncomputable def realCm : F := noteCommitment 1 1 realPk 0 0

/-- Its leaf, hashing the deposit value commitment of a *non-zero* value. -/
noncomputable def realLeaf : F := leafHash realCm (cvOf oneBits 1).x (cvOf oneBits 1).y

/-- The root this note is opened against. -/
noncomputable def realRoot : F := rootFrom realLeaf

/-- A real spent slot: `is_dummy = 0`, so ownership, the non-zero asset id and Merkle
membership are all enforced rather than bypassed. -/
noncomputable def realSlot : SpentSlot 10 where
  assetId := 1
  value := 1
  pk := realPk
  rho := 0
  rcm := 0
  nsk := 0
  rcv := 0
  rcvDep := 0
  isDummy := 0
  root := realRoot
  nullifier := nullifierOf (deriveNk 0) 0 realCm
  cv := cvOf oneBits 1
  cvDep := cvOf oneBits 1
  rH := rH
  ivk := deriveIvk 0
  pkDerived := derivePk (deriveIvk 0)
  nk := deriveNk 0
  cm := realCm
  leaf := realLeaf
  valueBits := oneBits
  assetBits := oneBits
  rcvBits := zeroBits
  rcvDepBits := zeroBits
  gen := gen 1
  vT := vTOf oneBits 1
  vTDep := vTOf oneBits 1
  rHDep := rH
  assetInv := 1
  assetIsZero := 0
  pathElements := fun _ => zeroBits
  pathIndices := fun _ => 0
  mpB := fun _ => zeroBits
  mpS := fun _ => selZero
  mpC := fun d => slots 0 (chainFrom realLeaf d) zeroBits
  mpChain := chainFrom realLeaf
  mpComputed := realRoot
  mpDiff := 0

theorem realSlot_sat : SpentNoteSat realSlot := by
  refine ⟨rfl, rfl, ?_, rfl, num2Bits_one (by norm_num), num2Bits_one (by norm_num), rfl,
    valueCommit_witness oneBits 1, rfl, merkleProofOrDummy_real realLeaf, rfl, rfl,
    ⟨?_, ?_⟩, ?_, valueCommit_witness oneBits 1⟩ <;> simp [realSlot, realPk, pkOfNsk]

/-! ## Assembling a transaction

The three transactions below differ only in their slots, their public bucket and the group
readings of the points they publish. `ofParts` derives everything else — the comparator
witnesses, the accumulator chains, the forwarded deposit commitments and the Horner
accumulator — so a witness is described by what makes it distinctive rather than by
forty-odd fields of boilerplate.
-/

/-- The parts of a witness that differ between transactions. -/
structure Parts where
  /-- The two spent-note slots. -/
  spent : ℕ → SpentSlot 10
  /-- The two output-note slots. -/
  out : ℕ → OutputSlot
  /-- The advertised Merkle root. -/
  root : F
  /-- The public bucket: its asset, its incoming amount, and their bit decompositions. -/
  pubAsset : F
  pubIn : F
  pubAssetBits : ℕ → F
  pubInBits : ℕ → F
  /-- The subgroup elements the published value commitments open to. -/
  inCvG : ℕ → G
  outCvG : ℕ → G
  pubInG : G

/-- The candidate asset set a witness's balance check iterates over. -/
noncomputable def candOf (w : TxWitness 10 2 2) (c : ℕ) : F :=
  candAt 2 2 (inAsset w) (outAsset w) w.publicAssetId c

/-- `in_term[c][i] = in_value[i] · in_eq[c][i].out`. -/
noncomputable def inTermOf (w : TxWitness 10 2 2) (c i : ℕ) : F :=
  inValue w i * eqOut (inAsset w i) (candOf w c)

/-- `out_term[c][j] = out_value[j] · out_eq[c][j].out`. -/
noncomputable def outTermOf (w : TxWitness 10 2 2) (c j : ℕ) : F :=
  outValue w j * eqOut (outAsset w j) (candOf w c)

/-- The `lhs[c][·]` accumulator, from the public bucket up through the input terms. -/
noncomputable def lhsOf (w : TxWitness 10 2 2) (c : ℕ) : ℕ → F :=
  accOf (w.publicIn * eqOut w.publicAssetId (candOf w c)) (inTermOf w c)

/-- The `rhs[c][·]` accumulator. -/
noncomputable def rhsOf (w : TxWitness 10 2 2) (c : ℕ) : ℕ → F :=
  accOf (w.publicOut * eqOut w.publicAssetId (candOf w c)) (outTermOf w c)

/-- Every witness below has zero blinding, an empty `public_out`, and no address or clue
data; those are fixed here rather than repeated three times. -/
noncomputable def ofParts (p : Parts) : TxWitness 10 2 2 :=
  let base : TxWitness 10 2 2 :=
    { z := 0, y := 0
      merkleRoot := p.root
      publicAssetId := p.pubAsset
      publicIn := p.pubIn
      publicOut := 0
      recipient := 0, chainId := 0, payer := 0, relayer := 0
      spent := p.spent
      out := p.out
      outCvDep := fun j => (p.out j).cvDep
      outClueRx := fun _ => 0, outClueRy := fun _ => 0, outClueBits := fun _ => 0
      outAuxDigest := 0
      pubGen := gen p.pubAsset
      pubAssetBits := p.pubAssetBits
      pubInBits := p.pubInBits
      pubOutBits := zeroBits
      pubInPt := vTOf p.pubInBits p.pubAsset
      pubOutPt := vTOf zeroBits p.pubAsset
      vbPubInv := fun _ => 0, vbPubEq := fun _ => 0
      vbInInv := fun _ _ => 0, vbInEq := fun _ _ => 0
      vbOutInv := fun _ _ => 0, vbOutEq := fun _ _ => 0
      vbInTerm := fun _ _ => 0, vbOutTerm := fun _ _ => 0
      vbLhs := fun _ _ => 0, vbRhs := fun _ _ => 0
      inCvG := p.inCvG, outCvG := p.outCvG
      inRHG := fun _ => 0, outRHG := fun _ => 0
      pubInG := p.pubInG, pubOutG := 0
      peAcc := fun _ => 0 }
  { base with
    vbPubInv := fun c => eqInv base.publicAssetId (candOf base c)
    vbPubEq := fun c => eqOut base.publicAssetId (candOf base c)
    vbInInv := fun c i => eqInv (inAsset base i) (candOf base c)
    vbInEq := fun c i => eqOut (inAsset base i) (candOf base c)
    vbOutInv := fun c j => eqInv (outAsset base j) (candOf base c)
    vbOutEq := fun c j => eqOut (outAsset base j) (candOf base c)
    vbInTerm := inTermOf base
    vbOutTerm := outTermOf base
    vbLhs := lhsOf base
    vbRhs := rhsOf base
    peAcc := hornerAcc (txCoeffs base) (piCount 2 2) base.z
    y := hornerAcc (txCoeffs base) (piCount 2 2) base.z (piCount 2 2) }

@[simp] theorem ofParts_spent (p : Parts) : (ofParts p).spent = p.spent := rfl
@[simp] theorem ofParts_out (p : Parts) : (ofParts p).out = p.out := rfl
@[simp] theorem ofParts_root (p : Parts) : (ofParts p).merkleRoot = p.root := rfl
@[simp] theorem ofParts_pubAsset (p : Parts) : (ofParts p).publicAssetId = p.pubAsset := rfl
@[simp] theorem ofParts_pubIn (p : Parts) : (ofParts p).publicIn = p.pubIn := rfl
@[simp] theorem ofParts_pubOut (p : Parts) : (ofParts p).publicOut = 0 := rfl
@[simp] theorem ofParts_inCvG (p : Parts) : (ofParts p).inCvG = p.inCvG := rfl
@[simp] theorem ofParts_outCvG (p : Parts) : (ofParts p).outCvG = p.outCvG := rfl
@[simp] theorem ofParts_inRHG (p : Parts) : (ofParts p).inRHG = fun _ => (0 : G) := rfl
@[simp] theorem ofParts_outRHG (p : Parts) : (ofParts p).outRHG = fun _ => (0 : G) := rfl
@[simp] theorem ofParts_pubInG (p : Parts) : (ofParts p).pubInG = p.pubInG := rfl
@[simp] theorem ofParts_pubOutG (p : Parts) : (ofParts p).pubOutG = 0 := rfl

/-- The balance intermediates are the canonical ones, so the only obligation left is the
`lhs[c][N_IN] === rhs[c][N_OUT]` equation itself. -/
theorem valueBalance_ofParts (p : Parts)
    (hbal : ∀ c, c < 5 → lhsOf (ofParts p) c 2 = rhsOf (ofParts p) c 2) :
    PerAssetValueBalanceSat 2 2 (inAsset (ofParts p)) (inValue (ofParts p))
      (outAsset (ofParts p)) (outValue (ofParts p)) (ofParts p).publicAssetId
      (ofParts p).publicIn (ofParts p).publicOut (ofParts p).vbPubInv (ofParts p).vbPubEq
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

/-- **The constraint system, reduced to what is specific to a transaction.** Everything
generic — the comparator and accumulator witnesses, the public-bucket wiring, the zero
blinding factors and the `PolyEval` chain — is discharged here; the hypotheses are exactly
the facts that depend on which notes the transaction moves. -/
theorem transactSat_ofParts (p : Parts)
    (hspent : ∀ i, SpentNoteSat (p.spent i))
    (hroot : ∀ i, (p.spent i).root = p.root)
    (hdummy : ∀ i, IsBit (p.spent i).isDummy ∧ (p.spent i).isDummy * (p.spent i).value = 0)
    (hrho : ∀ j, (p.out j).rho = deriveRho (p.spent 0).nullifier (j : F))
    (hout : ∀ j, OutputNoteSat (p.out j))
    (hpubAsset : Num2BitsSat 64 p.pubAsset p.pubAssetBits)
    (hpubIn : Num2BitsSat 64 p.pubIn p.pubInBits)
    (hbal : ∀ c, c < 5 → lhsOf (ofParts p) c 2 = rhsOf (ofParts p) c 2)
    (hpoint : p.inCvG 0 + p.inCvG 1 + p.pubInG = p.outCvG 0 + p.outCvG 1)
    (hinCv : ∀ i, (p.spent i).cv = coords (p.inCvG i))
    (houtCv : ∀ j, (p.out j).cv = coords (p.outCvG j))
    (hinRH : ∀ i, (p.spent i).rH = coords 0)
    (houtRH : ∀ j, (p.out j).rH = coords 0)
    (hpubInPt : vTOf p.pubInBits p.pubAsset = coords p.pubInG) :
    TransactSat (ofParts p) where
  spent_sat i _ := hspent i
  spent_root i _ := hroot i
  dummy_zero i _ := hdummy i
  rho_derived j _ := hrho j
  out_sat j _ := hout j
  cv_dep_bound _ _ := rfl
  pub_gen := rfl
  pub_asset_range := hpubAsset
  pub_in_range := hpubIn
  pub_out_range := num2Bits_zero 64
  pub_in_mul := rfl
  pub_out_mul := rfl
  value_balance := valueBalance_ofParts p hbal
  point_balance := by
    show coords _ = coords _
    simp only [pointSum, Finset.sum_range_succ, Finset.sum_range_zero, ofParts_inCvG,
      ofParts_outCvG, ofParts_inRHG, ofParts_outRHG, ofParts_pubInG, ofParts_pubOutG,
      zero_add, add_zero]
    exact congrArg coords hpoint
  point_in_cv i _ := hinCv i
  point_out_cv j _ := houtCv j
  point_in_rH i _ := hinRH i
  point_out_rH j _ := houtRH j
  point_pub_in := hpubInPt
  point_pub_out := vTOf_zero p.pubAsset
  compress := ⟨rfl, fun _ _ => rfl, rfl⟩

/-! ## The padding transaction

Both inputs are padding and both outputs are empty notes of asset `1`. It moves no value,
but it discharges every constraint — the full ten-level Merkle chain, both value
commitments, all five balance candidates and the thirty-coefficient Horner evaluation.
-/

noncomputable def padParts : Parts where
  spent := fun _ => padSlot (rootFrom padLeaf)
  out := padOut
  root := rootFrom padLeaf
  pubAsset := 0
  pubIn := 0
  pubAssetBits := zeroBits
  pubInBits := zeroBits
  inCvG := fun _ => 0
  outCvG := fun _ => 0
  pubInG := 0

noncomputable def padTx : TxWitness 10 2 2 := ofParts padParts

theorem padTx_sat : TransactSat padTx :=
  transactSat_ofParts padParts
    (fun _ => padSlot_sat _)
    (fun _ => rfl)
    (fun _ => padSlot_dummy _)
    (fun _ => rfl)
    padOut_sat
    (num2Bits_zero 64) (num2Bits_zero 64)
    -- Every value is zero, so both accumulators are zero whichever candidate is selected.
    (fun _ _ => by
      simp [lhsOf, rhsOf, accOf, inTermOf, outTermOf, inAsset, inValue, outAsset, outValue,
        padParts, padSlot, padOut, outSlotOf])
    (by simp [padParts])
    (fun _ => cvOf_zero_coords 0)
    (fun _ => cvOf_zero_coords 1)
    (fun _ => rH_eq)
    (fun _ => rH_eq)
    (vTOf_zero 0)

/-! ## A transaction that spends

Slot `0` spends the real note of asset `1`; slot `1` is padding opened against the same
root. This is the witness that exercises `is_dummy = 0`, a non-zero scalar multiplication in
`ValueCommit`, and a balance whose sums are not all zero.
-/

/-- The nullifier the outputs anchor their `rho` on. -/
noncomputable def spendNf0 : F := nullifierOf (deriveNk 0) 0 realCm

noncomputable def spendIn : ℕ → SpentSlot 10 := pair realSlot (fun _ => padSlot realRoot)

/-- The input-side facts, shared with the two-asset transaction below. -/
theorem spendIn_sat (i : ℕ) : SpentNoteSat (spendIn i) :=
  pair_forall realSlot_sat (fun _ => padSlot_sat _) i

theorem spendIn_root (i : ℕ) : (spendIn i).root = realRoot :=
  pair_forall (P := fun s : SpentSlot 10 => s.root = realRoot) rfl (fun _ => rfl) i

theorem spendIn_dummy (i : ℕ) :
    IsBit (spendIn i).isDummy ∧ (spendIn i).isDummy * (spendIn i).value = 0 :=
  pair_forall (P := fun s : SpentSlot 10 => IsBit s.isDummy ∧ s.isDummy * s.value = 0)
    ⟨by simp [realSlot, IsBit], by simp [realSlot]⟩ (fun _ => padSlot_dummy _) i

theorem spendIn_cv (i : ℕ) : (spendIn i).cv = coords (if i = 0 then assetGen 1 else 0) :=
  pair_cases
    (motive := fun (i : ℕ) (s : SpentSlot 10) =>
      s.cv = coords (if i = 0 then assetGen 1 else 0))
    (cvOf_one_coords 1)
    (fun _ hi => by rw [if_neg hi]; exact cvOf_zero_coords 0) i

theorem spendIn_rH (i : ℕ) : (spendIn i).rH = coords 0 :=
  pair_forall (P := fun s : SpentSlot 10 => s.rH = coords 0) rH_eq (fun _ => rH_eq) i

noncomputable def spendOut : ℕ → OutputSlot :=
  pair (outSlotOf spendNf0 1 1 oneBits oneBits 0) (outSlotOf spendNf0 1 0 oneBits zeroBits)

theorem spendOut_sat (j : ℕ) : OutputNoteSat (spendOut j) :=
  pair_forall
    (outSlotOf_sat one_ne_zero (num2Bits_one (by norm_num)) (num2Bits_one (by norm_num)) _ _)
    (fun _ => outSlotOf_sat one_ne_zero (num2Bits_one (by norm_num)) (num2Bits_zero 64) _ _) j

theorem spendOut_rho (j : ℕ) : (spendOut j).rho = deriveRho spendNf0 (j : F) :=
  pair_cases (motive := fun (j : ℕ) (o : OutputSlot) => o.rho = deriveRho spendNf0 (j : F))
    rfl (fun _ _ => rfl) j

theorem spendOut_cv (j : ℕ) : (spendOut j).cv = coords (if j = 0 then assetGen 1 else 0) :=
  pair_cases
    (motive := fun (j : ℕ) (o : OutputSlot) =>
      o.cv = coords (if j = 0 then assetGen 1 else 0))
    (cvOf_one_coords 1)
    (fun _ hj => by rw [if_neg hj]; exact cvOf_zero_coords 1) j

theorem spendOut_rH (j : ℕ) : (spendOut j).rH = coords 0 :=
  pair_forall (P := fun o : OutputSlot => o.rH = coords 0) rH_eq (fun _ => rH_eq) j

noncomputable def spendParts : Parts where
  spent := spendIn
  out := spendOut
  root := realRoot
  pubAsset := 0
  pubIn := 0
  pubAssetBits := zeroBits
  pubInBits := zeroBits
  inCvG := fun i => if i = 0 then assetGen 1 else 0
  outCvG := fun j => if j = 0 then assetGen 1 else 0
  pubInG := 0

noncomputable def spendTx : TxWitness 10 2 2 := ofParts spendParts

/-- **A value-moving transaction satisfies the constraint system.** -/
theorem spendTx_sat : TransactSat spendTx :=
  transactSat_ofParts spendParts
    spendIn_sat spendIn_root spendIn_dummy spendOut_rho spendOut_sat
    (num2Bits_zero 64) (num2Bits_zero 64)
    -- Both sides collapse to `1 · [asset 1 = cand c]`: one unit in, one unit out.
    (fun _ _ => by
      simp only [lhsOf, rhsOf, accOf, inTermOf, outTermOf, inAsset, inValue, outAsset,
        outValue, ofParts_pubIn, ofParts_pubOut]
      norm_num [ofParts_spent, ofParts_out, spendParts, spendIn, spendOut, pair, realSlot,
        padSlot, outSlotOf])
    (by simp [spendParts])
    spendIn_cv spendOut_cv spendIn_rH spendOut_rH (vTOf_zero 0)

/-! ## A transaction moving two different assets

The witnesses above use a single asset id, so the per-asset machinery is proved but never
exercised on a transaction whose five candidates differ. This one spends the shielded
asset-`1` note and moves a unit of asset `2` in through the transparent bucket and out as a
note. It is also the only witness with a non-zero public input.
-/

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

theorem dualOut_cv (j : ℕ) :
    (dualOut j).cv = coords (if j = 0 then assetGen 1 else assetGen 2) :=
  pair_cases
    (motive := fun (j : ℕ) (o : OutputSlot) =>
      o.cv = coords (if j = 0 then assetGen 1 else assetGen 2))
    (cvOf_one_coords 1)
    (fun _ hj => by rw [if_neg hj]; exact cvOf_one_coords 2) j

theorem dualOut_rH (j : ℕ) : (dualOut j).rH = coords 0 :=
  pair_forall (P := fun o : OutputSlot => o.rH = coords 0) rH_eq (fun _ => rH_eq) j

noncomputable def dualParts : Parts where
  spent := spendIn
  out := dualOut
  root := realRoot
  pubAsset := 2
  pubIn := 1
  pubAssetBits := twoBits
  pubInBits := oneBits
  inCvG := fun i => if i = 0 then assetGen 1 else 0
  outCvG := fun j => if j = 0 then assetGen 1 else assetGen 2
  pubInG := assetGen 2

noncomputable def dualTx : TxWitness 10 2 2 := ofParts dualParts

/-- **A two-asset transaction satisfies the constraint system.** -/
theorem dualTx_sat : TransactSat dualTx :=
  transactSat_ofParts dualParts
    spendIn_sat spendIn_root spendIn_dummy dualOut_rho dualOut_sat
    (num2Bits_two (by norm_num)) (num2Bits_one (by norm_num))
    -- Left: the public unit of asset `2` and the spent unit of asset `1`. Right: the same
    -- two units as output notes.
    (fun _ _ => by
      simp only [lhsOf, rhsOf, accOf, inTermOf, outTermOf, inAsset, inValue, outAsset,
        outValue, ofParts_pubIn, ofParts_pubOut]
      norm_num [ofParts_spent, ofParts_out, dualParts, spendIn, dualOut, pair, realSlot,
        padSlot, outSlotOf]
      ring)
    (by simp [dualParts])
    spendIn_cv dualOut_cv spendIn_rH dualOut_rH (vTOf_one 2)

end Witness

/-- **`transact_sound` is not vacuous.** There is an assignment satisfying the whole
constraint system of `Transact(10, 2, 2)`, so the implication has non-empty domain. -/
theorem transactSat_satisfiable : ∃ w : Transact2x2, TransactSat w :=
  ⟨Witness.padTx, Witness.padTx_sat⟩

/-- …and the conclusion really is derivable for it. -/
theorem transact_wellFormed_witness : TxWellFormed Witness.padTx :=
  transact2x2_sound Witness.padTx_sat

/-- **`SpentReal` is inhabited.** `spentNote_sound` concludes `SpentReal` from
`is_dummy = 0`, and every slot in the padding witness is a dummy — so on its own that
theorem could have been about an unreachable case. This exhibits a slot satisfying
`SpentNoteSat` with the flag clear. -/
theorem spentNoteSat_real_satisfiable : ∃ s : SpentSlot 10, SpentNoteSat s ∧ s.isDummy = 0 :=
  ⟨Witness.realSlot, Witness.realSlot_sat, rfl⟩

/-- …and the ownership, non-zero asset and membership conclusions really are derivable. -/
theorem spentReal_witness : SpentReal Witness.realSlot :=
  spentNote_sound Witness.realSlot_sat rfl

/-- **A transaction that moves value is satisfiable.** The padding witness discharges every
constraint with zero values, which leaves open whether the balance and value-commitment
machinery is satisfiable at all once the sums are non-trivial. This witness spends one unit
of asset `1` through a non-dummy input slot. -/
theorem transactSat_spend_satisfiable :
    ∃ w : Transact2x2, TransactSat w ∧ (w.spent 0).isDummy = 0 ∧ (w.out 0).value = 1 :=
  ⟨Witness.spendTx, Witness.spendTx_sat, rfl, rfl⟩

/-- …and its well-formedness conclusion, including per-asset conservation of a non-zero
amount. -/
theorem transact_wellFormed_spend : TxWellFormed Witness.spendTx :=
  transact2x2_sound Witness.spendTx_sat

/-- **A transaction moving two distinct assets is satisfiable.** Both witnesses above use a
single asset id, which leaves the per-asset balance exercised only where all five candidates
agree. This one spends a shielded unit of asset `1` and moves a unit of asset `2` in through
the transparent bucket, so the candidate set holds two different assets and the public input
is non-zero. -/
theorem transactSat_twoAsset_satisfiable :
    ∃ w : Transact2x2, TransactSat w ∧
      inAsset w 0 ≠ outAsset w 1 ∧ w.publicAssetId = 2 ∧ w.publicIn = 1 :=
  ⟨Witness.dualTx, Witness.dualTx_sat, by
    show (1 : F) ≠ 2
    simpa using natCast_ne_of_lt (m := 1) (n := 2) one_lt_p two_lt_p (by norm_num), rfl, rfl⟩

theorem transact_wellFormed_twoAsset : TxWellFormed Witness.dualTx :=
  transact2x2_sound Witness.dualTx_sat

end Lelantos
