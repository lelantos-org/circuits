import Lelantos.Gadgets.Merkle
import Lelantos.Gadgets.ValueCommit

/-!
# `src/lib/spent.circom` — one spent-note slot

`SpentNote(DEPTH)` opens a note against the commitment tree and emits its nullifier. The
model carries every signal circom declares, including the intermediates, so that the
fidelity harness can compare them one by one against a real witness.

`spentNote_sound` extracts what a **non-dummy** slot proves: ownership (the prover knows
`nsk`), a non-zero asset id, 64-bit values, membership of the leaf under the root, and a
correctly formed nullifier.

The dummy branch deliberately yields nothing. When `is_dummy = 1`:

* the Merkle path is entirely unconstrained,
* `pk` need not derive from `nsk`,
* `asset_id` may be zero,
* and the slot **still emits a prover-chosen `nullifier`**.

Only `DummyZeroValue` (applied by the caller, `src/lib/transact.circom:113-114`) makes this safe,
by forcing `value = 0` so the slot is neutral for value conservation. The prover-chosen
nullifier is a real obligation on the contract's double-spend set, not an artefact of the
model — see `dummy_nullifier_unconstrained`.
-/

namespace Lelantos

/-- Every signal of one `SpentNote(depth)` instance, inputs and intermediates alike. -/
structure SpentSlot (depth : ℕ) where
  -- Note fields.
  assetId : F
  value : F
  pk : F
  rho : F
  rcm : F
  nsk : F
  rcv : F
  rcvDep : F
  isDummy : F
  -- Binding inputs supplied by the caller.
  root : F
  nullifier : F
  -- Value commitments and the exported blinding point.
  cv : Pt
  cvDep : Pt
  rH : Pt
  -- Key-chain and hash intermediates.
  ivk : F
  pkDerived : F
  nk : F
  cm : F
  leaf : F
  -- Bit decompositions.
  valueBits : ℕ → F
  assetBits : ℕ → F
  rcvBits : ℕ → F
  rcvDepBits : ℕ → F
  -- The per-asset generator and the scalar-multiplication intermediates.
  gen : Pt
  vT : Pt
  vTDep : Pt
  rHDep : Pt
  -- `IsZero(asset_id)` signals.
  assetInv : F
  assetIsZero : F
  -- Merkle path and the `MerkleProofOrDummy` intermediates.
  pathElements : ℕ → ℕ → F
  pathIndices : ℕ → F
  mpB : ℕ → ℕ → F
  mpS : ℕ → ℕ → F
  mpC : ℕ → ℕ → F
  mpChain : ℕ → F
  mpComputed : F
  mpDiff : F

/-- The constraint system of `SpentNote(depth)`, in source order.

One named field per circom constraint, each citing its source line. `FIDELITY.md`'s
constraint table is checked against this definition by eye, so it has to be readable a row
at a time; positional projections into a nested conjunction retarget silently when a
constraint is inserted. -/
structure SpentNoteSat {depth : ℕ} (s : SpentSlot depth) : Prop where
  /-- `:46-47` — `ivk = Poseidon(TAG_IVK, nsk)`. -/
  ivk_def : s.ivk = deriveIvk s.nsk
  /-- `:49-50` — `pk_check.pk = Poseidon(TAG_PK, ivk)`. -/
  pk_derived : s.pkDerived = derivePk s.ivk
  /-- `:51` — ownership, real notes only. -/
  owns : (1 - s.isDummy) * (s.pkDerived - s.pk) = 0
  /-- `:54-59` — note commitment, over the *supplied* pk. -/
  cm_def : s.cm = noteCommitment s.assetId s.value s.pk s.rho s.rcm
  /-- `:62-63` — value range. -/
  value_range : RangeCheck64Sat s.value s.valueBits
  /-- `:66-67` — `HashToAssetGen`, which is also where `asset_id < 2^64` is enforced. -/
  asset_bits : Num2BitsSat 64 s.assetId s.assetBits
  /-- `:66-67` — …and its output point. -/
  gen_def : s.gen = coords (assetGen s.assetId)
  /-- `:69-75` — deposit value commitment, sharing the value bits. -/
  cv_dep_sat : ValueCommitSat s.valueBits s.gen s.rcvDep s.rcvDepBits s.vTDep s.rHDep s.cvDep
  /-- `:79-83` — leaf hash. -/
  leaf_def : s.leaf = leafHash s.cm s.cvDep.x s.cvDep.y
  /-- `:86-95` — membership, bypassed for dummies. -/
  membership : MerkleProofOrDummySat depth s.leaf s.pathElements s.pathIndices s.root
    s.isDummy s.mpDiff s.mpComputed s.mpB s.mpS s.mpC s.mpChain
  /-- `:99-100` — `nk = Poseidon(TAG_NK, nsk)`. -/
  nk_def : s.nk = deriveNk s.nsk
  /-- `:102-106` — nullifier. -/
  nf_def : nullifierOf s.nk s.rho s.cm = s.nullifier
  /-- `:109-110` — `IsZero(asset_id)`. -/
  asset_isZero : IsZeroSat s.assetId s.assetInv s.assetIsZero
  /-- `:111` — real notes have a non-zero asset id. -/
  asset_nonzero_real : (1 - s.isDummy) * s.assetIsZero = 0
  /-- `:114-123` — value commitment, sharing the same value bits as `cv_dep`. -/
  cv_sat : ValueCommitSat s.valueBits s.gen s.rcv s.rcvBits s.vT s.rH s.cv

/-- What a non-dummy spent slot establishes. -/
structure SpentReal {depth : ℕ} (s : SpentSlot depth) : Prop where
  /-- The prover knows the spend key: `pk` is the image of `nsk` under the key chain. -/
  owns : s.pk = pkOfNsk s.nsk
  /-- Real notes carry a non-zero asset id, which is also what domain-separates `cm`. -/
  assetNonzero : s.assetId ≠ 0
  /-- Both packed fields are genuinely 64-bit, so the packing is injective. -/
  valueRange : s.value.val < 2 ^ 64
  assetRange : s.assetId.val < 2 ^ 64
  /-- The leaf really sits under the claimed root. -/
  member : MerkleMember depth s.leaf s.pathElements s.pathIndices s.root
  /-- The leaf binds the commitment to its deposit value commitment. -/
  leafShape : s.leaf = leafHash s.cm s.cvDep.x s.cvDep.y
  /-- The commitment opens to the claimed note. -/
  commitment : s.cm = noteCommitment s.assetId s.value s.pk s.rho s.rcm
  /-- The nullifier is the honest one for this note. -/
  nf : s.nullifier = nullifierOf (deriveNk s.nsk) s.rho s.cm
  /-- Every path index is a valid quaternary digit, which is what lets
  `merkleMember_inj` turn `member` into a binding statement rather than a bare
  existential. -/
  pathValid : ∀ d, d < depth → (s.pathIndices d).val < 4
  /-- **`cv` opens to this note's own value under this note's own asset generator.**
  The point published on-chain commits to the `value` that `cm` binds, not to some
  unrelated 64-bit number. -/
  cvOpens : s.cv = coords ((s.value.val : ZMod ell) • assetGen s.assetId
    + blindScalar s.rcvBits • H)
  /-- …and `cv_dep`, the one hashed into the leaf, opens to the same value. -/
  cvDepOpens : s.cvDep = coords ((s.value.val : ZMod ell) • assetGen s.assetId
    + blindScalar s.rcvDepBits • H)

/-- **Soundness of `SpentNote` on a real slot.** -/
theorem spentNote_sound {depth : ℕ} {s : SpentSlot depth}
    (h : SpentNoteSat s) (hreal : s.isDummy = 0) : SpentReal s := by
  have hvc := h.cv_sat
  have hvcd := h.cv_dep_sat
  rw [h.gen_def] at hvc hvcd
  have hown : s.pk = pkOfNsk s.nsk := by
    have howns := h.owns
    rw [hreal, sub_zero, one_mul, sub_eq_zero] at howns
    rw [← howns, h.pk_derived, h.ivk_def]
    rfl
  have hassetNz : s.assetId ≠ 0 := by
    have hnz := h.asset_nonzero_real
    rw [hreal, sub_zero, one_mul] at hnz
    rw [isZero_sound h.asset_isZero] at hnz
    intro hz
    rw [if_pos hz] at hnz
    exact one_ne_zero hnz
  exact
    { owns := hown
      assetNonzero := hassetNz
      valueRange := rangeCheck64_sound h.value_range
      assetRange := (num2Bits_sound (le_of_lt two_pow_64_lt_p) h.asset_bits).2
      member := merkleProofOrDummy_sound h.membership hreal
      leafShape := h.leaf_def
      commitment := h.cm_def
      nf := by rw [← h.nf_def, h.nk_def]
      pathValid := merkleProofOrDummy_idx h.membership
      cvOpens := valueCommit_opens h.value_range hvc
      cvDepOpens := valueCommit_opens h.value_range hvcd }

/-- Every spent slot range-checks its value, dummy or not. -/
theorem spentNote_valueRange {depth : ℕ} {s : SpentSlot depth} (h : SpentNoteSat s) :
    s.value.val < 2 ^ 64 :=
  rangeCheck64_sound h.value_range

/-- The `is_dummy` flag is boolean. -/
theorem spentNote_isDummy_bit {depth : ℕ} {s : SpentSlot depth} (h : SpentNoteSat s) :
    s.isDummy = 0 ∨ s.isDummy = 1 :=
  merkleProofOrDummy_bit h.membership

/-- Even a dummy slot emits a nullifier, and its value is chosen by the prover: `nsk` and
`rho` are unconstrained in that branch, so the emitted `nullifier` is whatever the prover
picked. Recorded as an explicit obligation rather than left implicit. -/
theorem dummy_nullifier_unconstrained {depth : ℕ} {s : SpentSlot depth}
    (h : SpentNoteSat s) : s.nullifier = nullifierOf (deriveNk s.nsk) s.rho s.cm := by
  rw [← h.nf_def, h.nk_def]

end Lelantos
