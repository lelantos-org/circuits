import Lelantos.Gadgets.Merkle
import Lelantos.Gadgets.Balance

/-!
# `src/lib/spent.circom` — one spent-note slot

`SpentNote(DEPTH)` opens a note against the commitment tree and emits its nullifier. The
model carries every signal circom declares, including the intermediates, so that the
fidelity harness can compare them one by one against a real witness.

The tree leaf is the note commitment `cm` itself: there is no leaf hash and no value
commitment. `tree_update_batch.circom` inserts a spend's `out_cm` as it stands and builds a
deposit's leaf from its public `(asset, value)` by the same `NoteCommitment`, so opening
`cm` here pins the note to the `(asset, value)` it was inserted with
(`Lelantos.batch_deposit_spend_binds`).

`spentNote_sound` extracts what a **non-dummy** slot proves: ownership (the prover knows
`nsk`), a non-zero asset id, membership of `cm` under the root, and a correctly formed
nullifier.

The dummy branch yields less. When `is_dummy = 1`:

* the Merkle path is unconstrained,
* `pk` need not derive from `nsk`,
* `asset_id` may be zero,
* and the slot still emits a prover-chosen `nullifier`.

What holds on **every** slot, dummy or not: `value` and `asset_id` are 64-bit
(`spentNote_valueRange`, `spentNote_assetRange`), `cm` is the commitment of the slot's own
fields, and the nullifier is derived from it. The asset bound is unconditional because the
packing inside `NoteCommitment` is injective only under both bounds.

`DummyZeroValue` (applied by the caller, `src/lib/transact.circom:73`) makes the dummy
branch safe by forcing `value = 0`, so the slot is neutral for value conservation. The
prover-chosen nullifier is an obligation on the contract's double-spend set, not a
modelling artefact; see `dummy_nullifier_unconstrained`.
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
  isDummy : F
  -- Binding inputs supplied by the caller.
  root : F
  nullifier : F
  -- Key-chain and hash intermediates.
  ivk : F
  pkDerived : F
  nk : F
  inner : F
  cm : F
  -- Bit decompositions of the two range checks.
  valueBits : ℕ → F
  assetBits : ℕ → F
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
constraint table is checked against this definition row by row; named fields are used
because positional projections into a nested conjunction retarget silently when a
constraint is inserted. -/
structure SpentNoteSat {depth : ℕ} (s : SpentSlot depth) : Prop where
  /-- `src/lib/spent.circom:38-39` — `ivk = Poseidon(TAG_IVK, nsk)`. -/
  ivk_def : s.ivk = deriveIvk s.nsk
  /-- `:41-42` — `pk_check.pk = Poseidon(TAG_PK, ivk)`. -/
  pk_derived : s.pkDerived = derivePk s.ivk
  /-- `:43` — ownership, real notes only. -/
  owns : (1 - s.isDummy) * (s.pkDerived - s.pk) = 0
  /-- `:47-48` — `rng_value`: the value is 64-bit, on every slot. -/
  value_range : RangeCheck64Sat s.value s.valueBits
  /-- `:50-51` — `rng_asset`: the asset id is 64-bit, on every slot, dummies included. -/
  asset_range : RangeCheck64Sat s.assetId s.assetBits
  /-- `:54-57` — `inner = NoteInner(pk, rho, rcm)`, over the *supplied* pk. -/
  inner_def : s.inner = noteInner s.pk s.rho s.rcm
  /-- `:59-62` — `cm = NoteCommitment(asset_id, value, inner)`. -/
  cm_def : s.cm = noteCommitment s.assetId s.value s.inner
  /-- `:65-74` — membership of `cm`, which is the leaf; bypassed for dummies. -/
  membership : MerkleProofOrDummySat depth s.cm s.pathElements s.pathIndices s.root
    s.isDummy s.mpDiff s.mpComputed s.mpB s.mpS s.mpC s.mpChain
  /-- `:78-79` — `nk = Poseidon(TAG_NK, nsk)`. -/
  nk_def : s.nk = deriveNk s.nsk
  /-- `:81-85` — nullifier. -/
  nf_def : nullifierOf s.nk s.rho s.cm = s.nullifier
  /-- `:89-90` — `IsZero(asset_id)`. -/
  asset_isZero : IsZeroSat s.assetId s.assetInv s.assetIsZero
  /-- `:91` — real notes have a non-zero asset id. Id 0 means "no asset". -/
  asset_nonzero_real : (1 - s.isDummy) * s.assetIsZero = 0

/-- What a non-dummy spent slot establishes. -/
structure SpentReal {depth : ℕ} (s : SpentSlot depth) : Prop where
  /-- The prover knows the spend key: `pk` is the image of `nsk` under the key chain. -/
  owns : s.pk = pkOfNsk s.nsk
  /-- Real notes carry a non-zero asset id. -/
  assetNonzero : s.assetId ≠ 0
  /-- Both packed fields are 64-bit, so the packing is injective. -/
  valueRange : s.value.val < 2 ^ 64
  assetRange : s.assetId.val < 2 ^ 64
  /-- The commitment, which is the tree leaf, sits under the claimed root. -/
  member : MerkleMember depth s.cm s.pathElements s.pathIndices s.root
  /-- The commitment opens to the claimed note. -/
  commitment : s.cm = noteCm s.assetId s.value s.pk s.rho s.rcm
  /-- The nullifier is the one derived from this note. -/
  nf : s.nullifier = nullifierOf (deriveNk s.nsk) s.rho s.cm
  /-- Every path index is a valid quaternary digit, which lets `merkleMember_inj` turn
  `member` into a binding statement rather than a bare existential. -/
  pathValid : ∀ d, d < depth → (s.pathIndices d).val < 4

/-- Every spent slot range-checks its value, dummy or not. -/
theorem spentNote_valueRange {depth : ℕ} {s : SpentSlot depth} (h : SpentNoteSat s) :
    s.value.val < 2 ^ 64 :=
  rangeCheck64_sound h.value_range

/-- Every spent slot range-checks its asset id, dummy or not. -/
theorem spentNote_assetRange {depth : ℕ} {s : SpentSlot depth} (h : SpentNoteSat s) :
    s.assetId.val < 2 ^ 64 :=
  rangeCheck64_sound h.asset_range

/-- Every spent slot's `cm` is the commitment of its own five note fields, dummy or not. -/
theorem spentNote_commitment {depth : ℕ} {s : SpentSlot depth} (h : SpentNoteSat s) :
    s.cm = noteCm s.assetId s.value s.pk s.rho s.rcm := by
  rw [h.cm_def, h.inner_def, noteCm]

/-- **Soundness of `SpentNote` on a real slot.** -/
theorem spentNote_sound {depth : ℕ} {s : SpentSlot depth}
    (h : SpentNoteSat s) (hreal : s.isDummy = 0) : SpentReal s := by
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
      valueRange := spentNote_valueRange h
      assetRange := spentNote_assetRange h
      member := merkleProofOrDummy_sound h.membership hreal
      commitment := spentNote_commitment h
      nf := by rw [← h.nf_def, h.nk_def]
      pathValid := merkleProofOrDummy_idx h.membership }

/-- The `is_dummy` flag is boolean. -/
theorem spentNote_isDummy_bit {depth : ℕ} {s : SpentSlot depth} (h : SpentNoteSat s) :
    s.isDummy = 0 ∨ s.isDummy = 1 :=
  merkleProofOrDummy_bit h.membership

/-- A dummy slot also emits a nullifier, chosen by the prover: `nsk` and `rho` are
unconstrained in that branch. Stated explicitly as an obligation. -/
theorem dummy_nullifier_unconstrained {depth : ℕ} {s : SpentSlot depth}
    (h : SpentNoteSat s) : s.nullifier = nullifierOf (deriveNk s.nsk) s.rho s.cm := by
  rw [← h.nf_def, h.nk_def]

end Lelantos
