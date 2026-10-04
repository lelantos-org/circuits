import Lelantos.Gadgets.Merkle
import Lelantos.Gadgets.Balance

/-!
# `src/lib/spent.circom` — one spent-note slot

`SpentNote(DEPTH)` opens a note against the commitment tree and emits its nullifier. The
model carries every signal circom declares, including the intermediates, so that the
fidelity harness can compare them against a real witness.

The tree leaf is the note commitment `cm`. `tree_update_batch.circom` inserts a spend's
`out_cm` as it stands and builds a deposit's leaf from its public `(asset, value)` by the
same `NoteCommitment`, so opening `cm` here pins the note to the `(asset, value)` it was
inserted with (`Lelantos.batch_deposit_spend_binds`).

`spentNote_sound` gives what a non-dummy slot proves: ownership (the prover knows `nsk` and
the diversifier `d` that `pk` derives from), a non-zero asset id, membership of `cm` under
the root, and a correctly formed nullifier. When `is_dummy = 1` the Merkle path is
unconstrained, `asset_id` may be zero, and the slot still emits a prover-chosen `nullifier`.

On every slot, dummy or not, `pk` is the key `nsk` derives at `d` (`spentNote_owns`): it is
not an input of the template. `value` and `asset_id` are 64-bit (`spentNote_valueRange`,
`spentNote_assetRange`), `cm` is the commitment of the slot's own fields, and the nullifier
is derived from it. The asset bound is unconditional because the packing inside
`NoteCommitment` is injective only under both bounds.

`DummyZeroValue` (applied by the caller, `src/lib/transact.circom:68`) makes the dummy
branch safe by forcing `value = 0`, so the slot is neutral for value conservation. The
prover-chosen nullifier is an obligation on the contract's double-spend set; see
`dummy_nullifier_unconstrained`.
-/

namespace Lelantos

/-- Every signal of one `SpentNote(depth)` instance, inputs and intermediates alike. -/
structure SpentSlot (depth : ℕ) where
  -- Note fields.
  assetId : F
  value : F
  rho : F
  rcm : F
  nsk : F
  d : F
  isDummy : F
  -- Binding inputs supplied by the caller.
  root : F
  nullifier : F
  -- Key-chain and hash intermediates. `pk` is the output of `owner_pk`, not an input.
  ivk : F
  pk : F
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

/-- The constraint system of `SpentNote(depth)`, in source order: one named field per circom
constraint, each citing its source line. `FIDELITY.md`'s constraint table is checked
against this definition row by row. -/
structure SpentNoteSat {depth : ℕ} (s : SpentSlot depth) : Prop where
  /-- `src/lib/spent.circom:44-45` — `ivk = Poseidon(TAG_IVK, nsk)`. -/
  ivk_def : s.ivk = deriveIvk s.nsk
  /-- `:47-49` — `owner_pk.pk = Poseidon(TAG_PK, ivk, d)`, on every slot. -/
  pk_def : s.pk = derivePk s.ivk s.d
  /-- `:53-54` — `rng_value`: the value is 64-bit, on every slot. -/
  value_range : RangeCheck64Sat s.value s.valueBits
  /-- `:56-57` — `rng_asset`: the asset id is 64-bit, on every slot, dummies included. -/
  asset_range : RangeCheck64Sat s.assetId s.assetBits
  /-- `:60-63` — `inner = NoteInner(owner_pk.pk, rho, rcm)`, over the derived pk. -/
  inner_def : s.inner = noteInner s.pk s.rho s.rcm
  /-- `:65-68` — `cm = NoteCommitment(asset_id, value, inner)`. -/
  cm_def : s.cm = noteCommitment s.assetId s.value s.inner
  /-- `:71-80` — membership of `cm`, which is the leaf; bypassed for dummies. -/
  membership : MerkleProofOrDummySat depth s.cm s.pathElements s.pathIndices s.root
    s.isDummy s.mpDiff s.mpComputed s.mpB s.mpS s.mpC s.mpChain
  /-- `:84-85` — `nk = Poseidon(TAG_NK, nsk)`. -/
  nk_def : s.nk = deriveNk s.nsk
  /-- `:87-91` — nullifier. -/
  nf_def : nullifierOf s.nk s.rho s.cm = s.nullifier
  /-- `:95-96` — `IsZero(asset_id)`. -/
  asset_isZero : IsZeroSat s.assetId s.assetInv s.assetIsZero
  /-- `:97` — real notes have a non-zero asset id. Id 0 means "no asset". -/
  asset_nonzero_real : (1 - s.isDummy) * s.assetIsZero = 0

/-- What a non-dummy spent slot establishes. -/
structure SpentReal {depth : ℕ} (s : SpentSlot depth) : Prop where
  /-- The prover knows the spend key: `pk` is the image of `nsk` under the key chain, at
  the slot's diversifier. -/
  owns : s.pk = pkOfNsk s.nsk s.d
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
  /-- Every path index is a valid quaternary digit, a hypothesis of `merkleMember_inj`. -/
  pathValid : ∀ d, d < depth → (s.pathIndices d).val < 4

/-- Every spent slot range-checks its value, dummy or not. -/
theorem spentNote_valueRange {depth : ℕ} {s : SpentSlot depth} (h : SpentNoteSat s) :
    s.value.val < 2 ^ 64 :=
  rangeCheck64_sound h.value_range

/-- Every spent slot range-checks its asset id, dummy or not. -/
theorem spentNote_assetRange {depth : ℕ} {s : SpentSlot depth} (h : SpentNoteSat s) :
    s.assetId.val < 2 ^ 64 :=
  rangeCheck64_sound h.asset_range

/-- Every spent slot's `pk` is the key its `nsk` derives at its diversifier, dummy or not. -/
theorem spentNote_owns {depth : ℕ} {s : SpentSlot depth} (h : SpentNoteSat s) :
    s.pk = pkOfNsk s.nsk s.d := by
  rw [h.pk_def, h.ivk_def]
  rfl

/-- Every spent slot's `cm` is the commitment of its own five note fields, dummy or not. -/
theorem spentNote_commitment {depth : ℕ} {s : SpentSlot depth} (h : SpentNoteSat s) :
    s.cm = noteCm s.assetId s.value s.pk s.rho s.rcm := by
  rw [h.cm_def, h.inner_def, noteCm]

/-- Soundness of `SpentNote` on a real slot. -/
theorem spentNote_sound {depth : ℕ} {s : SpentSlot depth}
    (h : SpentNoteSat s) (hreal : s.isDummy = 0) : SpentReal s := by
  have hassetNz : s.assetId ≠ 0 := by
    have hnz := h.asset_nonzero_real
    rw [hreal, sub_zero, one_mul] at hnz
    rw [isZero_sound h.asset_isZero] at hnz
    intro hz
    rw [if_pos hz] at hnz
    exact one_ne_zero hnz
  exact
    { owns := spentNote_owns h
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

/-- A dummy slot also emits a nullifier, chosen by the prover: `nsk`, `d`, `rho` and `rcm`
are unconstrained in that branch. -/
theorem dummy_nullifier_unconstrained {depth : ℕ} {s : SpentSlot depth}
    (h : SpentNoteSat s) : s.nullifier = nullifierOf (deriveNk s.nsk) s.rho s.cm := by
  rw [← h.nf_def, h.nk_def]

end Lelantos
