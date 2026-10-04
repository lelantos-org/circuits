import Lelantos.Gadgets.Balance
import Lelantos.Gadgets.Note

/-!
# `src/lib/output.circom` — one output-note slot

Unlike `SpentNote`: no Merkle proof, no key chain, no dummy branch. `pk` is the recipient's
key and is unconstrained; the circuit proves nothing about who can later spend the note
(`src/README.md § 1, "Out of scope"` excludes spend authorization for v1).

It proves:

* `value` and `asset_id` are 64-bit, which `NoteCommitment`'s packing needs;
* `asset_id ≠ 0` unconditionally (in `SpentNote` the check is gated on `1 - is_dummy`):
  id 0 means "no asset";
* the public `cm` is the commitment of the slot's own five note fields.

`cm` is the leaf `tree_update_batch.circom` inserts for this slot. There is no value
commitment: the only thing an output publishes is `cm`, and what hides `(asset, value)`
inside it is `rcm` alone, since an output's `rho` is publicly derivable.
-/

namespace Lelantos

/-- Every signal of one `OutputNote()` instance. -/
structure OutputSlot where
  assetId : F
  value : F
  pk : F
  rho : F
  rcm : F
  /-- Binding input supplied by the caller. -/
  cm : F
  /-- Intermediates. -/
  inner : F
  valueBits : ℕ → F
  assetBits : ℕ → F
  assetInv : F
  assetIsZero : F

/-- The constraint system of `OutputNote()`, in source order. Fields are named, as in
`SpentNoteSat`, so the fidelity table can be checked against them row by row. -/
structure OutputNoteSat (o : OutputSlot) : Prop where
  /-- `src/lib/output.circom:24-25` — `rng_value`: the value is 64-bit. -/
  value_range : RangeCheck64Sat o.value o.valueBits
  /-- `:27-28` — `rng_asset`: the asset id is 64-bit. -/
  asset_range : RangeCheck64Sat o.assetId o.assetBits
  /-- `:31-32` — `IsZero(asset_id)`. -/
  asset_isZero : IsZeroSat o.assetId o.assetInv o.assetIsZero
  /-- `:33` — unconditional non-zero asset id, unlike `SpentNote`'s gated check. -/
  asset_nonzero : o.assetIsZero = 0
  /-- `:36-39` — `inner = NoteInner(pk, rho, rcm)`. -/
  inner_def : o.inner = noteInner o.pk o.rho o.rcm
  /-- `:41-45` — `cm_h = NoteCommitment(asset_id, value, inner)`, bound to the `cm` input. -/
  cm_def : noteCommitment o.assetId o.value o.inner = o.cm

/-- What an output slot establishes. -/
structure OutputWellFormed (o : OutputSlot) : Prop where
  assetNonzero : o.assetId ≠ 0
  valueRange : o.value.val < 2 ^ 64
  assetRange : o.assetId.val < 2 ^ 64
  /-- The published commitment is the commitment of this slot's own note. -/
  commitment : noteCm o.assetId o.value o.pk o.rho o.rcm = o.cm

theorem outputNote_sound {o : OutputSlot} (h : OutputNoteSat o) : OutputWellFormed o := by
  have hnz : o.assetId ≠ 0 := by
    intro hzero
    have hz := h.asset_nonzero
    rw [isZero_sound h.asset_isZero, if_pos hzero] at hz
    exact one_ne_zero hz
  exact
    { assetNonzero := hnz
      valueRange := rangeCheck64_sound h.value_range
      assetRange := rangeCheck64_sound h.asset_range
      commitment := by rw [noteCm, ← h.inner_def]; exact h.cm_def }

end Lelantos
