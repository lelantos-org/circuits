import Lelantos.Gadgets.ValueCommit
import Lelantos.Gadgets.Note

/-!
# `src/lib/output.circom` — one output-note slot

Simpler than `SpentNote`: no Merkle proof, no key chain, no dummy branch. `pk` is the
recipient's key and is deliberately unconstrained — the circuit proves nothing about who
can later spend the note, by design — `src/README.md § 1, "Out of scope (v1)"` puts spend
authorization out of scope for v1.

Two things it does prove, and both matter:

* `asset_id ≠ 0` **unconditionally** (unlike `SpentNote`, where the check is gated on
  `1 - is_dummy`), which keeps `packed_av ≥ 2^64` and so keeps the `cm` preimage
  domain-separated from tag-prefixed hashes.

* `cv` and `cv_dep` are built from the *same* range-checked bit array and the *same*
  generator — structurally so, since both come out of one `ValueCommitPair`
  (`src/lib/output.circom:59-66`) — so they cannot open to different
  `(asset, value)` pairs. That is `outputNote_cvDep_binds` — the 2x2 half of deposit
  binding. The value-inflation defences C-1' and C-1'' live in
  `tree_update_batch.circom` and are **not** covered by this development.
-/

namespace Lelantos

/-- Every signal of one `OutputNote()` instance. -/
structure OutputSlot where
  assetId : F
  value : F
  pk : F
  rho : F
  rcm : F
  rcv : F
  rcvDep : F
  /-- Binding inputs supplied by the caller. -/
  cm : F
  cv : Pt
  /-- Exported. -/
  cvDep : Pt
  rH : Pt
  /-- Intermediates. -/
  valueBits : ℕ → F
  assetBits : ℕ → F
  rcvBits : ℕ → F
  rcvDepBits : ℕ → F
  gen : Pt
  vT : Pt
  vTDep : Pt
  rHDep : Pt
  assetInv : F
  assetIsZero : F

/-- The constraint system of `OutputNote()`, in source order. Named fields for the same
reason as `SpentNoteSat`: the fidelity table is checked against them row by row. -/
structure OutputNoteSat (o : OutputSlot) : Prop where
  /-- `src/lib/output.circom:36-42` — `cm` binds the note. -/
  cm_def : noteCommitment o.assetId o.value o.pk o.rho o.rcm = o.cm
  /-- `:45-46` — value range. -/
  value_range : RangeCheck64Sat o.value o.valueBits
  /-- `:49-50` — `IsZero(asset_id)`. -/
  asset_isZero : IsZeroSat o.assetId o.assetInv o.assetIsZero
  /-- `:51` — unconditional non-zero asset id, unlike `SpentNote`'s gated check. -/
  asset_nonzero : o.assetIsZero = 0
  /-- `:56-57` — `HashToAssetGen`, which also enforces `asset_id < 2^64`. -/
  asset_bits : Num2BitsSat 64 o.assetId o.assetBits
  /-- `:56-57` — …and its output point. -/
  gen_def : o.gen = coords (assetGen o.assetId)
  /-- `:59-66, 68-69` — value commitment (`ValueCommitPair.cv`, bound to the `cv` input). -/
  cv_sat : ValueCommitSat o.valueBits o.gen o.rcv o.rcvBits o.vT o.rH o.cv
  /-- `:59-66, 74-75` — deposit value commitment (`ValueCommitPair.cv_dep`), sharing the
  same bits and generator structurally rather than by convention. -/
  cv_dep_sat : ValueCommitSat o.valueBits o.gen o.rcvDep o.rcvDepBits o.vTDep o.rHDep o.cvDep

/-- What an output slot establishes. -/
structure OutputWellFormed (o : OutputSlot) : Prop where
  assetNonzero : o.assetId ≠ 0
  valueRange : o.value.val < 2 ^ 64
  assetRange : o.assetId.val < 2 ^ 64
  commitment : noteCommitment o.assetId o.value o.pk o.rho o.rcm = o.cm
  /-- `cv` and `cv_dep` share the value·generator term, so they open to the same
  `(asset, value)`. -/
  cvDepBinds : o.vT = o.vTDep
  /-- **`cv` opens to this note's own value under this note's own asset generator.**
  Not "some 64-bit number times some point": the scalar is `value`, the range-checked
  signal that `cm` also binds. -/
  cvOpens : o.cv = coords ((o.value.val : ZMod ell) • assetGen o.assetId
    + blindScalar o.rcvBits • H)
  /-- …and so does `cv_dep`, with its own blinding factor and nothing else different. -/
  cvDepOpens : o.cvDep = coords ((o.value.val : ZMod ell) • assetGen o.assetId
    + blindScalar o.rcvDepBits • H)

theorem outputNote_sound {o : OutputSlot} (h : OutputNoteSat o) : OutputWellFormed o := by
  have hvc := h.cv_sat
  have hvcd := h.cv_dep_sat
  rw [h.gen_def] at hvc hvcd
  have hnz : o.assetId ≠ 0 := by
    intro hzero
    have hz := h.asset_nonzero
    rw [isZero_sound h.asset_isZero, if_pos hzero] at hz
    exact one_ne_zero hz
  exact
    { assetNonzero := hnz
      valueRange := rangeCheck64_sound h.value_range
      assetRange := (num2Bits_sound (le_of_lt two_pow_64_lt_p) h.asset_bits).2
      commitment := h.cm_def
      cvDepBinds := by rw [hvc.1, hvcd.1]
      cvOpens := valueCommit_opens h.value_range hvc
      cvDepOpens := valueCommit_opens h.value_range hvcd }

/-- **Deposit binding, 2x2 half.** The exported `cv_dep` carries the same
`value · V^asset` term as `cv`, so an output cannot advertise one value on-chain and
deposit another. -/
theorem outputNote_cvDep_binds {o : OutputSlot} (h : OutputNoteSat o) :
    o.vT = o.vTDep := (outputNote_sound h).cvDepBinds

/-- **Deposit binding, stated where it can be read.** `cv` and `cv_dep` open to the *same*
`(asset_id, value)` — the note's own — differing only in the blinding factor.

`outputNote_cvDep_binds` alone is weaker than it looks: `vT = vTDep` is an equation between
two scalar-multiplication intermediates, which holds because the model feeds both gadgets
the same bit array. This version names the value being committed, so the statement is about
the note rather than about the wiring. -/
theorem outputNote_cvDep_same_value {o : OutputSlot} (h : OutputNoteSat o) :
    ∃ r r' : ZMod ell,
      o.cv = coords ((o.value.val : ZMod ell) • assetGen o.assetId + r • H) ∧
      o.cvDep = coords ((o.value.val : ZMod ell) • assetGen o.assetId + r' • H) :=
  ⟨blindScalar o.rcvBits, blindScalar o.rcvDepBits,
    (outputNote_sound h).cvOpens, (outputNote_sound h).cvDepOpens⟩

end Lelantos
