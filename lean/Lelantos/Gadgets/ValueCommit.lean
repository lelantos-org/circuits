import Lelantos.Model.Jubjub
import Lelantos.Gadgets.Balance

/-!
# `src/lib/value_commit.circom`

`ValueCommit` produces `cv = value · V^asset ⊕ rcv · H` and exports `rH = rcv · H`
separately, so that `PerAssetPointBalance` can sum the blinding terms on the opposite side
of its equation and avoid a field wrap in `Σrcv_in − Σrcv_out`.

`valueCommit_opens` is the result the note modules consume: `cv` opens to the note's own
range-checked `value` under its own asset generator.

Two modelling points:

* `ValueCommit` takes pre-decomposed bits and imposes no range check of its own
  (`src/lib/value_commit.circom:126-128`). `value < 2^64` holds only because the caller
  applies `RangeCheck64`, and `SpentNote` / `OutputNote` feed the *same* bit array to both
  `cv` and `cv_dep`, which is what forces the two commitments to open to the same value.

* The circuit builds each note's `(cv, cv_dep)` with a single `ValueCommitPair`
  (`src/lib/value_commit.circom:77-124`) rather than two `ValueCommit` instances: the
  shared `value · gen` term is computed once and each blinder added separately. This
  model keeps two independent `ValueCommitSat` instances per slot, which is the same
  constraint set — `ValueCommitPair` removes a *duplicated* `EscalarMulAny(64)`, not a
  constraint. Sharing the term structurally is strictly stronger than the model's
  assumption that the two instances receive equal `bits` and `gen`, so the model stays
  on the safe (weaker) side.

* `MulH` decomposes its scalar with `Num2Bits(253)`. Since `2^253 < p` that decomposition
  is alias-free, but the subgroup order is `ell ≈ 2^251`, so `rcv` is not uniquely
  recoverable from `rcv · H`. That affects extraction of the blinding factor only, and no
  theorem here claims it.
-/

namespace Lelantos

/-- `ValueScalarMul` (`src/lib/value_commit.circom:24`): `out = (Σ bᵢ 2^i) · gen`
via `EscalarMulAny(64)`. -/
def ValueScalarMulSat (bits : ℕ → F) (gen out : Pt) : Prop :=
  out = escalarMul (bitsNat bits 64) gen

/-- `MulH` — `src/lib/value_commit.circom:41-58`: `Num2Bits(253)` then `EscalarMulFix`. -/
structure MulHSat (scalar : F) (sbits : ℕ → F) (out : Pt) : Prop where
  /-- `:49-50` — the 253-bit decomposition of the blinding scalar. -/
  scalar_bits : Num2BitsSat 253 scalar sbits
  /-- `:52-57` — `EscalarMulFix(253, H)`. -/
  out_def : out = escalarMul (bitsNat sbits 253) (coords H)

/-- `ValueCommit` — `src/lib/value_commit.circom:126-153`. Note slots instantiate the
two-blinder `ValueCommitPair` (`:77-124`) instead; see the module note for why modelling
that as two independent `ValueCommitSat` is the same constraint set. -/
structure ValueCommitSat (bits : ℕ → F) (gen : Pt) (rcv : F) (sbits : ℕ → F)
    (vT rH cv : Pt) : Prop where
  /-- `:133-138` — `vT = value · gen`. -/
  value_term : ValueScalarMulSat bits gen vT
  /-- `:140-141, 151-152` — `rH = rcv · H`, and the `rH` output it is read from. -/
  blind_term : MulHSat rcv sbits rH
  /-- `:143-150` — `cv = BabyAdd(vT, rH)`. -/
  sum_def : cv = babyAdd vT rH

/-- The value a bit array commits to, as a subgroup scalar. -/
def valScalar (bits : ℕ → F) : ZMod ell := (bitsNat bits 64 : ℕ)

/-- The blinding scalar a 253-bit array commits to. -/
def blindScalar (sbits : ℕ → F) : ZMod ell := (bitsNat sbits 253 : ℕ)

/-- **Soundness of `ValueCommit`.** A satisfying assignment opens to
`value · gen + rcv · H` in the subgroup. -/
theorem valueCommit_group {bits sbits : ℕ → F} {rcv : F} {g : G} {vT rH cv : Pt}
    (h : ValueCommitSat bits (coords g) rcv sbits vT rH cv) :
    cv = coords (valScalar bits • g + blindScalar sbits • H) ∧ rH = coords (blindScalar sbits • H) := by
  have hvT := h.value_term
  have hrH := h.blind_term.out_def
  refine ⟨?_, ?_⟩
  · rw [h.sum_def, hvT, hrH, escalarMul_spec, escalarMul_spec, babyAdd_spec]
    rfl
  · rw [hrH, escalarMul_spec]
    rfl

/-- **The bit array is the note's value.** `valScalar` reads the bits `ValueScalarMul`
consumes; this is what connects them to the `value` *signal* the note commitment binds.

Without it `valueCommit_group` talks about an opaque bit array and nothing ties `cv` to the
note at all — the gadget could be committing to any 64-bit number. `2^64 < p` makes the
`Num2Bits(64)` decomposition alias-free, which is exactly what makes the reading unique. -/
theorem valScalar_eq_val {v : F} {bits : ℕ → F} (h : Num2BitsSat 64 v bits) :
    valScalar bits = (v.val : ZMod ell) := by
  unfold valScalar
  rw [(num2Bits_sound (le_of_lt two_pow_64_lt_p) h).1]

/-- **`cv` opens to the note's own `(asset_id, value)`.** The full statement the gadget is
there to provide: the commitment is `value · V^asset + rcv · H`, with `value` the range-
checked signal and `V^asset` the generator for the note's asset id. -/
theorem valueCommit_opens {v rcv a : F} {bits sbits : ℕ → F} {vT rH cv : Pt}
    (hbits : Num2BitsSat 64 v bits)
    (h : ValueCommitSat bits (coords (assetGen a)) rcv sbits vT rH cv) :
    cv = coords ((v.val : ZMod ell) • assetGen a + blindScalar sbits • H) := by
  rw [(valueCommit_group h).1, valScalar_eq_val hbits]

end Lelantos
