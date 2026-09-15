import Lelantos.Model.Jubjub
import Lelantos.Gadgets.Balance

/-!
# `src/lib/value_commit.circom`

`ValueCommit` produces `cv = value · V^asset ⊕ rcv · H` and exports `rH = rcv · H`
separately, so that `PerAssetPointBalance` can sum the blinding terms on the opposite side
of its equation and avoid a field wrap in `Σrcv_in − Σrcv_out`.

`valueCommit_opens` is the result the note modules consume: `cv` opens to the note's own
range-checked `value` under its own asset generator.

Modelling points:

* `ValueCommit` takes pre-decomposed bits and imposes no range check of its own
  (`src/lib/value_commit.circom:127-132`). `value < 2^64` holds because the caller
  applies `RangeCheck64`, and `SpentNote` / `OutputNote` feed the same bit array to both
  `cv` and `cv_dep`, which forces the two commitments to open to the same value.

* The circuit builds each note's `(cv, cv_dep)` with a single `ValueCommitPair`
  (`src/lib/value_commit.circom:76-117`) rather than two `ValueCommit` instances: the
  shared `value · gen` term is computed once and each blinder is added separately. The
  model uses two independent `ValueCommitSat` instances per slot, which is the same
  constraint set; `ValueCommitPair` removes a duplicated `EscalarMulAny(64)`, not a
  constraint. The structural sharing implies the model's assumption that both instances
  receive equal `bits` and `gen`, so the model is the weaker statement.

* `MulH` decomposes its scalar with `Num2Bits(252)`, which is alias-free since `2^252 < p`.
  `blindScalar_eq_val` discharges that bound, letting `valueCommit_opens` name the `rcv`
  signal rather than its bit array. The subgroup order is `ell ≈ 2^251`, so `rcv` is not
  uniquely recoverable from the point `rcv · H`; no theorem here claims that.
-/

namespace Lelantos

/-- `ValueScalarMul` (`src/lib/value_commit.circom:32-46`): `out = (Σ bᵢ 2^i) · gen`
via `EscalarMulAny(64)`. -/
def ValueScalarMulSat (bits : ℕ → F) (gen out : Pt) : Prop :=
  out = escalarMul (bitsNat bits 64) gen

/-- `MulH` — `src/lib/value_commit.circom:51-64`: `Num2Bits(252)` then `FixedBaseMul`. -/
structure MulHSat (scalar : F) (sbits : ℕ → F) (out : Pt) : Prop where
  /-- `:59-60` — the 252-bit decomposition of the blinding `scalar`. -/
  scalar_bits : Num2BitsSat 252 scalar sbits
  /-- `:59-63` — `FixedBaseMul(RCV_BITS(), H)`. -/
  out_def : out = escalarMul (bitsNat sbits 252) (coords H)

/-- `ValueCommit` — `src/lib/value_commit.circom:127-154`. Note slots instantiate the
two-blinder `ValueCommitPair` (`:78-123`) instead; the module note explains why two
independent `ValueCommitSat` instances are the same constraint set. -/
structure ValueCommitSat (bits : ℕ → F) (gen : Pt) (rcv : F) (sbits : ℕ → F)
    (vT rH cv : Pt) : Prop where
  /-- `:134-139` — `vT = value · gen`. -/
  value_term : ValueScalarMulSat bits gen vT
  /-- `:141-142, 152-153` — `rH = rcv · H`, and the `rH` output it is read from. -/
  blind_term : MulHSat rcv sbits rH
  /-- `:144-148` — `cv = BabyAdd(vT, rH)`. -/
  sum_def : cv = babyAdd vT rH

/-- The value a bit array commits to, as a subgroup scalar. -/
def valScalar (bits : ℕ → F) : ZMod ell := (bitsNat bits 64 : ℕ)

/-- The blinding scalar a 252-bit array commits to. -/
def blindScalar (sbits : ℕ → F) : ZMod ell := (bitsNat sbits 252 : ℕ)

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
consumes; this connects them to the `value` signal the note commitment binds, so that
`cv` is tied to the note rather than to an arbitrary 64-bit number. `2^64 < p` makes the
`Num2Bits(64)` decomposition alias-free, so the reading is unique. -/
theorem valScalar_eq_val {v : F} {bits : ℕ → F} (h : Num2BitsSat 64 v bits) :
    valScalar bits = (v.val : ZMod ell) := by
  unfold valScalar
  rw [(num2Bits_sound (le_of_lt two_pow_64_lt_p) h).1]

/-- **The bit array is the note's blinder.** The counterpart of `valScalar_eq_val` for
`rcv`: it connects the blinding term of `cv` to the `rcv` signal that `MulHSat` decomposes,
rather than to an opaque 252-bit array.

`2^252 < p` makes the reading unique: it is the hypothesis `num2Bits_sound` needs for
`Num2Bits(252)` to be alias-free, and `RCV_BITS` in
`src/lib/value_commit.circom` is chosen to satisfy it. -/
theorem blindScalar_eq_val {r : F} {sbits : ℕ → F} (h : Num2BitsSat 252 r sbits) :
    blindScalar sbits = (r.val : ZMod ell) := by
  unfold blindScalar
  rw [(num2Bits_sound (le_of_lt two_pow_252_lt_p) h).1]

/-- **`cv` opens to the note's own `(asset_id, value)`.** The commitment is
`value · V^asset + rcv · H`, with `value` the range-checked signal and `V^asset` the
generator for the note's asset id. -/
theorem valueCommit_opens {v rcv a : F} {bits sbits : ℕ → F} {vT rH cv : Pt}
    (hbits : Num2BitsSat 64 v bits)
    (h : ValueCommitSat bits (coords (assetGen a)) rcv sbits vT rH cv) :
    cv = coords ((v.val : ZMod ell) • assetGen a + (rcv.val : ZMod ell) • H) := by
  rw [(valueCommit_group h).1, valScalar_eq_val hbits,
    blindScalar_eq_val h.blind_term.scalar_bits]

end Lelantos
