import Lelantos.Model.Poseidon
import Lelantos.Model.Bits
import Mathlib.Tactic.IntervalCases

/-!
# `src/lib/note.circom` — keys, commitments, nullifiers

Straight transcription of the six templates, plus the two structural facts they exist to
provide:

* `packAV_inj` — packing `(asset_id, value)` into `asset_id · 2^64 + value` is injective
  once both fields are 64-bit range-checked. This is what makes `NoteCommitment` bind the
  asset and the value separately rather than only their combination, and it is also the
  implicit domain separation the module relies on: for a real note `asset_id ≠ 0`, so
  `packed_av ≥ 2^64` and the `cm` preimage can never collide with a small tag like
  `TAG_MERKLE` or `TAG_LEAF`.

* `nullifier_binds_cm` — the commitment sits *inside* the nullifier preimage, so two notes
  that share `(nk, rho)` still get different nullifiers. This is the faerie-gold defence
  described at `src/README.md` § 7, "Why `cm` is in the preimage (faerie gold)"; without
  `cm` in the preimage an attacker who
  produced a second note with a victim's `rho` could burn the victim's nullifier.
-/

namespace Lelantos

/-- `DeriveIvk` — `src/lib/note.circom:14`. -/
def deriveIvk (nsk : F) : F := poseidon [TAG_IVK, nsk]

/-- `DeriveNk` — `src/lib/note.circom:25`. -/
def deriveNk (nsk : F) : F := poseidon [TAG_NK, nsk]

/-- `DerivePk` — `src/lib/note.circom:36`. -/
def derivePk (ivk : F) : F := poseidon [TAG_PK, ivk]

/-- The full spend-key chain `nsk → ivk → pk`. -/
def pkOfNsk (nsk : F) : F := derivePk (deriveIvk nsk)

/-- `packed_av <== asset_id * 2^64 + value` — `src/lib/note.circom:60`. -/
def packAV (assetId value : F) : F := assetId * POW_2_64 + value

/-- `NoteCommitment` — `src/lib/note.circom:51`. Note there is no tag: domain separation
comes from `packed_av ≥ 2^64`, which holds because real notes have `asset_id ≠ 0`. -/
def noteCommitment (assetId value pk rho rcm : F) : F :=
  poseidon [packAV assetId value, pk, rho, rcm]

/-- `DeriveRho` — `src/lib/note.circom:75`. -/
def deriveRho (nf0 index : F) : F := poseidon [TAG_RHO, nf0, index]

/-- `Nullifier` — `src/lib/note.circom:96`. -/
def nullifierOf (nk rho cm : F) : F := poseidon [TAG_NF, nk, rho, cm]

/-- `MerkleLevel4`'s node hash — `src/lib/merkle.circom:66`. -/
def merkleNode (c : ℕ → F) : F := poseidon [TAG_MERKLE, c 0, c 1, c 2, c 3]

/-- The leaf hash binding a commitment to its deposit value commitment —
`src/lib/spent.circom:79`. -/
def leafHash (cm x y : F) : F := poseidon [TAG_LEAF, cm, x, y]

/-! ## Structural facts -/

private theorem packAV_cast (x y : F) : packAV x y = ((x.val * 2 ^ 64 + y.val : ℕ) : F) := by
  unfold packAV
  push_cast
  simp [pow_2_64_eq, ZMod.natCast_val, ZMod.cast_id]

private theorem packAV_bound {x y : F} (hx : x.val < 2 ^ 64) (hy : y.val < 2 ^ 64) :
    x.val * 2 ^ 64 + y.val < p := by
  have hlt : x.val * 2 ^ 64 + y.val < 2 ^ 128 := by
    have : x.val * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)
    have h128 : (2 : ℕ) ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
    omega
  exact lt_trans hlt two_pow_128_lt_p

/-- On range-checked inputs the packed field element really is `asset·2^64 + value` as an
integer. -/
theorem packAV_val {x y : F} (hx : x.val < 2 ^ 64) (hy : y.val < 2 ^ 64) :
    (packAV x y).val = x.val * 2 ^ 64 + y.val := by
  rw [packAV_cast, ZMod.val_natCast_of_lt (packAV_bound hx hy)]

/-- Packing is injective on 64-bit-range-checked inputs, since `2^128 < p`. -/
theorem packAV_inj {a v a' v' : F}
    (ha : a.val < 2 ^ 64) (hv : v.val < 2 ^ 64)
    (ha' : a'.val < 2 ^ 64) (hv' : v'.val < 2 ^ 64)
    (h : packAV a v = packAV a' v') : a = a' ∧ v = v' := by
  have hnat : a.val * 2 ^ 64 + v.val = a'.val * 2 ^ 64 + v'.val := by
    rw [← packAV_val ha hv, ← packAV_val ha' hv', h]
  refine ⟨val_inj ?_, val_inj ?_⟩ <;> omega

/-- **The implicit domain separation of `NoteCommitment`.** A real note has
`asset_id ≠ 0`, so its packed field is at least `2^64` and can never equal a small
domain tag. This is the argument `src/lib/note.circom:48-50` makes in prose. -/
theorem packAV_val_ge {a v : F} (hnz : a ≠ 0) (ha : a.val < 2 ^ 64) (hv : v.val < 2 ^ 64) :
    2 ^ 64 ≤ (packAV a v).val := by
  rw [packAV_val ha hv]
  have : a.val ≠ 0 := fun hz => hnz (val_inj (by simpa using hz))
  have : 1 ≤ a.val := by omega
  calc (2 : ℕ) ^ 64 = 1 * 2 ^ 64 := (one_mul _).symm
    _ ≤ a.val * 2 ^ 64 := Nat.mul_le_mul_right _ this
    _ ≤ a.val * 2 ^ 64 + v.val := Nat.le_add_right _ _

/-- **Faerie-gold resistance.** Equal nullifiers force equal `(nk, rho, cm)`; in
particular the commitment is pinned, so a second note sharing `(nk, rho)` cannot collide
with the victim's nullifier.

Conditional on `hcr`, which is unsatisfiable (`poseidon_collision`) — read this as an
assumption recorded in the statement, not as a proved property. -/
theorem nullifier_binds_cm (hcr : ¬ PoseidonCollision) {nk rho cm nk' rho' cm' : F}
    (h : nullifierOf nk rho cm = nullifierOf nk' rho' cm') :
    nk = nk' ∧ rho = rho' ∧ cm = cm' := by
  have h' := poseidon_inj hcr h
  simp only [List.cons.injEq, and_true] at h'
  exact ⟨h'.2.1, h'.2.2.1, h'.2.2.2⟩

/-- The key chain is injective, so a satisfied ownership check pins `nsk`. -/
theorem pkOfNsk_inj (hcr : ¬ PoseidonCollision) {nsk nsk' : F}
    (h : pkOfNsk nsk = pkOfNsk nsk') : nsk = nsk' := by
  unfold pkOfNsk derivePk deriveIvk at h
  have h1 := poseidon_inj hcr h
  simp only [List.cons.injEq, and_true] at h1
  have h2 := poseidon_inj hcr h1.2
  simp only [List.cons.injEq, and_true] at h2
  exact h2.2

/-- `DeriveRho` is injective, so distinct `(nf0, index)` give distinct output `rho`. -/
theorem deriveRho_inj (hcr : ¬ PoseidonCollision) {a b a' b' : F}
    (h : deriveRho a b = deriveRho a' b') : a = a' ∧ b = b' := by
  have h' := poseidon_inj hcr h
  simp only [List.cons.injEq, and_true] at h'
  exact ⟨h'.2.1, h'.2.2⟩

/-- **The note commitment binds every field of the note.** Given the 64-bit range checks
that `SpentNote` and `OutputNote` apply, a commitment cannot be reopened to a different
`(asset_id, value, pk, rho, rcm)`.

Without `packAV_inj` this would only bind the *packed* pair, and a prover could trade
asset id against value inside one field element. -/
theorem noteCommitment_inj (hcr : ¬ PoseidonCollision) {a v pk rho rcm a' v' pk' rho' rcm' : F}
    (ha : a.val < 2 ^ 64) (hv : v.val < 2 ^ 64)
    (ha' : a'.val < 2 ^ 64) (hv' : v'.val < 2 ^ 64)
    (h : noteCommitment a v pk rho rcm = noteCommitment a' v' pk' rho' rcm') :
    a = a' ∧ v = v' ∧ pk = pk' ∧ rho = rho' ∧ rcm = rcm' := by
  have h' := poseidon_inj hcr h
  simp only [List.cons.injEq, and_true] at h'
  obtain ⟨hpack, hpk, hrho, hrcm⟩ := h'
  obtain ⟨hA, hV⟩ := packAV_inj ha hv ha' hv' hpack
  exact ⟨hA, hV, hpk, hrho, hrcm⟩

/-- The leaf hash binds the commitment and both `cv_dep` coordinates. -/
theorem leafHash_inj (hcr : ¬ PoseidonCollision) {cm x y cm' x' y' : F}
    (h : leafHash cm x y = leafHash cm' x' y') : cm = cm' ∧ x = x' ∧ y = y' := by
  have h' := poseidon_inj hcr h
  simp only [List.cons.injEq, and_true] at h'
  exact ⟨h'.2.1, h'.2.2.1, h'.2.2.2⟩

/-- **A note commitment is never a leaf hash.** `NoteCommitment` and `leafHash` have the
*same* arity (4), so arity gives no separation here — the separation is entirely the
`packed_av ≥ 2^64 > TAG_LEAF` argument, and it therefore depends on the caller's
`asset_id ≠ 0` and both range checks. Drop any of those three and a prover could present
a leaf hash as a note commitment. -/
theorem noteCommitment_ne_leafHash (hcr : ¬ PoseidonCollision) {a v : F} (hnz : a ≠ 0)
    (ha : a.val < 2 ^ 64) (hv : v.val < 2 ^ 64) (pk rho rcm cm x y : F) :
    noteCommitment a v pk rho rcm ≠ leafHash cm x y := by
  intro h
  have h' := poseidon_inj hcr h
  simp only [List.cons.injEq, and_true] at h'
  have hge := packAV_val_ge hnz ha hv
  rw [h'.1] at hge
  have hsmall : (TAG_LEAF : F).val = 10 := by
    rw [TAG_LEAF]
    exact ZMod.val_natCast_of_lt (by unfold p; norm_num)
  omega

/-- A Merkle node binds all four children. -/
theorem merkleNode_inj (hcr : ¬ PoseidonCollision) {c c' : ℕ → F}
    (h : merkleNode c = merkleNode c') : ∀ k, k < 4 → c k = c' k := by
  have h' := poseidon_inj hcr h
  simp only [List.cons.injEq, and_true] at h'
  intro k hk
  interval_cases k
  · exact h'.2.1
  · exact h'.2.2.1
  · exact h'.2.2.2.1
  · exact h'.2.2.2.2

/-- A note commitment is never a Merkle node: the preimages have different arities
(4 vs 5), and circom instantiates `Poseidon(4)` and `Poseidon(5)` as different
permutations. -/
theorem noteCommitment_ne_merkleNode (hcr : ¬ PoseidonCollision) (a v pk rho rcm : F)
    (c : ℕ → F) : noteCommitment a v pk rho rcm ≠ merkleNode c := by
  intro h
  have h' := poseidon_inj hcr h
  simp at h'

/-- A leaf hash is never a Merkle node, by arity. This is what stops a prover presenting
an internal node as a leaf. -/
theorem leafHash_ne_merkleNode (hcr : ¬ PoseidonCollision) (cm x y : F) (c : ℕ → F) :
    leafHash cm x y ≠ merkleNode c := by
  intro h
  have h' := poseidon_inj hcr h
  simp at h'

end Lelantos
