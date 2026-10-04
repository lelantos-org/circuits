import Lelantos.Model.Poseidon
import Lelantos.Model.Bits
import Mathlib.Tactic.IntervalCases

/-!
# `src/lib/note.circom` — keys, commitments, nullifiers

Transcription of the seven templates, plus the structural facts they provide:

* `packAV_inj` — packing `(asset_id, value)` into `asset_id · 2^64 + value` is injective
  once both fields are 64-bit range-checked, so `NoteCommitment` binds the asset and the
  value separately rather than only their combination.

* `noteCommitment_inj` — the commitment is taken in two steps,
  `inner = Poseidon(TAG_INNER, pk, rho, rcm)` and
  `cm = Poseidon(TAG_CM, asset_id · 2^64 + value, inner)`. The outer hash binds
  `(asset_id, value, inner)`, given the two range checks; `noteInner_inj` binds
  `(pk, rho, rcm)`; `noteCm_inj` composes them. The split is what lets a deposit publish
  `inner` beside its public `(asset, value)` and have `tree_update_batch.circom` build the
  leaf from the three (`Lelantos.batch_deposit_leaf`).

* `nullifier_binds_cm` — the commitment is part of the nullifier preimage, so two notes
  that share `(nk, rho)` get different nullifiers. This is the faerie-gold defence
  described at `src/lib/note.circom:121-128`; without `cm` in the preimage an attacker who
  produced a second note with a victim's `rho` could burn the victim's nullifier.

Domain separation is by the leading tag, not by the size of the packed field: every
same-arity pair of hash sites leads with a different constant
(`noteCommitment_ne_deriveRho`, `noteInner_ne_nullifier`), and different arities are
different preimage lengths (`noteCommitment_ne_merkleNode`).

The tree leaf is `cm` itself. There is no leaf hash.
-/

namespace Lelantos

/-- `DeriveIvk` — `src/lib/note.circom:19-29`. -/
def deriveIvk (nsk : F) : F := poseidon [TAG_IVK, nsk]

/-- `DeriveNk` — `src/lib/note.circom:31-40`. -/
def deriveNk (nsk : F) : F := poseidon [TAG_NK, nsk]

/-- `DerivePk` — `src/lib/note.circom:42-51`. -/
def derivePk (ivk : F) : F := poseidon [TAG_PK, ivk]

/-- The full spend-key chain `nsk → ivk → pk`. -/
def pkOfNsk (nsk : F) : F := derivePk (deriveIvk nsk)

/-- `NoteInner` — `src/lib/note.circom:62-75`. The half of a note that stays private on
every path: the owner key, `rho` and the hiding randomness. -/
def noteInner (pk rho rcm : F) : F := poseidon [TAG_INNER, pk, rho, rcm]

/-- `packed_av <== asset_id * POW_2_64() + value` — `src/lib/note.circom:93`. -/
def packAV (assetId value : F) : F := assetId * POW_2_64 + value

/-- `NoteCommitment` — `src/lib/note.circom:86-101`: `Poseidon(TAG_CM, packed_av, inner)`.
The third argument is an `inner`, whoever computed it: `SpentNote` and `OutputNote` pass
`noteInner pk rho rcm`, `TreeUpdateBatch` passes the word a depositor published. -/
def noteCommitment (assetId value inner : F) : F :=
  poseidon [TAG_CM, packAV assetId value, inner]

/-- The commitment of a whole note: `NoteInner` then `NoteCommitment`, as the two slot
templates wire them, at `src/lib/spent.circom:54-62` on the input side and at
`src/lib/output.circom:36-45` on the output side. -/
def noteCm (assetId value pk rho rcm : F) : F :=
  noteCommitment assetId value (noteInner pk rho rcm)

/-- `DeriveRho` — `src/lib/note.circom:108-119`. -/
def deriveRho (nf0 index : F) : F := poseidon [TAG_RHO, nf0, index]

/-- `Nullifier` — `src/lib/note.circom:133-146`. -/
def nullifierOf (nk rho cm : F) : F := poseidon [TAG_NF, nk, rho, cm]

/-- The node hash of `MerkleLevel4`, `Poseidon(TAG_MERKLE, c0, c1, c2, c3)` —
`src/lib/merkle.circom:66-74`. -/
def merkleNode (c : ℕ → F) : F := poseidon [TAG_MERKLE, c 0, c 1, c 2, c 3]

/-- `Poseidon` reads four children, so agreement on those four suffices. -/
theorem merkleNode_congr {a b : ℕ → F} (h : ∀ c, c < 4 → a c = b c) :
    merkleNode a = merkleNode b := by
  simp only [merkleNode, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num),
    h 3 (by norm_num)]

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

/-- On range-checked inputs the packed field element is `asset·2^64 + value` as an
integer. -/
theorem packAV_val {x y : F} (hx : x.val < 2 ^ 64) (hy : y.val < 2 ^ 64) :
    (packAV x y).val = x.val * 2 ^ 64 + y.val := by
  rw [packAV_cast, ZMod.val_natCast_of_lt (packAV_bound hx hy)]

/-- Packing is injective on 64-bit-range-checked inputs, since `2^128 < p`. This is the
precondition stated at `src/lib/note.circom:79-82`. -/
theorem packAV_inj {a v a' v' : F}
    (ha : a.val < 2 ^ 64) (hv : v.val < 2 ^ 64)
    (ha' : a'.val < 2 ^ 64) (hv' : v'.val < 2 ^ 64)
    (h : packAV a v = packAV a' v') : a = a' ∧ v = v' := by
  have hnat : a.val * 2 ^ 64 + v.val = a'.val * 2 ^ 64 + v'.val := by
    rw [← packAV_val ha hv, ← packAV_val ha' hv', h]
  refine ⟨val_inj ?_, val_inj ?_⟩ <;> omega

/-- **Faerie-gold resistance.** Equal nullifiers force equal `(nk, rho, cm)`; in
particular the commitment is pinned, so a second note sharing `(nk, rho)` cannot collide
with the victim's nullifier.

Conditional on `hcr`, which is unsatisfiable (`poseidon_collision`); this is an assumption
recorded in the statement, not a proved property. -/
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

/-- `inner` binds the owner key, `rho` and the hiding randomness. -/
theorem noteInner_inj (hcr : ¬ PoseidonCollision) {pk rho rcm pk' rho' rcm' : F}
    (h : noteInner pk rho rcm = noteInner pk' rho' rcm') :
    pk = pk' ∧ rho = rho' ∧ rcm = rcm' := by
  have h' := poseidon_inj hcr h
  simp only [List.cons.injEq, and_true] at h'
  exact ⟨h'.2.1, h'.2.2.1, h'.2.2.2⟩

/-- **The note commitment binds `(asset_id, value, inner)`.** Given the two 64-bit range
checks every caller applies — `SpentNote`, `OutputNote`, and `TreeUpdateBatch` on a deposit
leaf — a commitment cannot be reopened to a different asset, a different value or a
different `inner`.

Without `packAV_inj` this would only bind the packed pair, and a prover could trade
asset id against value inside one field element. Both range checks are needed: dropping
either one makes the packing non-injective. -/
theorem noteCommitment_inj (hcr : ¬ PoseidonCollision) {a v inner a' v' inner' : F}
    (ha : a.val < 2 ^ 64) (hv : v.val < 2 ^ 64)
    (ha' : a'.val < 2 ^ 64) (hv' : v'.val < 2 ^ 64)
    (h : noteCommitment a v inner = noteCommitment a' v' inner') :
    a = a' ∧ v = v' ∧ inner = inner' := by
  have h' := poseidon_inj hcr h
  simp only [List.cons.injEq, and_true] at h'
  obtain ⟨_, hpack, hinner⟩ := h'
  obtain ⟨hA, hV⟩ := packAV_inj ha hv ha' hv' hpack
  exact ⟨hA, hV, hinner⟩

/-- **The commitment of a whole note binds every field of it**: `noteCommitment_inj`
through the outer hash, then `noteInner_inj` through the inner one. -/
theorem noteCm_inj (hcr : ¬ PoseidonCollision) {a v pk rho rcm a' v' pk' rho' rcm' : F}
    (ha : a.val < 2 ^ 64) (hv : v.val < 2 ^ 64)
    (ha' : a'.val < 2 ^ 64) (hv' : v'.val < 2 ^ 64)
    (h : noteCm a v pk rho rcm = noteCm a' v' pk' rho' rcm') :
    a = a' ∧ v = v' ∧ pk = pk' ∧ rho = rho' ∧ rcm = rcm' := by
  obtain ⟨hA, hV, hinner⟩ := noteCommitment_inj hcr ha hv ha' hv' h
  obtain ⟨hpk, hrho, hrcm⟩ := noteInner_inj hcr hinner
  exact ⟨hA, hV, hpk, hrho, hrcm⟩

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

/-! ## Domain separation

Same arity, different leading tag; or different arity. -/

/-- **A note commitment is never an output `rho`.** `NoteCommitment` and `DeriveRho` are the
only two arity-3 sites, and they lead with different tags:
`TAG_CM` at `src/lib/note.circom:96` and `TAG_RHO` at `src/lib/note.circom:114`. -/
theorem noteCommitment_ne_deriveRho (hcr : ¬ PoseidonCollision) (a v inner nf0 index : F) :
    noteCommitment a v inner ≠ deriveRho nf0 index := by
  intro h
  have h' := poseidon_inj hcr h
  simp only [List.cons.injEq, and_true] at h'
  have hne : (TAG_CM : F) ≠ TAG_RHO := by
    simpa [TAG_CM, TAG_RHO] using tag_ne (m := 1) (n := 11) (by norm_num) (by norm_num)
      (by norm_num)
  exact hne h'.1

/-- **An `inner` is never a nullifier.** `NoteInner` and `Nullifier` are the two arity-4
sites, leading with `TAG_INNER` and `TAG_NF`. -/
theorem noteInner_ne_nullifier (hcr : ¬ PoseidonCollision) (pk rho rcm nk rho' cm : F) :
    noteInner pk rho rcm ≠ nullifierOf nk rho' cm := by
  intro h
  have h' := poseidon_inj hcr h
  simp only [List.cons.injEq, and_true] at h'
  have hne : (TAG_INNER : F) ≠ TAG_NF := by
    simpa [TAG_INNER, TAG_NF] using tag_ne (m := 14) (n := 2) (by norm_num) (by norm_num)
      (by norm_num)
  exact hne h'.1

/-- A note commitment is never a Merkle node: the preimages have different arities
(3 vs 5), and circom instantiates `Poseidon(3)` and `Poseidon(5)` as different
permutations. Since the leaf is `cm`, this is what stops a prover presenting an internal
node as a leaf. -/
theorem noteCommitment_ne_merkleNode (hcr : ¬ PoseidonCollision) (a v inner : F)
    (c : ℕ → F) : noteCommitment a v inner ≠ merkleNode c := by
  intro h
  have h' := poseidon_inj hcr h
  simp at h'

end Lelantos
