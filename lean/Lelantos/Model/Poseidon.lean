import Lelantos.Model.Field

/-!
# Poseidon and the domain-separation tags

Poseidon is modelled as an opaque function `poseidon : List F → F`. Every circom call
`Poseidon(k)([a₁, …, a_k])` becomes `poseidon [a₁, …, a_k]`.

## Collision resistance is a hypothesis, not an axiom

`Function.Injective poseidon` is refutable: `List F` is infinite and `F` is finite, so no
injection exists (`poseidon_not_injective`). As an axiom it would make the development
inconsistent: `False` would yield `TxWellFormed w` for every `w` while still type-checking
and passing `#print axioms`.

A conclusion of the form `P ∨ PoseidonCollision` is equally uninformative, since
`PoseidonCollision` is provable (`poseidon_collision`) and discharges it by `Or.inr`; the same
holds for any statement that only asserts some collision exists. A non-trivial treatment
requires either concrete colliding preimages built from the prover's witness or a
concrete-security formulation with an explicit adversary and advantage bound. Neither is
modelled here.

Collision resistance instead appears as an explicit hypothesis `hcr : ¬ PoseidonCollision`
on the theorems that need it, and nowhere else. The hypothesis is unsatisfiable, so those
theorems are vacuous read literally, but the vacuity is local and visible in the statement:
the environment stays consistent, no other theorem is weakened, and `transact_sound` and the
arithmetic layer depend on no hash assumption. See `Lelantos.TxBinding` for where the
hypothesis is discharged, and `lean/README.md` for the list of what is not proved.

Modelling the arguments as a `List` rather than a fixed arity also gives cross-arity
separation. This matches circom, which instantiates `Poseidon(3)` and `Poseidon(4)` as
distinct permutations.

## Tags

Mirrors `src/lib/tags.circom:19-31`. These must stay byte-identical to
`sdk/src/crypto/tags.ts`; changing any value invalidates every previously issued proof.
-/

namespace Lelantos

/-- Poseidon over BN254 `Fr`, as an opaque function of its argument list. -/
opaque poseidon : List F → F

/-- Literal injectivity of `poseidon` is false. Kept as a theorem so that an
`axiom poseidon_injective` cannot be added without sitting next to its own refutation. -/
theorem poseidon_not_injective : ¬ Function.Injective poseidon := fun hinj =>
  have : Finite (List F) := Finite.of_injective poseidon hinj
  not_finite (List F)

/-- A Poseidon collision: two distinct argument lists with the same digest. -/
def PoseidonCollision : Prop := ∃ a b : List F, a ≠ b ∧ poseidon a = poseidon b

/-- Collision resistance as a hypothesis: no collision means equal digests force equal
preimages. Every hash-binding theorem takes this as an explicit argument — see the module
note for why it is not an axiom. -/
theorem poseidon_inj (hcr : ¬ PoseidonCollision) {a b : List F}
    (h : poseidon a = poseidon b) : a = b := by
  by_contra hab
  exact hcr ⟨a, b, hab, h⟩

/-- The collision-resistance hypothesis is unsatisfiable: collisions exist.

Stated explicitly so the reading of every `hcr`-taking theorem is unambiguous. Such a
theorem is conditional on a false hypothesis, and an empty `#print axioms` result does not
mean hash binding was proved. -/
theorem poseidon_collision : PoseidonCollision := by
  by_contra hnc
  exact poseidon_not_injective fun _ _ hab => poseidon_inj hnc hab

/-! ## Domain-separation tags (`src/lib/tags.circom`) -/

/-- Reserved; `NoteCommitment` uses the packed `asset_id · 2^64 + value` field instead. -/
def TAG_CM : F := 1
def TAG_NF : F := 2
def TAG_PK : F := 3
def TAG_IVK : F := 4
def TAG_MERKLE : F := 5
def TAG_DK : F := 6
def TAG_ASSET : F := 7
def TAG_FMD_BIT : F := 8
def TAG_NK : F := 9
def TAG_LEAF : F := 10
def TAG_RHO : F := 11

/-- `POW_2_64`, the shift used to pack `(asset_id, value)` into one field element. -/
def POW_2_64 : F := 18446744073709551616

theorem pow_2_64_eq : POW_2_64 = ((2 ^ 64 : ℕ) : F) := by
  unfold POW_2_64; norm_num

end Lelantos
