import Lelantos.Model.Field

/-!
# Poseidon and the domain-separation tags

Poseidon is modelled as an opaque function `poseidon : List F → F`. Every circom call
`Poseidon(k)([a₁, …, a_k])` becomes `poseidon [a₁, …, a_k]`.

## Collision resistance is a hypothesis, not an axiom

`Function.Injective poseidon` is refutable: `List F` is infinite and `F` is finite, so no
injection exists (`poseidon_not_injective`). As an axiom it would make the development
inconsistent.

Collision resistance instead appears as an explicit hypothesis `hcr : ¬ PoseidonCollision`
on the theorems that need it, and nowhere else. The hypothesis is unsatisfiable
(`poseidon_collision`), so those theorems are vacuous read literally; a non-vacuous
treatment (concrete colliding preimages, or an explicit adversary and advantage bound) is
not modelled. The environment stays consistent, and `transact_sound` and the arithmetic
layer depend on no hash assumption. See `Lelantos.TxBinding` for where the hypothesis is
discharged, and `lean/README.md` for the list of what is not proved.

Modelling the arguments as a `List` gives cross-arity separation, matching circom, which
instantiates `Poseidon(3)` and `Poseidon(4)` as distinct permutations.

## Arities in use

| Arity | Sites |
|---|---|
| 2 | `DeriveIvk`, `DeriveNk`, `DerivePk` |
| 3 | `NoteCommitment` (`TAG_CM`), `DeriveRho` (`TAG_RHO`) |
| 4 | `NoteInner` (`TAG_INNER`), `Nullifier` (`TAG_NF`) |
| 5 | `MerkleLevel4` and `BatchAppend` nodes (`TAG_MERKLE`), `CoeffDigest` blocks (`TAG_DIGEST` on block 0, the previous block's output on the rest) |

Every same-arity pair of sites leads with a different tag, except the later blocks of
`CoeffDigest`, which lead with a hash output. Separating those from a Merkle node is not a
collision-resistance statement and is not claimed in this development.

## Tags

Mirrors `src/lib/tags.circom:30-40`. These must stay byte-identical to
`sdk/src/crypto/tags.ts`; changing any value invalidates every issued proof.
Values 7 and 10 are reserved and must not be reused.
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
preimages. See the module note for why it is not an axiom. -/
theorem poseidon_inj (hcr : ¬ PoseidonCollision) {a b : List F}
    (h : poseidon a = poseidon b) : a = b := by
  by_contra hab
  exact hcr ⟨a, b, hab, h⟩

/-- The collision-resistance hypothesis is unsatisfiable: collisions exist. Every
`hcr`-taking theorem is conditional on a false hypothesis, and an empty `#print axioms`
result does not mean hash binding was proved. -/
theorem poseidon_collision : PoseidonCollision := by
  by_contra hnc
  exact poseidon_not_injective fun _ _ hab => poseidon_inj hnc hab

/-! ## Domain-separation tags (`src/lib/tags.circom`) -/

/-- `cm = Poseidon(TAG_CM, packed_av, inner)`. -/
def TAG_CM : F := 1
def TAG_NF : F := 2
def TAG_PK : F := 3
def TAG_IVK : F := 4
def TAG_MERKLE : F := 5
def TAG_DK : F := 6
def TAG_FMD_BIT : F := 8
def TAG_NK : F := 9
def TAG_RHO : F := 11
/-- `inner = Poseidon(TAG_INNER, pk, rho, rcm)`. -/
def TAG_INNER : F := 14
/-- Leads block 0 of the coefficient digest (`CoeffDigest`, `src/lib/poly_eval.circom:43`). -/
def TAG_DIGEST : F := 15

/-- Two small tag values are different field elements. Used by the same-arity separation
lemmas, where the two preimages differ only in their leading tag. -/
theorem tag_ne {m n : ℕ} (hm : m < 2 ^ 64) (hn : n < 2 ^ 64) (h : m ≠ n) :
    ((m : ℕ) : F) ≠ ((n : ℕ) : F) :=
  natCast_ne_of_lt (lt_trans hm two_pow_64_lt_p) (lt_trans hn two_pow_64_lt_p) h

/-- `POW_2_64`, the shift used to pack `(asset_id, value)` into one field element. -/
def POW_2_64 : F := 18446744073709551616

theorem pow_2_64_eq : POW_2_64 = ((2 ^ 64 : ℕ) : F) := by
  unfold POW_2_64; norm_num

end Lelantos
