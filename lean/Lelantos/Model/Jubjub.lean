import Lelantos.Model.Bits

/-!
# Baby Jubjub, as the circuit uses it

The circuit only ever manipulates points of the **prime-order subgroup** of Baby Jubjub:
`EscalarMulAny` requires its base to lie there (`circomlib/escalarmulany.circom:129`), and
every point in `2x2.circom` is produced by `Pedersen`, `EscalarMulFix`, `EscalarMulAny` or
`BabyAdd` applied to such points.

That subgroup is cyclic of prime order `ell`, so it is *isomorphic to* `ZMod ell` — and
modelling it as literally `ZMod ell` is not a loss of generality, it is an honest
statement of the situation. It also makes the central negative result unavoidable rather
than easy to overlook: in a cyclic group written additively, "known relative discrete
logs" is not a weakness one has to remember to model, it is the default.

Constraints in circom compare *coordinates*, not abstract group elements, so we keep a
`coords : G → Pt` embedding and require it to be injective. Coordinate equality is then
group equality, which is what `PerAssetPointBalance` actually checks.

## What is axiomatized here

* `ell_prime` — arithmetic, same situation as `Lelantos.p_prime`.
* `coords_injective` — distinct subgroup elements have distinct affine coordinates. True
  of any affine embedding of an elliptic curve group.
* `babyAdd_spec` — circomlib's `BabyAdd` computes the group law. Its two `<--` divisions
  (`babyjub.circom:45,48`) are immediately re-constrained by
  `(1 ± d·τ) * out === …`, which pins `out` **provided** `1 ± d·τ ≠ 0`. On Baby Jubjub
  `a = 168700` is a square and `d = 168696` is a non-square, so the twisted Edwards
  addition law is complete and the denominators never vanish for on-curve inputs. That
  completeness fact is what `babyAdd_spec` packages.
* `escalarMul_spec` — `EscalarMulAny(n)` / `EscalarMulFix(n)` compute `k • P`.
* `assetGen_dl` — `HashToAssetGen` is a *single-segment* Pedersen hash, so it is a known
  multiple of one fixed base. See `Lelantos.Gadgets.PointBalance` for the consequence.
-/

namespace Lelantos

/-- Order of the Baby Jubjub prime-order subgroup: the full curve order divided by the
cofactor 8. Equals `circomlibjs`'s `babyJub.subOrder`
(`node_modules/circomlibjs/src/babyjub.js:23`). -/
def ell : ℕ :=
  2736030358979909402780800718157159386076813972158567259200215660948447373041

/-- The subgroup order is prime. Same situation as `Lelantos.p_prime`: a 251-bit primality
certificate is out of reach for `norm_num`. Discharge with
`python3 lean/scripts/check-prime.py`. -/
axiom ell_prime : Nat.Prime ell

instance : Fact (Nat.Prime ell) := ⟨ell_prime⟩
instance : NeZero ell := ⟨by have := ell_prime.pos; omega⟩

/-- The prime-order subgroup of Baby Jubjub, written additively. -/
abbrev G : Type := ZMod ell

/-- An affine point as the circuit sees it: the pair of field elements that constraints
compare. -/
structure Pt where
  x : F
  y : F
deriving DecidableEq

instance : Inhabited Pt := ⟨⟨0, 0⟩⟩

/-- The affine coordinates of a subgroup element. -/
opaque coords : G → Pt

/-- Distinct group elements have distinct coordinates, so the coordinate-wise equalities
that `PerAssetPointBalance` checks really are group equalities. -/
axiom coords_injective : Function.Injective coords

theorem coords_inj {g h : G} (hgh : coords g = coords h) : g = h := coords_injective hgh

/-- circomlib `BabyAdd` (`babyjub.circom:35-50`) computes the group law. The two `<--`
divisions are pinned by the following `===` because the twisted Edwards addition law on
Baby Jubjub is complete — see the module note. -/
axiom babyAdd : Pt → Pt → Pt

axiom babyAdd_spec (g h : G) : babyAdd (coords g) (coords h) = coords (g + h)

/-- `EscalarMulAny(n)` / `EscalarMulFix(n)`: the output is the scalar multiple of the base
by the natural number the bits encode. -/
axiom escalarMul : ℕ → Pt → Pt

axiom escalarMul_spec (k : ℕ) (g : G) : escalarMul k (coords g) = coords ((k : ZMod ell) • g)

/-- The Pedersen value base `H`, circomlib's `BASE[2]`
(`src/lib/value_commit.circom:15,18`). -/
axiom H : G

/-- The base all asset generators are built from: circomlib's `BASE[0]`. -/
axiom BASE0 : G

/-- The publicly computable multiplier behind `HashToAssetGen`. -/
axiom assetMul : F → ℕ

/-- The per-asset generator `V^a`. -/
noncomputable def assetGen (a : F) : G := (assetMul a : ZMod ell) • BASE0

/-- **The known-discrete-log fact.** `HashToAssetGen` (`src/lib/asset_gen.circom:11`)
Pedersen-hashes a 72-bit message, which circomlib packs into a *single* segment, so the
result is always `assetMul a • BASE[0]` for a multiplier anyone can compute. This is
`assetGen` by definition above; the axiom is that `assetMul` exists and is computable,
which `src/lib/balance.circom:56-62` and `src/README.md § 5` already state in prose. -/
theorem assetGen_dl (a : F) : assetGen a = (assetMul a : ZMod ell) • BASE0 := rfl

/-- Asset ids `1, 2, 3` differ only in the lowest 4-bit Pedersen window (the tag occupies
message bits 0-7, `asset_id` bits 8-71), and circomlib's signed 4-bit encoding maps those
three windows to the consecutive multipliers `2, 3, 4`. Since `assetMul` is affine in the
window contribution, the multipliers form an arithmetic progression.

This is the concrete instance that makes `pointBalance_not_sound` bite. It is checked at
runtime by `src/test/transact.test.ts:847`. -/
axiom assetMul_arith : assetMul 1 + assetMul 3 = 2 * assetMul 2

/-- `PointSum(n)` (`src/lib/value_commit.circom:91`): the identity for `n = 0`, otherwise a
left-nested chain of `BabyAdd`. -/
def pointSum (pts : ℕ → G) (n : ℕ) : G := ∑ i ∈ Finset.range n, pts i

end Lelantos
