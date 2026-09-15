import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# The circom scalar field

`src/4x6.circom` is compiled for the BN254 curve, so every signal ranges over
`F = ZMod p` with `p` the BN254 scalar-field modulus (circom's default prime `r`).

The primality of `p` is not machine-checked here; see `p_prime` below and
`lean/scripts/check-prime.py` for the external check. The size bounds on `p` are decided
by `norm_num` on concrete numerals.
-/

namespace Lelantos

/-- BN254 scalar-field modulus, i.e. circom's default prime `r`.
Must equal the `p` reported by `snarkjs r1cs info build/4x6.r1cs` (curve `bn-128`). -/
def p : ℕ :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

theorem p_pos : 0 < p := by unfold p; norm_num

/-- Small bounds used to inject slot indices and small asset ids into `F`. -/
theorem one_lt_p : 1 < p := by unfold p; norm_num

theorem two_lt_p : 2 < p := by unfold p; norm_num

/-- `3 < p`: the bound the small completeness shapes are stated at. It keeps distinct slot
indices distinct in `F`, which `DeriveRho`'s `index` argument relies on to separate output
slots; the deployed shape needs `seven_lt_p` below. -/
theorem three_lt_p : 3 < p := by unfold p; norm_num

/-- `4 < p`: a small-shape bound; `transact_binding` uses `seven_lt_p` below. -/
theorem four_lt_p : 4 < p := by unfold p; norm_num

/-- `7 < p`: the ceiling `transact_binding` and `perAssetValueBalance_nat` are stated at.

The widest instantiated shape (`Transact(11, 4, 6)`, `src/4x6.circom`) needs six. The
balance bound below rounds `(n + 1) · 2^64` up to `8 · 2^64 = 2^67`, so seven is the largest
slot count that argument covers without a new power. -/
theorem seven_lt_p : 7 < p := by unfold p; norm_num

/-- `2 ^ 64 < p`: makes `RangeCheck64` an integer range check rather than a statement
modulo `p`. See `src/lib/balance.circom:11`. -/
theorem two_pow_64_lt_p : 2 ^ 64 < p := by unfold p; norm_num

/-- `2 ^ 66 < p`: `PerAssetValueBalance` sums at most `N_IN + 1` terms of size `< 2 ^ 64`
per side, so a three-slot side is bounded by `4 · 2^64 = 2^66`. Used by the small
completeness shapes; `Transact(11, 4, 6)` needs `two_pow_67_lt_p` below. See
`src/lib/balance.circom:75-79`. -/
theorem two_pow_66_lt_p : 2 ^ 66 < p := by unfold p; norm_num

/-- `2 ^ 67 < p`: the same sum at the widest shape the repository instantiates,
`Transact(11, 4, 6)` (`src/4x6.circom`) — seven terms and a bound of `7 · 2^64 < 2^67`.

`perAssetValueBalance_nat`'s slot bound rests only on this. It covers any shape with at
most seven slots per side, since the proof rounds up to `8 · 2^64`; more slots require the
next power here and relaxing the two bounds that cite it. -/
theorem two_pow_67_lt_p : 2 ^ 67 < p := by unfold p; norm_num

/-- `2 ^ 128 < p`: `NoteCommitment` packs `asset_id · 2^64 + value` into one field
element, so with both fields 64-bit range-checked the packing is injective.
See `src/lib/note.circom:59`. -/
theorem two_pow_128_lt_p : 2 ^ 128 < p := by unfold p; norm_num

/-- `2 ^ 252 < p`: `MulH` decomposes its scalar with `Num2Bits(252)`, so that
decomposition is also alias-free. See `src/lib/value_commit.circom:37`. -/
theorem two_pow_252_lt_p : 2 ^ 252 < p := by unfold p; norm_num

instance : NeZero p := ⟨by have := p_pos; omega⟩

/-- `ZMod.val` is injective on `F`; used to move between the field and `ℕ`. -/
theorem val_inj {a b : ZMod p} (h : a.val = b.val) : a = b := by
  have := congrArg (fun n : ℕ => (n : ZMod p)) h
  simpa [ZMod.natCast_val, ZMod.cast_id] using this

/-!
## The one arithmetic axiom

`p` is a 254-bit prime. Mathlib's `norm_num` primality extension is trial-division based
and cannot certify a number this large, and Mathlib has no Pocklington/Pratt certificate
tactic; a Lean proof would require the Lucas primality criterion (~200 lines) plus
certificates for every prime factor of `p - 1`.

It is therefore an axiom, listed in `lean/expected/axioms.txt` and surfaced by
`#print axioms`.

**Discharge:** `python3 lean/scripts/check-prime.py`, or `openssl prime <p>`. `p` is the
published BN254 scalar-field order and the modulus circom uses, so if it were composite
every claim about the circuit would be void, independently of this development.

TODO: replace with a machine-checked Pocklington proof once Mathlib supports one.
-/

/-- The BN254 scalar-field modulus is prime. Not machine-checked — see the module note. -/
axiom p_prime : Nat.Prime p

instance : Fact (Nat.Prime p) := ⟨p_prime⟩

/-- Small naturals inject into the field, so a compile-time index like `DeriveRho`'s
`index` argument distinguishes output slots. -/
theorem natCast_inj_of_lt {m n : ℕ} (hm : m < p) (hn : n < p) (h : (m : ZMod p) = (n : ZMod p)) :
    m = n := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt hm, ZMod.val_natCast_of_lt hn] at this

/-- Distinct naturals below `p` remain distinct in the field: no wrap-around identifies
them. Used wherever a statement mentions concrete asset ids or slot indices. -/
theorem natCast_ne_of_lt {m n : ℕ} (hm : m < p) (hn : n < p) (h : m ≠ n) :
    ((m : ℕ) : ZMod p) ≠ ((n : ℕ) : ZMod p) := fun heq => h (natCast_inj_of_lt hm hn heq)

/-- The circom signal type: BN254 `Fr`. -/
abbrev F : Type := ZMod p

end Lelantos
