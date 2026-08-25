import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# The circom scalar field

`src/2x2.circom` is compiled for the BN254 curve, so every signal ranges over
`F = ZMod p` with `p` the BN254 scalar-field modulus (circom's default prime `r`).

The only fact about `p` we cannot machine-check here is its primality — see `p_prime`
below and `lean/scripts/check-prime.py` for the external check. Everything else about
`p` (the size bounds) is decided by `norm_num` on concrete numerals.
-/

namespace Lelantos

/-- BN254 scalar-field modulus, i.e. circom's default prime `r`.
Must equal the `p` reported by `snarkjs r1cs info build/2x2.r1cs` (curve `bn-128`). -/
def p : ℕ :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

theorem p_pos : 0 < p := by unfold p; norm_num

/-- Slot indices and small asset ids are tiny; these are all that is needed to inject them
into `F`. -/
theorem one_lt_p : 1 < p := by unfold p; norm_num

theorem two_lt_p : 2 < p := by unfold p; norm_num

/-- `3 < p`: the largest output-slot index over the deployed shapes (`N_OUT = 3` in
`src/3x3.circom`) still injects into `F`, which is what makes `DeriveRho`'s `index`
argument separate output slots. -/
theorem three_lt_p : 3 < p := by unfold p; norm_num

/-- `4 < p`: the same for the widest shape the repository instantiates, `N_OUT = 4` in
`src/4x4.circom:45`. `transact_binding` needs every output index below `p`. -/
theorem four_lt_p : 4 < p := by unfold p; norm_num

/-- `2 ^ 64 < p`: this is what makes `RangeCheck64` a genuine range check rather than a
statement modulo `p`. See `src/lib/balance.circom:11`. -/
theorem two_pow_64_lt_p : 2 ^ 64 < p := by unfold p; norm_num

/-- `2 ^ 66 < p`: `PerAssetValueBalance` sums at most `N_IN + 1` terms of size `< 2 ^ 64`
per side. The largest deployed shape is `Transact(10, 3, 3)` (`src/3x3.circom`), giving four
terms and a bound of `4 · 2^64 = 2^66`, so neither side can wrap. See
`src/lib/balance.circom:75-80`. -/
theorem two_pow_66_lt_p : 2 ^ 66 < p := by unfold p; norm_num

/-- `2 ^ 67 < p`: the same sum at the widest shape the repository instantiates,
`Transact(10, 4, 4)` (`src/4x4.circom:45`) — five terms and a bound of `5 · 2^64 < 2^67`.
This is the only thing `perAssetValueBalance_nat`'s slot bound rests on, so widening the
shapes further is a matter of adding the next power here. -/
theorem two_pow_67_lt_p : 2 ^ 67 < p := by unfold p; norm_num

/-- `2 ^ 128 < p`: `NoteCommitment` packs `asset_id · 2^64 + value` into one field
element, so with both fields 64-bit range-checked the packing is injective.
See `src/lib/note.circom:60`. -/
theorem two_pow_128_lt_p : 2 ^ 128 < p := by unfold p; norm_num

/-- `2 ^ 252 < p`: `MulH` decomposes its scalar with `Num2Bits(252)`, so that
decomposition is also alias-free. See `src/lib/value_commit.circom:41`. -/
theorem two_pow_252_lt_p : 2 ^ 252 < p := by unfold p; norm_num

instance : NeZero p := ⟨by have := p_pos; omega⟩

/-- `ZMod.val` is injective on `F`, the workhorse for moving between the field and `ℕ`. -/
theorem val_inj {a b : ZMod p} (h : a.val = b.val) : a = b := by
  have := congrArg (fun n : ℕ => (n : ZMod p)) h
  simpa [ZMod.natCast_val, ZMod.cast_id] using this

/-!
## The one arithmetic axiom

`p` is a 254-bit prime. Mathlib's `norm_num` primality extension is trial-division based
and cannot certify a number this large, and Mathlib has no Pocklington/Pratt certificate
tactic, so proving this in Lean would mean first developing the Lucas primality criterion
(~200 lines) plus certificates for every prime factor of `p - 1`.

Recorded as an axiom instead. It is listed in `lean/expected/axioms.txt` and surfaced by
`#print axioms`, so it can never be forgotten.

**Discharge:** `python3 lean/scripts/check-prime.py`, or `openssl prime <p>`. `p` is the
standard published BN254 scalar-field order; it is also the modulus circom itself uses, so
if it were composite every claim about the circuit — not just this development — is void.

TODO: replace with a machine-checked Pocklington proof if Mathlib ever grows one.
-/

/-- The BN254 scalar-field modulus is prime. Not machine-checked — see the module note. -/
axiom p_prime : Nat.Prime p

instance : Fact (Nat.Prime p) := ⟨p_prime⟩

/-- Small naturals inject into the field, so a compile-time index like `DeriveRho`'s
`index` argument really does distinguish output slots. -/
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
