import Lelantos.Circuit.Transact

/-!
# Assignments the constraint system rejects

`transact_sound` states what a satisfying assignment proves; this module states the
contrapositive, that families of malformed transactions have no satisfying assignment at
all. Each result takes `TransactSat w` plus a description of the malformation and derives
`False`, so it rules out a family rather than one hand-built counterexample. These are the
Lean counterparts of the rejecting cases in `src/test/transact.test.ts`.

`cross_asset_cancellation_rejected` is the one to read first: the assignment that
`Lelantos.pointBalance_not_sound` shows the Edwards point balance *accepts* has no
satisfying assignment of the full system. The two together are exactly what the
defence-in-depth comment at `src/lib/balance.circom:34-41` claims.
-/

namespace Lelantos

variable {depth nIn nOut : ℕ} {w : TxWitness depth nIn nOut}

/-- Conservation with the sums expanded, for the deployed two-in/two-out shape. -/
private theorem conservation_2x2 (h : TransactSat w) (hnIn : nIn = 2) (hnOut : nOut = 2)
    (a : F) :
    w.publicIn.val * indN (w.publicAssetId = a)
        + ((inValue w 0).val * indN (inAsset w 0 = a)
          + (inValue w 1).val * indN (inAsset w 1 = a))
      = w.publicOut.val * indN (w.publicAssetId = a)
        + ((outValue w 0).val * indN (outAsset w 0 = a)
          + (outValue w 1).val * indN (outAsset w 1 = a)) := by
  subst hnIn; subst hnOut
  have hcons := (transact_sound (by norm_num) (by norm_num) h).conservation a
  unfold ConservesAtNat at hcons
  simpa [Finset.sum_range_succ, add_assoc] using hcons

/-- `(1 : F)` reads back as the natural number `1`. -/
private theorem val_one : (1 : F).val = 1 := by
  have h1 : (1 : F) = ((1 : ℕ) : F) := by norm_num
  rw [h1, ZMod.val_natCast_of_lt (by have := two_lt_p; omega)]

private theorem zero_ne_one' : (0 : F) ≠ 1 :=
  zero_ne_one

private theorem two_ne_one' : (2 : F) ≠ 1 := by
  simpa using natCast_ne_of_lt (m := 2) (n := 1) two_lt_p one_lt_p (by norm_num)

private theorem three_ne_one' : (3 : F) ≠ 1 := by
  simpa using natCast_ne_of_lt (m := 3) (n := 1)
    (lt_trans (by norm_num) two_pow_64_lt_p) one_lt_p (by norm_num)

/-! ## Value conservation -/

/-- **Cross-asset cancellation is rejected.** One unit of asset `1` and one unit of asset
`3` in, two units of asset `2` out, nothing public: this satisfies the Edwards point balance
exactly, because `V¹ + V³ = 2·V²` (see `Lelantos.pointBalance_not_sound`). The per-asset
value balance rejects it, because asset ids are compared as field elements rather than as
curve points.

This is the in-Lean counterpart of the `F2` case in `src/test/transact.test.ts`, and the
reason `PerAssetValueBalance` exists. -/
theorem cross_asset_cancellation_rejected (h : TransactSat w)
    (hnIn : nIn = 2) (hnOut : nOut = 2)
    (hin0 : inAsset w 0 = 1) (hin1 : inAsset w 1 = 3)
    (hv0 : inValue w 0 = 1)
    (hout0 : outAsset w 0 = 2) (hout1 : outAsset w 1 = 2)
    (hpub : w.publicAssetId = 0) : False := by
  classical
  have hcons := conservation_2x2 h hnIn hnOut 1
  rw [hin0, hin1, hv0, hout0, hout1, hpub] at hcons
  -- The public bucket sits at asset `0` and every output at asset `2`, so on the right every
  -- indicator vanishes; on the left the asset-`1` input contributes one unit.
  have e0 : indN ((0 : F) = 1) = 0 := if_neg zero_ne_one'
  have e1 : indN ((1 : F) = 1) = 1 := if_pos rfl
  have e2 : indN ((2 : F) = 1) = 0 := if_neg two_ne_one'
  have e3 : indN ((3 : F) = 1) = 0 := if_neg three_ne_one'
  rw [e0, e1, e2, e3, val_one] at hcons
  omega

/-- **Minting is rejected.** An asset that appears on no input slot and is not the public
bucket's asset cannot leave the transaction with a non-zero value. -/
theorem mint_from_nothing_rejected (h : TransactSat w) (hnIn : nIn ≤ 2) (hnOut : nOut ≤ 2)
    {a : F} (hnotIn : ∀ i, i < nIn → inAsset w i ≠ a) (hnotPub : w.publicAssetId ≠ a)
    {j : ℕ} (hj : j < nOut) (hja : outAsset w j = a) (hpos : outValue w j ≠ 0) : False :=
  hpos (no_asset_creation hnIn hnOut h a hnotIn hnotPub j hj hja)

/-- **Inflation is rejected.** With a single asset `a` on both sides and no public bucket,
the output total is exactly the input total; claiming more is impossible. -/
theorem inflation_rejected (h : TransactSat w) (hnIn : nIn = 2) (hnOut : nOut = 2)
    {a : F} (hin0 : inAsset w 0 = a) (hin1 : inAsset w 1 = a)
    (hout0 : outAsset w 0 = a) (hout1 : outAsset w 1 = a) (hpub : w.publicAssetId ≠ a)
    (hgt : (inValue w 0).val + (inValue w 1).val
            < (outValue w 0).val + (outValue w 1).val) : False := by
  classical
  have hcons := conservation_2x2 h hnIn hnOut a
  rw [hin0, hin1, hout0, hout1] at hcons
  have esame : indN (a = a) = 1 := if_pos rfl
  have epub : indN (w.publicAssetId = a) = 0 := if_neg hpub
  rw [esame, epub] at hcons
  omega

/-! ## Structural malformations -/

/-- **A padding slot carrying value is rejected.** This is what makes a dummy input neutral
for conservation, and hence what makes the bypassed Merkle check safe. -/
theorem dummy_with_value_rejected (h : TransactSat w) (hnIn : nIn ≤ 2) (hnOut : nOut ≤ 2)
    {i : ℕ} (hi : i < nIn) (hdummy : (w.spent i).isDummy = 1)
    (hval : (w.spent i).value ≠ 0) : False :=
  hval ((transact_sound hnIn hnOut h).dummySlots i hi hdummy)

/-- **A zero asset id on an output is rejected**, unconditionally — the check is not gated
on a dummy flag, unlike the input side. This is what keeps `packed_av ≥ 2^64` and so keeps
the commitment preimage separated from the tag-prefixed hashes. -/
theorem zero_asset_output_rejected (h : TransactSat w) (hnIn : nIn ≤ 2) (hnOut : nOut ≤ 2)
    {j : ℕ} (hj : j < nOut) (hzero : outAsset w j = 0) : False :=
  ((transact_sound hnIn hnOut h).outputs j hj).assetNonzero hzero

/-- **An out-of-range value is rejected.** Every value is 64-bit, which is the precondition
the no-wrap argument in `perAssetValueBalance_nat` consumes. -/
theorem oversized_value_rejected (h : TransactSat w) {i : ℕ} (hi : i < nIn)
    (hbig : 2 ^ 64 ≤ (inValue w i).val) : False := by
  have hsmall := spentNote_valueRange (h.spent_sat i hi)
  unfold inValue at hbig
  omega

/-- **A spent slot opened against a different root is rejected.** Every input is checked
against the single advertised root, so a prover cannot mix trees within one transaction. -/
theorem foreign_root_rejected (h : TransactSat w) {i : ℕ} (hi : i < nIn)
    (hne : (w.spent i).root ≠ w.merkleRoot) : False :=
  hne (h.spent_root i hi)

/-- **Two outputs sharing a `rho` are rejected**, which is what stops two notes of one
transaction from sharing a future nullifier. Needs collision resistance, so it is stated
against `TxBinding` rather than `TxWellFormed`. -/
theorem shared_rho_rejected (hnc : ¬ PoseidonCollision) (h : TransactSat w)
    (hnOut : nOut ≤ 2)
    {j j' : ℕ} (hj : j < nOut) (hj' : j' < nOut) (hne : j ≠ j')
    (hshared : (w.out j).rho = (w.out j').rho) : False :=
  (transact_binding hnc hnOut h).rhoDistinct j j' hj hj' hne hshared

end Lelantos
