import Lelantos.Circuit.Transact

/-!
# Assignments the constraint system rejects

`transact_sound` states what a satisfying assignment proves; this module states the
contrapositive, that families of malformed transactions have no satisfying assignment at
all. Each result takes `TransactSat w` plus a description of the malformation and derives
`False`, so it rules out a family rather than one hand-built counterexample. These are the
Lean counterparts of the rejecting cases in `test/transact/`.
-/

namespace Lelantos

variable {depth nIn nOut : ℕ} {w : TxWitness depth nIn nOut}

/-- Conservation with the sums expanded, at the two-in/two-out shape. -/
private theorem conservation_2x2 (h : TransactSat w) (hnIn : nIn = 2) (hnOut : nOut = 2)
    (a : F) :
    (inValue w 0).val * indN (inAsset w 0 = a)
        + (inValue w 1).val * indN (inAsset w 1 = a)
      = w.publicOut.val * indN (w.publicAssetId = a)
        + ((outValue w 0).val * indN (outAsset w 0 = a)
          + (outValue w 1).val * indN (outAsset w 1 = a)) := by
  subst hnIn; subst hnOut
  have hcons := (transact_sound (by norm_num) (by norm_num) h).conservation a
  unfold ConservesAtNat at hcons
  simpa [Finset.sum_range_succ, add_assoc] using hcons

/-! ## Value conservation -/

/-- **Minting is rejected.** An asset that appears on no input slot cannot leave the
transaction as a note with a non-zero value. -/
theorem mint_from_nothing_rejected (h : TransactSat w) (hnIn : nIn ≤ 7) (hnOut : nOut ≤ 7)
    {a : F} (hnotIn : ∀ i, i < nIn → inAsset w i ≠ a)
    {j : ℕ} (hj : j < nOut) (hja : outAsset w j = a) (hpos : outValue w j ≠ 0) : False :=
  hpos (no_asset_creation hnIn hnOut h a hnotIn j hj hja)

/-- **Withdrawing an asset nobody spent is rejected.** -/
theorem withdraw_from_nothing_rejected (h : TransactSat w) (hnIn : nIn ≤ 7) (hnOut : nOut ≤ 7)
    (hnotIn : ∀ i, i < nIn → inAsset w i ≠ w.publicAssetId) (hpos : w.publicOut ≠ 0) : False :=
  hpos (no_asset_withdrawal hnIn hnOut h hnotIn)

/-- **Inflation is rejected.** With a single asset `a` on both sides, the output total is at
most the input total; claiming more is impossible. The transparent bucket cannot help: it
sits on the output side and only takes value out. -/
theorem inflation_rejected (h : TransactSat w) (hnIn : nIn = 2) (hnOut : nOut = 2)
    {a : F} (hin0 : inAsset w 0 = a) (hin1 : inAsset w 1 = a)
    (hout0 : outAsset w 0 = a) (hout1 : outAsset w 1 = a)
    (hgt : (inValue w 0).val + (inValue w 1).val
            < (outValue w 0).val + (outValue w 1).val) : False := by
  classical
  have hcons := conservation_2x2 h hnIn hnOut a
  rw [hin0, hin1, hout0, hout1] at hcons
  have esame : indN (a = a) = 1 := if_pos rfl
  rw [esame] at hcons
  omega

/-! ## The transparent bucket -/

/-- **A transfer that names an asset is rejected.** With nothing withdrawn, the bucket's
asset id must be `0`, so a shielded transfer cannot be made to publish the asset it moves. -/
theorem transfer_naming_asset_rejected (h : TransactSat w) (hout : w.publicOut = 0)
    (hasset : w.publicAssetId ≠ 0) : False :=
  hasset (publicBucket_zero_asset h hout)

/-- **A withdrawal under asset id 0 is rejected.** Id `0` means "no asset". -/
theorem withdraw_asset_zero_rejected (h : TransactSat w) (hasset : w.publicAssetId = 0)
    (hout : w.publicOut ≠ 0) : False :=
  hout (publicBucket_zero_out h hasset)

/-! ## Structural malformations -/

/-- **A padding slot carrying value is rejected.** This makes a dummy input neutral for
conservation, and hence makes skipping its Merkle check safe. -/
theorem dummy_with_value_rejected (h : TransactSat w) (hnIn : nIn ≤ 7) (hnOut : nOut ≤ 7)
    {i : ℕ} (hi : i < nIn) (hdummy : (w.spent i).isDummy = 1)
    (hval : (w.spent i).value ≠ 0) : False :=
  hval ((transact_sound hnIn hnOut h).dummySlots i hi hdummy)

/-- **A zero asset id on an output is rejected**, unconditionally — the check is not gated
on a dummy flag, unlike the input side. -/
theorem zero_asset_output_rejected (h : TransactSat w) (hnIn : nIn ≤ 7) (hnOut : nOut ≤ 7)
    {j : ℕ} (hj : j < nOut) (hzero : outAsset w j = 0) : False :=
  ((transact_sound hnIn hnOut h).outputs j hj).assetNonzero hzero

/-- **An out-of-range value is rejected.** Every value is 64-bit, which is the precondition
the no-wrap argument in `perAssetValueBalance_nat` consumes. -/
theorem oversized_value_rejected (h : TransactSat w) {i : ℕ} (hi : i < nIn)
    (hbig : 2 ^ 64 ≤ (inValue w i).val) : False := by
  have hsmall := spentNote_valueRange (h.spent_sat i hi)
  unfold inValue at hbig
  omega

/-- **An out-of-range asset id is rejected on every input slot, dummies included.** The
bound is unconditional because the packing inside `NoteCommitment` is injective only under
it. -/
theorem oversized_input_asset_rejected (h : TransactSat w) {i : ℕ} (hi : i < nIn)
    (hbig : 2 ^ 64 ≤ (inAsset w i).val) : False := by
  have hsmall := spentNote_assetRange (h.spent_sat i hi)
  unfold inAsset at hbig
  omega

/-- **An out-of-range asset id is rejected on every output slot.** -/
theorem oversized_output_asset_rejected (h : TransactSat w) {j : ℕ} (hj : j < nOut)
    (hbig : 2 ^ 64 ≤ (outAsset w j).val) : False := by
  have hsmall := (outputNote_sound (h.out_sat j hj)).assetRange
  unfold outAsset at hbig
  omega

/-- **An out-of-range transparent bucket is rejected**, in either word. -/
theorem oversized_public_rejected (h : TransactSat w)
    (hbig : 2 ^ 64 ≤ w.publicAssetId.val ∨ 2 ^ 64 ≤ w.publicOut.val) : False := by
  have ha := rangeCheck64_sound h.pub_asset_range
  have ho := rangeCheck64_sound h.pub_out_range
  omega

/-- **A spent slot opened against a different root is rejected.** Every input is checked
against the single advertised root, so a prover cannot mix trees within one transaction. -/
theorem foreign_root_rejected (h : TransactSat w) {i : ℕ} (hi : i < nIn)
    (hne : (w.spent i).root ≠ w.merkleRoot) : False :=
  hne (h.spent_root i hi)

/-- **A zero challenge is rejected.** At `z = 0` only the first coefficient would reach
`y`. -/
theorem zero_challenge_rejected (h : TransactSat w) (hz : w.z = 0) : False :=
  polyEvalSat_z_ne_zero h.compress hz

/-- **A public digest that is not the digest of the coefficients is rejected.** The
prover cannot publish a `digest` for one coefficient vector and evaluate another into
`y`. -/
theorem wrong_digest_rejected (h : TransactSat w)
    (hne : w.digest ≠ coeffDigest (txCoeffs w) (piCount nIn nOut)) : False :=
  hne (transact_digest_public h)

/-- **Two outputs sharing a `rho` are rejected**, so two notes of one transaction cannot
share a future nullifier. Requires collision resistance, so it is stated against
`TxBinding` rather than `TxWellFormed`. -/
theorem shared_rho_rejected (hnc : ¬ PoseidonCollision) (h : TransactSat w)
    (hnOut : nOut ≤ 7)
    {j j' : ℕ} (hj : j < nOut) (hj' : j' < nOut) (hne : j ≠ j')
    (hshared : (w.out j).rho = (w.out j').rho) : False :=
  (transact_binding hnc hnOut h).rhoDistinct j j' hj hj' hne hshared

end Lelantos
