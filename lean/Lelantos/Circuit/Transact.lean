import Lelantos.Circuit.Witness
import Lelantos.Gadgets.PointBalance
import Lelantos.Gadgets.PolyEval

/-!
# `src/2x2.circom` — the whole transact circuit

`Transact(DEPTH, N_IN, N_OUT)` is wiring: the per-slot logic lives in `SpentNote` and
`OutputNote`, and this file composes it with the public bucket, the two balance checks and
the public-input compression.

`transact_sound` is the top-level result. Given any assignment satisfying the modeled
constraint system it produces `TxWellFormed`, whose fields are the actual security
properties:

* every non-dummy input slot proves ownership and Merkle membership,
* every dummy input slot carries value `0`,
* every input slot is opened against the *same* root,
* every output slot is well-formed and its `rho` is the Orchard-style derivation,
* **for every asset id in the field**, value is conserved as an equation over `ℕ`,
* the deposit value commitments are the ones the output notes computed,
* and `y` is the polynomial evaluation of the declared 31-slot layout at `z`.

Every one of those is arithmetic: `transact_sound` assumes **nothing about Poseidon**.

The hash-binding properties — pairwise-distinct output `rho`s, Merkle membership being
binding rather than merely existential, and a commitment pinning its whole note — live in
the separate `TxBinding`, proved by `transact_binding` from an explicit collision-resistance
hypothesis. That hypothesis is unsatisfiable (`poseidon_collision`), so `TxBinding` is
assumed rather than proved; keeping it out of `TxWellFormed` is what stops the assumption
from reaching conservation and every other consequence. See `Lelantos.Model.Poseidon`.

## What is *not* claimed

* `PerAssetPointBalance` is included in the constraint model but no conclusion is drawn
  from it — see `pointBalance_not_sound`. Conservation comes only from
  `PerAssetValueBalance`.
* `rho` uniqueness across transactions reduces to the contract enforcing nullifier
  uniqueness, so it appears in `ContractObligations`, not as a theorem.
* The FMD clue fields are bound by `PolyEval` and by nothing else. That is the circuit's
  actual behaviour (`src/README.md § 1 "FMD clue binding"`), and the model says so.
* `outAuxDigest` is likewise `PolyEval`-bound and nothing more. The circuit carries the
  digest so that altering it changes `y`; that it *is* the hash of the payload the contract
  received is checked on-chain, so it sits in `ContractObligations`.
* Everything is modulo the axioms in `Lelantos.Meta.Assumptions`.
-/

namespace Lelantos

variable {depth nIn nOut : ℕ}

/-- The constraint system of `Transact(depth, nIn, nOut)`. -/
structure TransactSat (w : TxWitness depth nIn nOut) : Prop where
  /-- `src/lib/transact.circom:97-117` — each spent slot, bound to the shared root. -/
  spent_sat : ∀ i, i < nIn → SpentNoteSat (w.spent i)
  spent_root : ∀ i, i < nIn → (w.spent i).root = w.merkleRoot
  /-- `:88, 113-114` — `DummyZeroValue(N_IN)`. -/
  dummy_zero : DummyZeroValueSat nIn (fun i => (w.spent i).isDummy) (inValue w)
  /-- `:126-129` — output `rho` is the Orchard-style derivation from `nullifier[0]`. -/
  rho_derived : ∀ j, j < nOut → (w.out j).rho = deriveRho (w.spent 0).nullifier (j : F)
  /-- `:131-141` — each output slot. -/
  out_sat : ∀ j, j < nOut → OutputNoteSat (w.out j)
  /-- `:143-144` — the forwarded deposit commitments are the ones the outputs computed. -/
  cv_dep_bound : ∀ j, j < nOut → w.outCvDep j = (w.out j).cvDep
  /-- `:150-161` — the public bucket: generator, two `ValueTimesGen`s (each a
  `RangeCheck64` plus a `ValueScalarMul`, `src/lib/balance.circom:24-40`). -/
  pub_gen : w.pubGen = coords (assetGen w.publicAssetId)
  /-- `HashToAssetGen` decomposes its argument with `Num2Bits(64)`
  (`src/lib/asset_gen.circom:15-16`), so the public bucket's asset id is range-checked
  too. Modelled so that every `===` in the transitive closure is accounted for. -/
  pub_asset_range : Num2BitsSat 64 w.publicAssetId w.pubAssetBits
  pub_in_range : RangeCheck64Sat w.publicIn w.pubInBits
  pub_out_range : RangeCheck64Sat w.publicOut w.pubOutBits
  pub_in_mul : ValueScalarMulSat w.pubInBits w.pubGen w.pubInPt
  pub_out_mul : ValueScalarMulSat w.pubOutBits w.pubGen w.pubOutPt
  /-- `:166-177` — the load-bearing conservation check. -/
  value_balance : PerAssetValueBalanceSat nIn nOut (inAsset w) (inValue w) (outAsset w)
    (outValue w) w.publicAssetId w.publicIn w.publicOut w.vbPubInv w.vbPubEq
    w.vbInInv w.vbInEq w.vbOutInv w.vbOutEq w.vbInTerm w.vbOutTerm w.vbLhs w.vbRhs
  /-- `:179-195` — the point equation. Included for fidelity; nothing is derived from it,
  because `pointBalance_not_sound` shows nothing can be. -/
  point_balance : PerAssetPointBalanceSat nIn nOut w.inCvG w.outCvG w.inRHG w.outRHG
    w.pubInG w.pubOutG
  point_in_cv : ∀ i, i < nIn → (w.spent i).cv = coords (w.inCvG i)
  point_out_cv : ∀ j, j < nOut → (w.out j).cv = coords (w.outCvG j)
  point_in_rH : ∀ i, i < nIn → (w.spent i).rH = coords (w.inRHG i)
  point_out_rH : ∀ j, j < nOut → (w.out j).rH = coords (w.outRHG j)
  /-- The public bucket's two points, as the point equation reads them. Without these the
  group-level `pubInG` / `pubOutG` would be free variables disconnected from the signals
  `pub_in_mul` / `pub_out_mul` produce, and `point_balance` would be satisfiable for *any*
  assignment by solving for `pubOutG` — i.e. modelled in name only. -/
  point_pub_in : w.pubInPt = coords w.pubInG
  point_pub_out : w.pubOutPt = coords w.pubOutG
  /-- `:200-225` — public-input compression. -/
  compress : PolyEvalSat (piCount nIn nOut) (txCoeffs w) w.z w.peAcc w.y

/-- Obligations the circuit cannot discharge, which the contract must.
Listed so that no theorem below can silently assume them. -/
structure ContractObligations (w : TxWitness depth nIn nOut) : Prop where
  /-- `nullifier[i]` is unspent. Also what makes `rho` derivation collision-free across
  transactions, since `DeriveRho` anchors on `nullifier[0]`. -/
  nullifiers_fresh : True
  /-- `z` is a Fiat-Shamir challenge derived from the full coefficient vector, not chosen
  by the prover. Without this `PolyEval` binding is vacuous. -/
  challenge_is_fiat_shamir : True
  /-- `chain_id = block.chainid` and `recipient_address < 2^160`. -/
  address_and_chain_checked : True
  /-- `out_aux_digest` is recomputed from the `aux` calldata, not taken from it. The
  coefficient binds whatever value the prover put there; only this check ties that value to
  the encrypted-note payload the recipient will actually receive. Without it a relayer keeps
  the `PolyEval`-bound clue intact — so the recipient still flags the note — while corrupting
  `ephPub` and the ciphertext, leaving a note that cannot be opened after its inputs are
  already spent. -/
  aux_digest_recomputed : True

/-- What a satisfying assignment proves. -/
structure TxWellFormed (w : TxWitness depth nIn nOut) : Prop where
  /-- Non-dummy inputs are genuine, owned, in-tree notes. -/
  realSlots : ∀ i, i < nIn → (w.spent i).isDummy = 0 → SpentReal (w.spent i)
  /-- Dummy inputs carry no value, so they are neutral for conservation. -/
  dummySlots : ∀ i, i < nIn → (w.spent i).isDummy = 1 → (w.spent i).value = 0
  /-- Every input slot is opened against the single advertised root. -/
  sharedRoot : ∀ i, i < nIn → (w.spent i).root = w.merkleRoot
  /-- Outputs are well-formed and bind their asset and value. -/
  outputs : ∀ j, j < nOut → OutputWellFormed (w.out j)
  /-- Output `rho` values are the Orchard-style derivation, so two outputs of the same
  transaction cannot share a future nullifier. -/
  rhoDerived : ∀ j, j < nOut → (w.out j).rho = deriveRho (w.spent 0).nullifier (j : F)
  /-- **Per-asset value conservation, over `ℕ`, for every asset id in the field.** -/
  conservation : ∀ a : F,
    ConservesAtNat nIn nOut (inAsset w) (inValue w) (outAsset w) (outValue w)
      w.publicAssetId w.publicIn w.publicOut a
  /-- The forwarded deposit commitments are the outputs' own. -/
  depositBinding : ∀ j, j < nOut → w.outCvDep j = (w.out j).cvDep
  /-- The compressed public input is the honest evaluation of the declared layout. -/
  compression : w.y = polyEval (txCoeffs w) (piCount nIn nOut) w.z
  /-- **Every input slot is covered by exactly one of the two cases above.** Without this
  the conclusion is silent about a slot whose `is_dummy` is neither `0` nor `1`, and
  "each input is a genuine note or carries no value" would not follow from `realSlots`
  and `dummySlots` alone. -/
  dummyIsBit : ∀ i, i < nIn → (w.spent i).isDummy = 0 ∨ (w.spent i).isDummy = 1
  /-- The public bucket's asset id is 64-bit, matching the on-chain `uint64`. -/
  publicAssetRange : w.publicAssetId.val < 2 ^ 64

/-- The **hash-binding layer**: everything that needs Poseidon collision resistance, kept
out of `TxWellFormed` on purpose.

The split is load-bearing. `TxWellFormed` is arithmetic: it depends on `p_prime` and the
Baby Jubjub gadget axioms, and on nothing about the hash. Folding these three fields into it
would make every downstream consequence — `no_asset_creation` included — inherit a
cryptographic hypothesis it does not need. `transact_binding` supplies this layer
separately. -/
structure TxBinding (w : TxWitness depth nIn nOut) : Prop where
  /-- **Output `rho`s are pairwise distinct.** This is the entire purpose of `DeriveRho`:
  two outputs of one transaction can never end up sharing a future nullifier. -/
  rhoDistinct : ∀ j j', j < nOut → j' < nOut → j ≠ j' → (w.out j).rho ≠ (w.out j').rho
  /-- **Membership is binding, not merely existential.** Any other leaf provable at the
  same position under the same root is *this* leaf. Without this, `realSlots`' `member`
  field would say almost nothing. -/
  membershipBinding : ∀ i, i < nIn → (w.spent i).isDummy = 0 →
    ∀ (leaf' : F) (pe' : ℕ → ℕ → F),
      MerkleMember depth leaf' pe' (w.spent i).pathIndices w.merkleRoot →
      (w.spent i).leaf = leaf'
  /-- **The commitment binds the whole note.** A real input's `cm` cannot be reopened to a
  different `(asset_id, value, pk, rho, rcm)`. -/
  commitmentBinding : ∀ i, i < nIn → (w.spent i).isDummy = 0 →
    ∀ a v pk rho rcm : F, a.val < 2 ^ 64 → v.val < 2 ^ 64 →
      noteCommitment a v pk rho rcm = (w.spent i).cm →
      a = (w.spent i).assetId ∧ v = (w.spent i).value ∧ pk = (w.spent i).pk ∧
        rho = (w.spent i).rho ∧ rcm = (w.spent i).rcm

/-- **Soundness of `Transact`.** Any assignment satisfying the constraint system yields a
well-formed transaction. -/
theorem transact_sound {w : TxWitness depth nIn nOut}
    (hnIn : nIn ≤ 3) (hnOut : nOut ≤ 3) (h : TransactSat w) : TxWellFormed w where
  realSlots i hi hreal := spentNote_sound (h.spent_sat i hi) hreal
  dummySlots _i hi hdum := dummyZeroValue_zero h.dummy_zero hi hdum
  sharedRoot := h.spent_root
  outputs j hj := outputNote_sound (h.out_sat j hj)
  rhoDerived := h.rho_derived
  conservation a :=
    perAssetValueBalance_nat h.value_balance hnIn hnOut
      (fun i hi => spentNote_valueRange (h.spent_sat i hi))
      (fun j hj => (outputNote_sound (h.out_sat j hj)).valueRange)
      (rangeCheck64_sound h.pub_in_range) (rangeCheck64_sound h.pub_out_range) a
  depositBinding := h.cv_dep_bound
  compression := polyEval_sound h.compress
  dummyIsBit _i hi := dummyZeroValue_bit h.dummy_zero hi
  publicAssetRange := (num2Bits_sound (le_of_lt two_pow_64_lt_p) h.pub_asset_range).2

/-- **The binding layer**, under the collision-resistance hypothesis.

`hnc` is unsatisfiable (`poseidon_collision`), so this theorem is vacuous read literally.
The assumption is placed in the statement rather than in an axiom so that it cannot leak
into `transact_sound` or anything else; `Lelantos.Model.Poseidon`'s module note records why the
alternatives — an axiom, or a `∨ PoseidonCollision` conclusion — are worse. -/
theorem transact_binding {w : TxWitness depth nIn nOut} (hnc : ¬ PoseidonCollision)
    (hnOut : nOut ≤ 3) (h : TransactSat w) : TxBinding w where
  rhoDistinct := by
    intro j j' hj hj' hne heq
    rw [h.rho_derived j hj, h.rho_derived j' hj'] at heq
    have hsmall : ∀ m : ℕ, m < nOut → m < p := fun m hm =>
      lt_trans (lt_of_lt_of_le hm hnOut) three_lt_p
    exact hne (natCast_inj_of_lt (hsmall j hj) (hsmall j' hj') (deriveRho_inj hnc heq).2)
  membershipBinding := by
    intro i hi hreal leaf' pe' hmem
    have hreal' := spentNote_sound (h.spent_sat i hi) hreal
    have hroot : (w.spent i).root = w.merkleRoot := h.spent_root i hi
    exact (merkleMember_inj hnc hreal'.pathValid (hroot ▸ hreal'.member) hmem).1
  commitmentBinding := by
    intro i hi hreal a v pk rho rcm ha hv hcm
    have hreal' := spentNote_sound (h.spent_sat i hi) hreal
    rw [hreal'.commitment] at hcm
    exact noteCommitment_inj hnc ha hv hreal'.assetRange hreal'.valueRange hcm


/-! ## Corollaries -/

/-- **No asset creation.** If an asset id appears on no input slot and is not the public
bucket's asset, then no output can carry it. Immediate from `conservation`, but worth
stating: it is the "you cannot mint a new asset out of nothing" property, and it holds
over `ℕ` so no wrap-around escape exists. -/
theorem no_asset_creation {w : TxWitness depth nIn nOut}
    (hnIn : nIn ≤ 3) (hnOut : nOut ≤ 3) (h : TransactSat w) (a : F)
    (hnotIn : ∀ i, i < nIn → inAsset w i ≠ a) (hnotPub : w.publicAssetId ≠ a) :
    ∀ j, j < nOut → outAsset w j = a → outValue w j = 0 := by
  classical
  have hcons := (transact_sound hnIn hnOut h).conservation a
  unfold ConservesAtNat indN at hcons
  rw [if_neg hnotPub] at hcons
  have hlhs : ∑ i ∈ Finset.range nIn,
      (inValue w i).val * (if inAsset w i = a then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [if_neg (hnotIn i (Finset.mem_range.mp hi))]; ring
  rw [hlhs] at hcons
  simp only [Nat.mul_zero, Nat.zero_add] at hcons
  intro j hj ha
  have hzero : ∑ k ∈ Finset.range nOut,
      (outValue w k).val * (if outAsset w k = a then 1 else 0) = 0 := by omega
  have hterm := (Finset.sum_eq_zero_iff.mp hzero) j (Finset.mem_range.mpr hj)
  rw [if_pos ha, mul_one] at hterm
  exact val_inj (by simpa using hterm)

/-- **Public-input binding at the transaction level.** If two transactions with *different*
public inputs are accepted against the same `(z, y)`, then `z` is one of at most
`piCount - 1` field elements — 30 out of `p ≈ 2^253.6` for the deployed instance.

The security reading needs `ContractObligations.challenge_is_fiat_shamir`: the prover must
not be able to pick `z` after fixing the coefficients. The circuit cannot enforce that, so
it is a hypothesis, not a conclusion. -/
theorem transact_pi_binding {w w' : TxWitness depth nIn nOut}
    (h : TransactSat w) (h' : TransactSat w')
    (hz : w.z = w'.z) (hy : w.y = w'.y)
    (hne : ∃ k, k < piCount nIn nOut ∧ txCoeffs w k ≠ txCoeffs w' k) :
    w.z ∈ ({z : F | polyEval (txCoeffs w) (piCount nIn nOut) z
              = polyEval (txCoeffs w') (piCount nIn nOut) z} : Set F).toFinset
    ∧ ({z : F | polyEval (txCoeffs w) (piCount nIn nOut) z
              = polyEval (txCoeffs w') (piCount nIn nOut) z} : Set F).toFinset.card
        ≤ piCount nIn nOut - 1 := by
  classical
  refine ⟨?_, polyEval_binding (by unfold piCount; omega) hne⟩
  simp only [Set.mem_toFinset, Set.mem_setOf_eq]
  have e1 := polyEval_sound h.compress
  have e2 := polyEval_sound h'.compress
  rw [← e1, hy, e2, hz]

/-- **Public-input binding, stated per named field.** `transact_pi_binding` needs a
coefficient index at which the two transactions differ. This form takes the difference where
it is actually observed — in one named public input — and produces the index from
`slotIndex`.

So: two accepted transactions that disagree about the Merkle root, any nullifier, any output
commitment, the public bucket, any value commitment, the addresses, or any clue field cannot
share `(z, y)` unless `z` is one of at most `piCount - 1` field elements. -/
theorem transact_pi_binding_slot {w w' : TxWitness depth nIn nOut}
    (h : TransactSat w) (h' : TransactSat w')
    (hz : w.z = w'.z) (hy : w.y = w'.y)
    {s : PISlot} (hs : s.InRange nIn nOut) (hne : slotValue w s ≠ slotValue w' s) :
    w.z ∈ ({z : F | polyEval (txCoeffs w) (piCount nIn nOut) z
              = polyEval (txCoeffs w') (piCount nIn nOut) z} : Set F).toFinset
    ∧ ({z : F | polyEval (txCoeffs w) (piCount nIn nOut) z
              = polyEval (txCoeffs w') (piCount nIn nOut) z} : Set F).toFinset.card
        ≤ piCount nIn nOut - 1 :=
  transact_pi_binding h h' hz hy
    ⟨slotIndex nIn nOut s, slotIndex_lt hs, by
      rw [txCoeffs_slotIndex w hs, txCoeffs_slotIndex w' hs]; exact hne⟩

/-! ## The deployed instances

`transact_sound` is stated for `nIn ≤ 3`, `nOut ≤ 3` — the bound comes from
`perAssetValueBalance_nat`, where it is what keeps each side of the balance equation below
`p`. The repository ships exactly two shapes, and both sit inside it. -/

/-- `Transact(10, 2, 2)` — `src/2x2.circom:28`. -/
abbrev Transact2x2 := TxWitness 10 2 2

/-- `Transact(10, 3, 3)` — `src/3x3.circom:38`. NOT DEPLOYED; see the circom header. -/
abbrev Transact3x3 := TxWitness 10 3 3

/-- **Soundness of the deployed `2x2` instance.** -/
theorem transact2x2_sound {w : Transact2x2} (h : TransactSat w) : TxWellFormed w :=
  transact_sound (by norm_num) (by norm_num) h

/-- **Soundness of the deployed `3x3` instance.** -/
theorem transact3x3_sound {w : Transact3x3} (h : TransactSat w) : TxWellFormed w :=
  transact_sound (by norm_num) (by norm_num) h

/-- **The `2x2` binding layer**, on the same unsatisfiable hypothesis. -/
theorem transact2x2_binding {w : Transact2x2} (hnc : ¬ PoseidonCollision)
    (h : TransactSat w) : TxBinding w :=
  transact_binding hnc (by norm_num) h

/-- **The `3x3` binding layer.** -/
theorem transact3x3_binding {w : Transact3x3} (hnc : ¬ PoseidonCollision)
    (h : TransactSat w) : TxBinding w :=
  transact_binding hnc (by norm_num) h

end Lelantos
