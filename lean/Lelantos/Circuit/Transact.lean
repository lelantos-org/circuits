import Lelantos.Circuit.Layout
import Lelantos.Gadgets.PolyEval
import Lelantos.Gadgets.CoeffDigest

/-!
# `src/lib/transact.circom` — the whole transact circuit

`Transact(DEPTH, N_IN, N_OUT)` is wiring: the per-slot logic lives in `SpentNote` and
`OutputNote`, and this file composes it with the transparent bucket, the value balance and
the public-input compression.

This module is the constraint system and what it proves. Its signals are
`Lelantos.Circuit.Witness`, its coefficient order `Lelantos.Circuit.Layout`, and what the
contract must check `Lelantos.Circuit.Obligations`.

`transact_sound` is the top-level result. Given any assignment satisfying the modelled
constraint system it produces `TxWellFormed`, whose fields are the security properties:

* every non-dummy input slot proves ownership and Merkle membership,
* every dummy input slot carries value `0`,
* every input slot is opened against the same root,
* every output slot is well-formed and its `rho` is the Orchard-style derivation,
* for every asset id in the field, value is conserved as an equation over `ℕ`,
* the transparent bucket is 64-bit in both words and names no asset when nothing leaves,
* the public `digest` is `CoeffDigest` of the coefficient vector,
* and the public `y` is the polynomial evaluation of that vector at a nonzero `z`.

All of these are arithmetic: `transact_sound` depends on `p_prime` and assumes nothing
about Poseidon beyond its being a function.

The hash-binding properties (pairwise-distinct output `rho`s, binding Merkle membership,
and a commitment pinning its whole note) are in the separate `TxBinding`, proved by
`transact_binding` from an explicit collision-resistance hypothesis. That hypothesis is
unsatisfiable (`poseidon_collision`), so `TxBinding` is assumed rather than proved; keeping
it out of `TxWellFormed` prevents the assumption from reaching conservation and the other
consequences. See `Lelantos.Model.Poseidon`.

## Not claimed

* There is no value commitment and no curve arithmetic in the circuit, so there is no
  statement about either. Conservation comes from `PerAssetValueBalance` alone.
* `rho` uniqueness across transactions reduces to the contract enforcing nullifier
  uniqueness, so it appears in `ContractObligations`, not as a theorem.
* Nothing stops one note from filling two input slots: each slot is opened against the
  shared root independently, and the balance sums count the duplicate once per slot. The
  circuit leaves it to the consumer (`src/4x6.circom:60-62`), and
  `ContractObligations.nullifiers_distinct` is that obligation stated.
* The address words, the FMD clue fields and the payload digest are not signals of the
  circuit. They are bound through the challenge, which is the contract's business.
* That the calldata a verifier accepts is the calldata the witness describes is not a
  theorem here. See "Why the compression binds" below for the two halves that are proved
  and the Fiat-Shamir step that is not.
* Everything is modulo the axioms in `Lelantos.Meta.Assumptions`.
-/

namespace Lelantos

variable {depth nIn nOut : ℕ}

/-- The constraint system of `Transact(depth, nIn, nOut)`. -/
structure TransactSat (w : TxWitness depth nIn nOut) : Prop where
  /-- `src/lib/transact.circom:76-91` — each `SpentNote`, wired to its inputs. -/
  spent_sat : ∀ i, i < nIn → SpentNoteSat (w.spent i)
  /-- `:90` — `spent[i].root <== merkle_root`: every slot opens against the shared root. -/
  spent_root : ∀ i, i < nIn → (w.spent i).root = w.merkleRoot
  /-- `:73, 94-95` — `DummyZeroValue(N_IN)` over `in_is_dummy` and `in_value`. -/
  dummy_zero : DummyZeroValueSat nIn (fun i => (w.spent i).isDummy) (inValue w)
  /-- `:111` — `dummy_acc[0] <== 0`.

  `:110-118` together say at least one input slot is real. `MerkleProofOrDummy` skips the
  root comparison on a dummy slot, so with every slot dummy no spend constraint reads
  `merkleRoot`. With one real slot the root is the output of a Poseidon chain over a note
  the prover owns. -/
  dummy_acc_base : w.dummyAcc 0 = 0
  /-- `:112-114` — `dummy_acc[i + 1] <== dummy_acc[i] + in_is_dummy[i]`. -/
  dummy_acc_step : ∀ i, i < nIn → w.dummyAcc (i + 1) = w.dummyAcc i + (w.spent i).isDummy
  /-- `:115-117` — `all_dummy = IsEqual()` on the count and `N_IN`. -/
  dummy_all_eq : IsEqualSat (w.dummyAcc nIn) (nIn : F) w.dummyAllInv w.dummyAllOut
  /-- `:118` — `all_dummy.out === 0`. -/
  not_all_dummy : w.dummyAllOut = 0
  /-- `:127-130` — output `rho` is the Orchard-style derivation from `nullifier[0]`. -/
  rho_derived : ∀ j, j < nOut → (w.out j).rho = deriveRho (w.spent 0).nullifier (j : F)
  /-- `:132-138` — each `OutputNote`, wired to its inputs. -/
  out_sat : ∀ j, j < nOut → OutputNoteSat (w.out j)
  /-- `:144-145` — `rng_pub_asset`: the bucket's asset id is 64-bit, matching the on-chain
  `uint64`. -/
  pub_asset_range : RangeCheck64Sat w.publicAssetId w.pubAssetBits
  /-- `:147-148` — `rng_pub_out`: the withdrawn amount is 64-bit; it is a term of the
  conservation sums. -/
  pub_out_range : RangeCheck64Sat w.publicOut w.pubOutBits
  /-- `:158-159` — `pub_out_z = IsZero()` on `public_out`. -/
  pub_out_isZero : IsZeroSat w.publicOut w.pubOutInv w.pubOutIsZero
  /-- `:160` — `pub_out_z.out * public_asset_id === 0`: a transaction that withdraws
  nothing names no asset. One constraint, not a comparison of two `IsZero` outputs. -/
  transfer_names_no_asset : w.pubOutIsZero * w.publicAssetId = 0
  /-- `:163-173` — the conservation check, `vbal`. -/
  value_balance : PerAssetValueBalanceSat nIn nOut (inAsset w) (inValue w) (outAsset w)
    (outValue w) w.publicAssetId w.publicOut w.vbPubInv w.vbPubEq
    w.vbInInv w.vbInEq w.vbOutInv w.vbOutEq w.vbInTerm w.vbOutTerm w.vbLhs w.vbRhs
  /-- `src/lib/poly_eval.circom:165-169` — `dg = CoeffDigest(N)` over the ordered `prefix`,
  the coefficient vector, with `digest <== dg.out`. The circuit's public output is that
  signal: `digest <== pe.digest`, at `src/lib/transact.circom:188`. It is computed
  in-circuit, not taken as an input, and it is not a `PolyEval` coefficient. -/
  digest_def : CoeffDigestSat (piCount nIn nOut) (txCoeffs w) w.dgBlock w.digest
  /-- `src/lib/poly_eval.circom:171-176` — public-input compression: `pe = PolyEval(N)` over
  the same `prefix`. The compressor is instantiated and wired, with `y <== pe.y`, at
  `src/lib/transact.circom:176-187`. -/
  compress : PolyEvalSat (piCount nIn nOut) (txCoeffs w) w.z w.zInv w.zIsZero w.peAcc w.y

/-- What a satisfying assignment proves. -/
structure TxWellFormed (w : TxWitness depth nIn nOut) : Prop where
  /-- Non-dummy inputs are owned, in-tree notes. -/
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
      w.publicAssetId w.publicOut a
  /-- The public `digest` is the `CoeffDigest` fold of the coefficient vector. -/
  digest : w.digest = coeffDigest (txCoeffs w) (piCount nIn nOut)
  /-- The public `y` is the evaluation of the same vector at the challenge. -/
  compression : w.y = polyEval (txCoeffs w) (piCount nIn nOut) w.z
  /-- The challenge is nonzero, so every coefficient reaches `y`. -/
  challengeNonzero : w.z ≠ 0
  /-- **Every input slot is covered by exactly one of the two cases above.** Without this
  the conclusion is silent about a slot whose `is_dummy` is neither `0` nor `1`, and
  "each input is a real note or carries no value" would not follow from `realSlots`
  and `dummySlots` alone. -/
  dummyIsBit : ∀ i, i < nIn → (w.spent i).isDummy = 0 ∨ (w.spent i).isDummy = 1
  /-- Every input slot's asset id is 64-bit, dummies included. -/
  inputAssetRange : ∀ i, i < nIn → (w.spent i).assetId.val < 2 ^ 64
  /-- The public bucket's asset id is 64-bit, matching the on-chain `uint64`. -/
  publicAssetRange : w.publicAssetId.val < 2 ^ 64
  /-- The withdrawn amount is 64-bit. -/
  publicOutRange : w.publicOut.val < 2 ^ 64
  /-- **A transaction that withdraws nothing names no asset.** -/
  transferNamesNoAsset : w.publicOut = 0 → w.publicAssetId = 0
  /-- **At least one input slot is real**, so the advertised root is the top of a Poseidon
  chain over a note the prover owns. -/
  someRealInput : ∃ i, i < nIn ∧ (w.spent i).isDummy = 0

/-- The **hash-binding layer**: everything that needs Poseidon collision resistance, kept
out of `TxWellFormed`.

`TxWellFormed` is arithmetic: it depends on `p_prime` and on nothing about the hash.
Folding these three fields into it would make every downstream consequence,
`no_asset_creation` included, inherit an unneeded cryptographic hypothesis.
`transact_binding` supplies this layer separately. -/
structure TxBinding (w : TxWitness depth nIn nOut) : Prop where
  /-- **Output `rho`s are pairwise distinct**, which is the purpose of `DeriveRho`: two
  outputs of one transaction cannot share a future nullifier. -/
  rhoDistinct : ∀ j j', j < nOut → j' < nOut → j ≠ j' → (w.out j).rho ≠ (w.out j').rho
  /-- **Membership is binding, not merely existential.** Any other leaf provable at the
  same position under the same root is this slot's commitment. Without this, `realSlots`'
  `member` field only asserts that some chain exists. -/
  membershipBinding : ∀ i, i < nIn → (w.spent i).isDummy = 0 →
    ∀ (leaf' : F) (pe' : ℕ → ℕ → F),
      MerkleMember depth leaf' pe' (w.spent i).pathIndices w.merkleRoot →
      (w.spent i).cm = leaf'
  /-- **The commitment binds the whole note.** An input's `cm` cannot be reopened to a
  different `(asset_id, value, pk, rho, rcm)`. It holds on dummy slots too: both range
  checks and the commitment are unconditional. -/
  commitmentBinding : ∀ i, i < nIn →
    ∀ a v pk rho rcm : F, a.val < 2 ^ 64 → v.val < 2 ^ 64 →
      noteCm a v pk rho rcm = (w.spent i).cm →
      a = (w.spent i).assetId ∧ v = (w.spent i).value ∧ pk = (w.spent i).pk ∧
        rho = (w.spent i).rho ∧ rcm = (w.spent i).rcm

/-- With every slot dummy the running count is the slot index, as a field element. -/
private theorem dummyAcc_eq_of_all {depth nIn nOut : ℕ} {w : TxWitness depth nIn nOut}
    (h : TransactSat w) (hall : ∀ i, i < nIn → (w.spent i).isDummy = 1) :
    ∀ k, k ≤ nIn → w.dummyAcc k = (k : F) := by
  intro k
  induction k with
  | zero => intro _; simpa using h.dummy_acc_base
  | succ m ih =>
    intro hm
    rw [h.dummy_acc_step m hm, ih (Nat.le_of_lt hm), hall m hm]
    push_cast
    ring

/-! ## The transparent bucket -/

/-- **A transaction that withdraws nothing names no asset.** Direct from
`pub_out_z.out * public_asset_id === 0` (`src/lib/transact.circom:160`): `IsZero` pins its
output to `1` at `public_out = 0`. A shielded transfer therefore publishes asset id `0`
rather than the id it moves. -/
theorem publicBucket_zero_asset {w : TxWitness depth nIn nOut} (h : TransactSat w)
    (hout : w.publicOut = 0) : w.publicAssetId = 0 := by
  have hz := isZero_sound h.pub_out_isZero
  rw [if_pos hout] at hz
  have hmul := h.transfer_names_no_asset
  rwa [hz, one_mul] at hmul

/-- **The converse needs no constraint.** At `public_asset_id = 0` the conservation
equation for asset id `0` reads `Σ in_value[asset = 0] = Σ out_value[asset = 0] +
public_out`. Outputs reject id `0`, a real input rejects it, and a dummy input carries value
`0`, so both sums vanish and `public_out = 0` follows. This is the argument at
`src/lib/transact.circom:154-157`.

It goes through in the field, so it needs neither the slot bound nor a range check. -/
theorem publicBucket_zero_out {w : TxWitness depth nIn nOut} (h : TransactSat w)
    (hasset : w.publicAssetId = 0) : w.publicOut = 0 := by
  have hcons := perAssetValueBalance_all_assets h.value_balance 0
  unfold ConservesAt at hcons
  have hin : ∑ i ∈ Finset.range nIn, inValue w i * ind (inAsset w i = 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have hi' := Finset.mem_range.mp hi
      rcases dummyZeroValue_bit h.dummy_zero hi' with h0 | h1
      · have hnz : inAsset w i ≠ 0 := (spentNote_sound (h.spent_sat i hi') h0).assetNonzero
        rw [ind, if_neg hnz, mul_zero]
      · rw [dummyZeroValue_zero h.dummy_zero hi' h1, zero_mul]
  have hout : ∑ j ∈ Finset.range nOut, outValue w j * ind (outAsset w j = 0) = 0 :=
    Finset.sum_eq_zero fun j hj => by
      have hnz : outAsset w j ≠ 0 :=
        (outputNote_sound (h.out_sat j (Finset.mem_range.mp hj))).assetNonzero
      rw [ind, if_neg hnz, mul_zero]
  rw [hin, hout, ind, if_pos hasset, mul_one, add_zero] at hcons
  exact hcons.symm

/-- The transparent bucket is empty exactly when it names no asset. -/
theorem publicBucket_zero_iff {w : TxWitness depth nIn nOut} (h : TransactSat w) :
    w.publicOut = 0 ↔ w.publicAssetId = 0 :=
  ⟨publicBucket_zero_asset h, publicBucket_zero_out h⟩

/-! ## Soundness -/

/-- **Soundness of `Transact`.** Any assignment satisfying the constraint system yields a
well-formed transaction. -/
theorem transact_sound {w : TxWitness depth nIn nOut}
    (hnIn : nIn ≤ 7) (hnOut : nOut ≤ 7) (h : TransactSat w) : TxWellFormed w where
  realSlots i hi hreal := spentNote_sound (h.spent_sat i hi) hreal
  dummySlots _i hi hdum := dummyZeroValue_zero h.dummy_zero hi hdum
  sharedRoot := h.spent_root
  outputs j hj := outputNote_sound (h.out_sat j hj)
  rhoDerived := h.rho_derived
  conservation a :=
    perAssetValueBalance_nat h.value_balance hnIn hnOut
      (fun i hi => spentNote_valueRange (h.spent_sat i hi))
      (fun j hj => (outputNote_sound (h.out_sat j hj)).valueRange)
      (rangeCheck64_sound h.pub_out_range) a
  digest := coeffDigest_sound h.digest_def
  compression := polyEval_sound h.compress
  challengeNonzero := polyEvalSat_z_ne_zero h.compress
  dummyIsBit _i hi := dummyZeroValue_bit h.dummy_zero hi
  inputAssetRange i hi := spentNote_assetRange (h.spent_sat i hi)
  publicAssetRange := rangeCheck64_sound h.pub_asset_range
  publicOutRange := rangeCheck64_sound h.pub_out_range
  transferNamesNoAsset := publicBucket_zero_asset h
  someRealInput := by
    -- The comparator says `dummyAllOut = 1` exactly when the count reaches `nIn`, and the
    -- circuit forces it to 0. So the count cannot reach `nIn`, and by `dummyIsBit` the only
    -- way to fall short is a slot at 0.
    by_contra hcon
    push_neg at hcon
    have hall : ∀ i, i < nIn → (w.spent i).isDummy = 1 := by
      intro i hi
      rcases dummyZeroValue_bit h.dummy_zero hi with h0 | h1
      · exact absurd h0 (hcon i hi)
      · exact h1
    have hout := isEqual_sound h.dummy_all_eq
    rw [dummyAcc_eq_of_all h hall nIn le_rfl, if_pos rfl, h.not_all_dummy] at hout
    exact zero_ne_one hout

/-- **The binding layer**, under the collision-resistance hypothesis.

`hnc` is unsatisfiable (`poseidon_collision`), so this theorem is vacuous read literally.
The assumption is placed in the statement rather than in an axiom so that it does not reach
`transact_sound` or anything else; `Lelantos.Model.Poseidon`'s module note explains why the
alternatives (an axiom, or a `∨ PoseidonCollision` conclusion) are unsuitable. -/
theorem transact_binding {w : TxWitness depth nIn nOut} (hnc : ¬ PoseidonCollision)
    (hnOut : nOut ≤ 7) (h : TransactSat w) : TxBinding w where
  rhoDistinct := by
    intro j j' hj hj' hne heq
    rw [h.rho_derived j hj, h.rho_derived j' hj'] at heq
    have hsmall : ∀ m : ℕ, m < nOut → m < p := fun m hm =>
      lt_trans (lt_of_lt_of_le hm hnOut) seven_lt_p
    exact hne (natCast_inj_of_lt (hsmall j hj) (hsmall j' hj') (deriveRho_inj hnc heq).2)
  membershipBinding := by
    intro i hi hreal leaf' pe' hmem
    have hreal' := spentNote_sound (h.spent_sat i hi) hreal
    have hroot : (w.spent i).root = w.merkleRoot := h.spent_root i hi
    exact (merkleMember_inj hnc hreal'.pathValid (hroot ▸ hreal'.member) hmem).1
  commitmentBinding := by
    intro i hi a v pk rho rcm ha hv hcm
    have hs := h.spent_sat i hi
    rw [spentNote_commitment hs] at hcm
    exact noteCm_inj hnc ha hv (spentNote_assetRange hs) (spentNote_valueRange hs) hcm


/-! ## Corollaries -/

/-- **No asset creation.** If an asset id appears on no input slot, then no output can
carry a non-zero value of it. Immediate from `conservation`; it holds over `ℕ`, so no
wrap-around is possible.

The transparent bucket needs no hypothesis: it sits on the output side, so it can only
take value out. -/
theorem no_asset_creation {w : TxWitness depth nIn nOut}
    (hnIn : nIn ≤ 7) (hnOut : nOut ≤ 7) (h : TransactSat w) (a : F)
    (hnotIn : ∀ i, i < nIn → inAsset w i ≠ a) :
    ∀ j, j < nOut → outAsset w j = a → outValue w j = 0 := by
  classical
  have hcons := (transact_sound hnIn hnOut h).conservation a
  unfold ConservesAtNat indN at hcons
  have hlhs : ∑ i ∈ Finset.range nIn,
      (inValue w i).val * (if inAsset w i = a then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [if_neg (hnotIn i (Finset.mem_range.mp hi))]; ring
  rw [hlhs] at hcons
  intro j hj ha
  have hzero : ∑ k ∈ Finset.range nOut,
      (outValue w k).val * (if outAsset w k = a then 1 else 0) = 0 := by omega
  have hterm := (Finset.sum_eq_zero_iff.mp hzero) j (Finset.mem_range.mpr hj)
  rw [if_pos ha, mul_one] at hterm
  exact val_inj (by simpa using hterm)

/-- **No withdrawal of an asset nobody spent.** If an asset id appears on no input slot and
the transparent bucket names it, nothing is withdrawn. -/
theorem no_asset_withdrawal {w : TxWitness depth nIn nOut}
    (hnIn : nIn ≤ 7) (hnOut : nOut ≤ 7) (h : TransactSat w)
    (hnotIn : ∀ i, i < nIn → inAsset w i ≠ w.publicAssetId) : w.publicOut = 0 := by
  classical
  have hcons := (transact_sound hnIn hnOut h).conservation w.publicAssetId
  unfold ConservesAtNat indN at hcons
  have hlhs : ∑ i ∈ Finset.range nIn,
      (inValue w i).val * (if inAsset w i = w.publicAssetId then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [if_neg (hnotIn i (Finset.mem_range.mp hi))]; ring
  rw [hlhs, if_pos rfl, mul_one] at hcons
  exact val_inj (by simp only [ZMod.val_zero]; omega)

/-! ## The compression

The verifier's public signals are `(y, digest, z)`. `y` and `digest` are both functions of
one coefficient vector, `txCoeffs w`: its evaluation at `z`, and its `CoeffDigest`.
-/

/-- **The public digest is the digest of the coefficient vector.** Unconditional: it is
`coeffDigest_sound` on the circuit's own `CoeffDigest` instance. -/
theorem transact_digest_public {w : TxWitness depth nIn nOut} (h : TransactSat w) :
    w.digest = coeffDigest (txCoeffs w) (piCount nIn nOut) :=
  coeffDigest_sound h.digest_def

/-- **Public-input binding at the transaction level.** If two transactions with different
coefficient vectors are accepted against the same `(z, y)`, then `z` is one of at most
`piCount - 1` field elements, 12 out of `p ≈ 2^253.6` at `Transact(11, 4, 6)`.

This counts challenges for two vectors that are both fixed. It is the Schwartz-Zippel half
of the binding argument; see "Why the compression binds" below for what fixes the vectors
before the challenge. -/
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
coefficient index at which the two transactions differ. This form takes the difference in
one named public input and produces the index from `slotIndex`.

Two accepted transactions that disagree about the Merkle root, any nullifier, any output
commitment or the public bucket cannot share `(z, y)` unless `z` is one of at most
`piCount - 1` field elements. -/
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

/-- **Public-input binding against calldata.** Let `c` be the coefficient vector a verifier
read from calldata, and suppose its evaluation at the proof's challenge is the proof's `y`,
which is what the contract checks. If `c` differs from the witness's coefficient vector
anywhere, then `z` is one of at most `piCount - 1` field elements.

Unconditional, and again a count for two fixed vectors: `c` need not come from a
satisfying witness. -/
theorem transact_calldata_pi_binding {w : TxWitness depth nIn nOut} (h : TransactSat w)
    {c : ℕ → F} (hy : polyEval c (piCount nIn nOut) w.z = w.y)
    (hne : ∃ k, k < piCount nIn nOut ∧ c k ≠ txCoeffs w k) :
    w.z ∈ ({z : F | polyEval c (piCount nIn nOut) z
              = polyEval (txCoeffs w) (piCount nIn nOut) z} : Set F).toFinset
    ∧ ({z : F | polyEval c (piCount nIn nOut) z
              = polyEval (txCoeffs w) (piCount nIn nOut) z} : Set F).toFinset.card
        ≤ piCount nIn nOut - 1 := by
  classical
  refine ⟨?_, polyEval_binding (by unfold piCount; omega) hne⟩
  simp only [Set.mem_toFinset, Set.mem_setOf_eq]
  rw [hy, polyEval_sound h.compress]

example : piCount 4 6 - 1 = 12 := by norm_num [piCount]

/-! ## Why the compression binds

The contract reads the digest word `d` from calldata, derives
`z = keccak(coefficients, d, challenge-only words) mod r`, computes `y` over the calldata
coefficients `c`, and verifies the proof against the public signals `(y, d, z)`. A
verifying proof shows a witness `w` with `CoeffDigest(txCoeffs w) = d` and
`Σ_k (txCoeffs w)_k · z^k = y`. (`r` is the BN254 scalar-field modulus, `p` in this
development.)

The evaluation alone would not bind. `z` is a circuit input derived from calldata the
prover authored, so the prover reads it before choosing a witness, and `PolyEval` is affine
in each coefficient (`polyEval_forge`). What binds is that the witness vector is committed
before the challenge exists:

* `d` is in the preimage of `z`, and under collision resistance of the Poseidon(5) fold
  the prover knows only one coefficient vector with digest `d`. So the witness vector is
  fixed before `z`.
* The calldata vector `c` is in the preimage too. If `txCoeffs w ≠ c`, the two are
  distinct polynomials of degree `< N` fixed before a random `z`, and agree there with
  probability at most `(N − 1)/r`: `12/r` at the shipped shape.

This is commit-then-challenge Fiat-Shamir. Its assumptions are collision resistance of
Poseidon(5), which is the † hypothesis, and keccak256 behaving as a random oracle.

What this development proves:

* `transact_digest_public` — unconditional. The public `digest` of a satisfying witness is
  `coeffDigest` of its coefficient vector.
* `txCoeffs_determined_by_digest` † — two satisfying witnesses with the same public digest
  have the same coefficient vector.
* `transact_calldata_binding` † — a calldata vector whose `coeffDigest` is the public
  digest of a satisfying witness is that witness's coefficient vector. Honest calldata
  satisfies the hypothesis. This is the "commitment opens to one vector" half.
* `transact_pi_binding`, `transact_calldata_pi_binding` — unconditional. Two distinct
  coefficient vectors evaluate equally on at most `piCount − 1` challenges. This is the
  Schwartz-Zippel half.

What it does not prove is the step that joins the two halves: from "the digest binds the
vector (†)" and "distinct vectors agree on at most `N − 1` challenges" to "no forged
calldata verifies except with negligible probability". That is the standard Fiat-Shamir
forking / random-oracle argument. It quantifies over provers and treats keccak256 as a
random oracle, and this development models neither. It is prose and is not formalised.

Three conditions on the contract, each of which the argument needs and none of which is a
property of the circuit (`ContractObligations`):

* the calldata digest word is passed to the verifier unmodified, as the `digest` public
  signal;
* that word is in the keccak preimage of `z`. Left out, the prover can choose the witness,
  and so the digest, after seeing `z`;
* every coefficient is in the keccak preimage of `z`.

The digest is not a coefficient: it is not evaluated into `y`.

Each coefficient is also constrained on its own, which is what gives each word a meaning.
The digest is what ties the proof to the calldata.

| slot | constrained by |
|---|---|
| `merkleRoot` | `spent_sat` — Merkle membership of at least one real input, `not_all_dummy` |
| `nullifier i` | `SpentNoteSat.nf_def`, a Poseidon image |
| `outCm j` | `OutputNoteSat.cm_def`, a Poseidon image |
| `publicAssetId` | `pub_asset_range` (64 bits), `transfer_names_no_asset`, `value_balance` |
| `publicOut` | `pub_out_range` (64 bits) and `value_balance` |

The address words, the FMD clue triples and the payload digest are not in the table
because they are not coefficients. `4x6.circom` has no signal for them; `PubInputs.sol`
hashes them into `z`, so altering one changes `z` and the proof, made for another `z`,
fails. The coefficient digest does not absorb them: there is no witness copy of them to
disagree with calldata.
-/

/-- **A calldata vector with the witness's digest is the witness's vector**, under Poseidon
collision resistance. Let `c` be the coefficient vector read from calldata. If its
`CoeffDigest` equals the public `digest` of a satisfying witness, then `c` agrees with that
witness's coefficient vector on every coefficient.

The hypothesis is what honest calldata satisfies: the prover writes the digest of the
coefficients it also writes. The conclusion is the "commitment opens to one vector" half of
the binding argument. It does not say that calldata which verifies satisfies the
hypothesis; that is the Fiat-Shamir step, which is not formalised.

`hcr` is unsatisfiable (`poseidon_collision`); this is an assumption recorded in the
statement. -/
theorem transact_calldata_binding (hcr : ¬ PoseidonCollision)
    {w : TxWitness depth nIn nOut} (h : TransactSat w) {c : ℕ → F}
    (hd : coeffDigest c (piCount nIn nOut) = w.digest) :
    ∀ k, k < piCount nIn nOut → c k = txCoeffs w k :=
  digest_inj hcr (hd.trans (transact_digest_public h))

/-- **The public digest determines the coefficient vector**, under Poseidon collision
resistance. Two satisfying witnesses with equal public digests agree on every coefficient:
the digest is `CoeffDigest` of the vector in both (`transact_digest_public`), and
`digest_inj` turns equal digests into equal vectors.

`hcr` is unsatisfiable (`poseidon_collision`); this is an assumption recorded in the
statement. -/
theorem txCoeffs_determined_by_digest (hcr : ¬ PoseidonCollision)
    {w w' : TxWitness depth nIn nOut} (h : TransactSat w) (h' : TransactSat w')
    (hd : w.digest = w'.digest) :
    ∀ k, k < piCount nIn nOut → txCoeffs w k = txCoeffs w' k :=
  transact_calldata_binding hcr h' ((transact_digest_public h).symm.trans hd)

/-- …stated per named public input: equal digests mean the same root, the same nullifiers,
the same output commitments and the same transparent bucket. -/
theorem slotValue_determined_by_digest (hcr : ¬ PoseidonCollision)
    {w w' : TxWitness depth nIn nOut} (h : TransactSat w) (h' : TransactSat w')
    (hd : w.digest = w'.digest) {s : PISlot} (hs : s.InRange nIn nOut) :
    slotValue w s = slotValue w' s := by
  rw [← txCoeffs_slotIndex w hs, ← txCoeffs_slotIndex w' hs]
  exact txCoeffs_determined_by_digest hcr h h' hd _ (slotIndex_lt hs)

/-! ## The instantiated shapes

`transact_sound` is stated for `nIn ≤ 7`, `nOut ≤ 7`. The bound comes from
`perAssetValueBalance_nat`, where it keeps each side of the balance equation below `p`
(rounding to `8 · 2^64`); the deployed shape is within it. The digest fold has no arity
cap, so it does not affect the bound. -/

/-- `Transact(11, 4, 6)` — `src/4x6.circom`. **The target shape.**

Six outputs so a withdrawal's change lands on the denomination ladder in one spend rather
than leaving an off-ladder remainder for a follow-up transfer; four inputs because an input
slot costs several times an output slot, carrying a Merkle path the output side does not.
Depth 11 because an unused output slot is a real value-0 leaf, so six outputs would
otherwise cut the tree's lifetime by a third.

It requires `≤ 6` slots per side; `transact_sound` is stated at 7, the limit of the proof. -/
abbrev Transact4x6 := TxWitness 11 4 6

/-- **Soundness of the `4x6` instance.** -/
theorem transact4x6_sound {w : Transact4x6} (h : TransactSat w) : TxWellFormed w :=
  transact_sound (by norm_num) (by norm_num) h

/-- **The `4x6` binding layer.** -/
theorem transact4x6_binding {w : Transact4x6} (hnc : ¬ PoseidonCollision)
    (h : TransactSat w) : TxBinding w :=
  transact_binding hnc (by norm_num) h


end Lelantos
