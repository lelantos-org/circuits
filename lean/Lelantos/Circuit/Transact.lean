import Lelantos.Circuit.Witness
import Lelantos.Gadgets.PointBalance
import Lelantos.Gadgets.PolyEval

/-!
# `src/lib/transact.circom` — the whole transact circuit

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
* and `y` is the polynomial evaluation of the declared 46-slot layout at `z`.

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
* **`y` is not claimed to determine the transaction.** Nothing here proves it does.
  `polyEval_forge` shows what would follow if it did not: one coefficient the rest of the
  system leaves free is one linear equation in one unknown, and `y` becomes whatever the
  contract asks for. What rules that out is the *layout* — every slot it carries is pinned
  by a constraint outside `TransactCompressN` — and that is a table below, checked by eye,
  not a theorem. Compression is binding only under
  `ContractObligations.challenge_binds_witness` and only while that table holds.
* Everything is modulo the axioms in `Lelantos.Meta.Assumptions`.
-/

namespace Lelantos

variable {depth nIn nOut : ℕ}

/-- The constraint system of `Transact(depth, nIn, nOut)`. -/
structure TransactSat (w : TxWitness depth nIn nOut) : Prop where
  /-- `src/lib/transact.circom:90-122` — each spent slot, bound to the shared root. -/
  spent_sat : ∀ i, i < nIn → SpentNoteSat (w.spent i)
  spent_root : ∀ i, i < nIn → (w.spent i).root = w.merkleRoot
  /-- `:87-89` — `DummyZeroValue(N_IN)`. -/
  dummy_zero : DummyZeroValueSat nIn (fun i => (w.spent i).isDummy) (inValue w)
  /-- `src/lib/transact.circom:129-140` — at least one input slot is real.

  `MerkleProofOrDummy` skips the root comparison on a dummy slot, so with every slot dummy
  nothing reads `merkleRoot` and it becomes a free coefficient — the one slot of the layout
  a prover could set to a chosen field element and solve `y = Σ c_k z^k` with. See the
  pinning section below. -/
  dummy_acc_base : w.dummyAcc 0 = 0
  dummy_acc_step : ∀ i, i < nIn → w.dummyAcc (i + 1) = w.dummyAcc i + (w.spent i).isDummy
  dummy_all_eq : IsEqualSat (w.dummyAcc nIn) (nIn : F) w.dummyAllInv w.dummyAllOut
  not_all_dummy : w.dummyAllOut = 0
  /-- `:151-154` — output `rho` is the Orchard-style derivation from `nullifier[0]`. -/
  rho_derived : ∀ j, j < nOut → (w.out j).rho = deriveRho (w.spent 0).nullifier (j : F)
  /-- `:156-166` — each output slot. -/
  out_sat : ∀ j, j < nOut → OutputNoteSat (w.out j)
  /-- `:168-169` — the forwarded deposit commitments are the ones the outputs computed. -/
  cv_dep_bound : ∀ j, j < nOut → w.outCvDep j = (w.out j).cvDep
  /-- `:175-189` — the public bucket: generator, two `ValueTimesGen`s (each a
  `RangeCheck64` plus a `ValueScalarMul`, `src/lib/balance.circom:24-41`). -/
  pub_gen : w.pubGen = coords (assetGen w.publicAssetId)
  /-- `HashToAssetGen` decomposes its argument with `Num2Bits(64)`
  (`src/lib/asset_gen.circom:18-19`), so the public bucket's asset id is range-checked
  too. Modelled so that every `===` in the transitive closure is accounted for. -/
  pub_asset_range : Num2BitsSat 64 w.publicAssetId w.pubAssetBits
  pub_in_range : RangeCheck64Sat w.publicIn w.pubInBits
  pub_out_range : RangeCheck64Sat w.publicOut w.pubOutBits
  pub_in_mul : ValueScalarMulSat w.pubInBits w.pubGen w.pubInPt
  pub_out_mul : ValueScalarMulSat w.pubOutBits w.pubGen w.pubOutPt
  /-- `src/lib/transact.circom:191-202` — the load-bearing conservation check. -/
  value_balance : PerAssetValueBalanceSat nIn nOut (inAsset w) (inValue w) (outAsset w)
    (outValue w) w.publicAssetId w.publicIn w.publicOut w.vbPubInv w.vbPubEq
    w.vbInInv w.vbInEq w.vbOutInv w.vbOutEq w.vbInTerm w.vbOutTerm w.vbLhs w.vbRhs
  /-- `src/lib/transact.circom:204-222` — the point equation, over the published coordinate
  pairs, which is what the circuit compares. Included for fidelity; nothing is derived from
  it, because `pointBalance_not_sound` shows nothing can be.

  This used to be stated over group elements, which cost six further fields asserting that
  each published pair is the image under `coords` of a subgroup element — the only fields in
  the model with no circom counterpart, and in the dangerous direction of `FIDELITY.md`'s
  table, since `PerAssetPointBalance` imposes no such check. `Gadgets/PointBalance.lean`
  now folds `PointSum` over `Pt` with `babyAdd`, exactly as
  `src/lib/value_commit.circom:157-183` does, and the six are gone. -/
  point_balance : PerAssetPointBalanceSat nIn nOut
    (fun i => (w.spent i).cv) (fun j => (w.out j).cv)
    (fun i => (w.spent i).rH) (fun j => (w.out j).rH)
    w.pubInPt w.pubOutPt
  /-- `src/lib/transact.circom:225-243`, wired into `PolyEval` at
  `src/lib/poly_eval.circom:110-111` — public-input compression. -/
  compress : PolyEvalSat (piCount nIn nOut) (txCoeffs w) w.z w.peAcc w.y

/-- The verifier's Fiat-Shamir derivation, as an abstract relation: `chal c z` holds when
`z` is the challenge derived from coefficient vector `c`.
`contracts/src/libs/PubInputs.sol :: _finalizeRaw` instantiates it as
`z = keccak256(abi.encode(c)) % r`, so it is a function of the vector alone. -/
abbrev Challenge : Type := (ℕ → F) → F → Prop

/-- Obligations the circuit cannot discharge, which the contract must.
Listed so that no theorem below can silently assume them.

`challenge_binds_witness` is the one field here with content. The other three are stubs:
they name a check without stating it, because what they range over — a nullifier set, an
EVM `block.chainid`, a keccak preimage — has no counterpart in this development. Do not
read a stub as discharged; read it as a claim made outside Lean. -/
structure ContractObligations (chal : Challenge) (w : TxWitness depth nIn nOut) : Prop where
  /-- `nullifier[i]` is unspent. Also what makes `rho` derivation collision-free across
  transactions, since `DeriveRho` anchors on `nullifier[0]`. -/
  nullifiers_fresh : True
  /-- **The challenge covers *this witness's* coefficient vector.**

  Not "the contract hashed something", and not "`z` looks random": the vector fed to the
  hash has to agree with `txCoeffs w`, the one the accepted proof evaluated. The contract
  hashes the vector it reconstructs from calldata and never sees `txCoeffs w`, so nothing
  on-chain establishes it directly. What makes it true in practice is the pinning argument
  below: every coefficient is fixed by a constraint the prover cannot solve around, so the
  only vector it can evaluate is the one describing the transaction it actually has.

  `chal` ranges over more than `txCoeffs w`. The contract's preimage is 69 words at the
  shipped shape against 46 coefficients — the addresses, the FMD clues and the payload
  digest are hashed and never evaluated, which is how they bind with no constraint at all.
  This field states only the part that has to agree.

  It was `challenge_is_fiat_shamir : True` until `polyEval_forge` was proved. A stub was the
  wrong shape: it reads as a check somebody performs, whereas the property is a relation
  between the challenge and the *witness*. -/
  challenge_binds_witness : chal (txCoeffs w) w.z
  /-- `chain_id = block.chainid` and `recipient_address < 2^160`.

  Checked against the calldata copy of those fields, which is a different quantity from
  `w.chainId` / `w.recipient` unless `challenge_binds_witness` holds. -/
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
  /-- **At least one input slot is real.** Not a value property: it is what keeps
  `merkleRoot` pinned, since a dummy slot's Merkle check is skipped and an all-dummy witness
  leaves the advertised root constrained by nothing. See the pinning section. -/
  someRealInput : ∃ i, i < nIn ∧ (w.spent i).isDummy = 0

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
      (rangeCheck64_sound h.pub_in_range) (rangeCheck64_sound h.pub_out_range) a
  depositBinding := h.cv_dep_bound
  compression := polyEval_sound h.compress
  dummyIsBit _i hi := dummyZeroValue_bit h.dummy_zero hi
  publicAssetRange := (num2Bits_sound (le_of_lt two_pow_64_lt_p) h.pub_asset_range).2
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
The assumption is placed in the statement rather than in an axiom so that it cannot leak
into `transact_sound` or anything else; `Lelantos.Model.Poseidon`'s module note records why the
alternatives — an axiom, or a `∨ PoseidonCollision` conclusion — are worse. -/
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
    (hnIn : nIn ≤ 7) (hnOut : nOut ≤ 7) (h : TransactSat w) (a : F)
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
`piCount - 1` field elements, 68 out of `p ≈ 2^253.6` at `Transact(11, 4, 6)`.

The security reading needs `ContractObligations.challenge_binds_witness`: the prover must
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

/-! ## Pinning: why the compression binds

`transact_pi_binding` is what `PolyEval` buys, and on its own it buys nothing. It is
quantified with both coefficient vectors fixed and then asks how many challenges collide;
the prover gets the opposite order, because `z` is an input it reads before choosing a
witness. The contract derives `z` from calldata the prover authored.

What closes the gap is that `PolyEval` is affine in each coefficient with slope `z ^ k`
(`polyEval_update`), so a coefficient the rest of the constraint system leaves free is one
linear equation in one unknown: `polyEval_forge` solves it, and `y` becomes whatever the
contract asks for, for a completely unrelated transaction. No collision, no low-probability
event — arithmetic.

So the compression is binding exactly when **every** coefficient is pinned, and that is a
property of which slots the layout contains, not of `PolyEval`. At the shipped layout:

| slot | pinned by |
|---|---|
| `merkleRoot` | `spent_sat` — Merkle membership of at least one real input, `not_all_dummy` |
| `nullifier i` | `SpentNoteSat.nf_def`, a Poseidon image |
| `outCm j` | `OutputNoteSat.cm_def`, a Poseidon image |
| `publicAssetId` | `pub_asset_range` (64 bits) and `value_balance` |
| `publicIn` / `publicOut` | `pub_in_range` / `pub_out_range` (64 bits) and `value_balance` |
| `inCv i` / `outCv j` | `SpentNoteSat.cv_sat` / `OutputNoteSat.cv_sat`, a `ValueCommit` |
| `outCvDepX/Y j` | `cv_dep_bound`, likewise |

Pinned does not mean constant. A prover picks its own notes, so it picks the values these
hash and commit to — what it cannot do is *steer* one to a chosen field element, because
each is a Poseidon or Pedersen image of signals that reach no other coefficient. Hitting a
target needs a preimage or a discrete log, not a division.

The three 64-bit slots are the residue: `publicAssetId` is genuinely free within its range
when `publicIn = publicOut = 0`, and `(publicIn, publicOut)` can be shifted together
without disturbing conservation. That is 128 bits of freedom against a 254-bit modulus, so
a solution to the one linear equation exists for about `2⁻¹²⁶` of challenges. This is the
development's honest bound on the compression, and `pub_in_range` / `pub_out_range` /
`pub_asset_range` are what keep it there rather than at 1.

The four address words, the FMD clue triples and the payload digest are not in the table
because they are not coefficients. `4x6.circom` constrains none of them, so as coefficients
they were 23 free unknowns at once; `PubInputs.sol` hashes them into `z` instead, which
binds them against a tampering relayer and needs no constraint at all. `piCount` records
the rule.
-/

/-! ## The instantiated shapes

`transact_sound` is stated for `nIn ≤ 7`, `nOut ≤ 7` — the bound comes from
`perAssetValueBalance_nat`, where it is what keeps each side of the balance equation below
`p`. Seven is where that argument's rounding to `8 · 2^64` runs out, not where any shape
sits; the shipped shape is comfortably inside it. -/

/-- `Transact(11, 4, 6)` — `src/4x6.circom`. **The target shape.**

Six outputs so a withdrawal's change lands on the denomination ladder in one spend rather
than leaving an off-ladder remainder for a follow-up transfer; four inputs because an input
slot costs roughly 3.4x an output slot, carrying a Merkle path the output side does not.
Depth 11 because an unused output slot is a real value-0 leaf, so six outputs would
otherwise cut the tree's lifetime by a third.

100,320 constraints, inside 2^17. It is the shape that fixes the `≤ 6` end of the slot
bound `transact_sound` carries — the bound itself is stated at 7, where the proof reaches. -/
abbrev Transact4x6 := TxWitness 11 4 6

/-- **Soundness of the `4x6` instance.** -/
theorem transact4x6_sound {w : Transact4x6} (h : TransactSat w) : TxWellFormed w :=
  transact_sound (by norm_num) (by norm_num) h

/-- **The `4x6` binding layer.** -/
theorem transact4x6_binding {w : Transact4x6} (hnc : ¬ PoseidonCollision)
    (h : TransactSat w) : TxBinding w :=
  transact_binding hnc (by norm_num) h


end Lelantos
