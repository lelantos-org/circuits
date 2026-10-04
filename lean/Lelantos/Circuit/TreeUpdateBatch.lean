import Lelantos.Circuit.BatchWitness
import Lelantos.Circuit.BatchLayout
import Lelantos.Circuit.Spent
import Lelantos.Gadgets.Comparators
import Lelantos.Gadgets.Balance
import Lelantos.Gadgets.CoeffDigest

/-!
# `src/tree_update_batch.circom` — the relayer batch tree-advance proof

The circuit builds each slot's leaf, hands the leaves to `BatchAppend`
(`Gadgets/BatchAppend.lean`), and equates the two roots it returns with the public
`old_root` and `new_root`.

A leaf is a note commitment, `cm = Poseidon(TAG_CM, asset_id·2^64 + value, inner)`. With
`is_deposit[k] = 0`, `cms[k]` is the `cm` a transact proof bound as `out_cm` and is the
leaf. With `is_deposit[k] = 1`, `cms[k]` is the depositor's `inner` and the leaf is
`NoteCommitment(leaf_asset[k], leaf_public_in[k], cms[k])`.

Signals: `Lelantos.Circuit.BatchWitness`. Coefficient order: `Lelantos.Circuit.BatchLayout`.
Contract checks: `Lelantos.Circuit.Obligations`. The constraint system is `BatchSat`; every
result depends on `p_prime` alone.

Results, each over a `BatchShape`; † marks those under Poseidon collision resistance:

* `batch_count_range`, `batch_active_spec`, `batch_padding_zero` — `actual_count ∈ [1, MAX_L]`,
  `active` is its prefix, and every field of an inactive slot is zero.
* `batch_capacity`, `batch_frontier_canonical` — the run fits the tree, and every frontier
  slot no root reads is zero.
* `batch_old_root`, `batch_advances_by_count`, `batch_advances_at_positions` — `old_root` is
  the tree holding `start_index` leaves with this frontier, and `new_root` that tree after
  `actual_count` single-leaf inserts at positions `start_index + k` (`appendRoot`).
* `batch_deposit_leaf`, `batch_spend_leaf` — the leaf of a slot, by `is_deposit`.
* `batch_deposit_opening_unique` †, `batch_deposit_spend_binds` † — a deposit leaf opens
  only as its `(leaf_asset, leaf_public_in)` and `inner`, in particular from `SpentNote`.
* `batch_new_root_determined` † — the public statement determines `new_root`, whatever the
  private frontier.
* `batch_compression`, `batch_challenge_nonzero` — `y` is the evaluation of the
  `4 + 4·MAX_L` coefficients, in `batchPiSlot` order (`Circuit/BatchLayout.lean`), at a
  nonzero `z`.
* `batch_digest_public` — the public `digest` is `CoeffDigest` of the same coefficients.
* `batchCoeffs_determined_by_digest` †, `batch_calldata_binding` † — the digest determines
  the coefficient vector, between two witnesses and against a calldata vector.
* `batch_pi_binding`, `batch_calldata_pi_binding` — distinct coefficient vectors agree on at
  most `4 + 4·MAX_L − 1` challenges, 35 at the deployed shape.

The tree results assume `ZerosCoherent zeros`: the `EMPTY_SUBTREE` table, a parameter of
the constraint system, is the empty-subtree chain (`Spec/QuatTree.lean`).

## Not covered

* `is_deposit` is constrained only to be boolean. Set on a spend leaf, the leaf is the hash
  of `out_cm` under `(leaf_asset, leaf_public_in)`, which has no opening as a note; cleared
  on a deposit leaf, the depositor's word is inserted as it stands. Both verify;
  `BatchContractObligations.is_deposit_pinned` records the check that excludes them.
* `new_root` does not commit to the coefficients: a zero leaf is the empty leaf, so a run
  with a trailing zero leaf and a shorter run have the same roots. The `CoeffDigest` public
  signal is the commitment.
* That `start_index` is the tree size, `old_root` the live root, and the leaves the
  escrowed ones is the contract's to check: `BatchContractObligations`
  (`Circuit/Obligations.lean`), assumed by no theorem here.
-/

namespace Lelantos

/-- The constraint system of `TreeUpdateBatch(depth, maxL)` with `COUNT_BITS = countBits` and
`EMPTY_SUBTREE = zeros`, in source order. Line numbers refer to
`src/tree_update_batch.circom`. -/
structure BatchSat {depth maxL : ℕ} (countBits : ℕ) (zeros : ℕ → F)
    (w : BatchSignals depth maxL) : Prop where
  /-- `:98` — `is_deposit` is boolean. -/
  deposit_bit : ∀ k, k < maxL → IsBit (w.isDeposit k)
  /-- `:99` — a spend leaf carries no `leaf_asset`. -/
  spend_zero_asset : ∀ k, k < maxL → (1 - w.isDeposit k) * w.leafAsset k = 0
  /-- `:100` — a spend leaf carries no `leaf_public_in`. -/
  spend_zero_public_in : ∀ k, k < maxL → (1 - w.isDeposit k) * w.leafPublicIn k = 0
  /-- `:113-114` — `rng_asset`: `leaf_asset` is 64-bit, on every slot. -/
  asset_range : ∀ k, k < maxL → RangeCheck64Sat (w.leafAsset k) (w.assetBits k)
  /-- `:116-117` — `rng_public_in`: `leaf_public_in` is 64-bit, on every slot. -/
  public_in_range : ∀ k, k < maxL → RangeCheck64Sat (w.leafPublicIn k) (w.pubInBits k)
  /-- `:119-122` — `dep_cm = NoteCommitment(leaf_asset, leaf_public_in, cms)`: the deposit
  leaf, with `cms[k]` in the `inner` position. -/
  dep_cm_def : ∀ k, k < maxL →
    w.depCm k = noteCommitment (w.leafAsset k) (w.leafPublicIn k) (w.cms k)
  /-- `:124` — `dep_delta[k] <== is_deposit[k] * (dep_cm[k].cm - cms[k])`. -/
  dep_delta_def : ∀ k, k < maxL → w.depDelta k = w.isDeposit k * (w.depCm k - w.cms k)
  /-- `:125` — `leaves[k] <== cms[k] + dep_delta[k]`: the mux. -/
  leaf_def : ∀ k, k < maxL → w.leaves k = w.cms k + w.depDelta k
  /-- `:131-141` — one `BatchAppend(DEPTH, MAX_L)` over `start_index`, `actual_count`, the
  leaves and `frontier_in`. -/
  append : BatchAppendSat depth maxL countBits zeros w.startIndex w.actualCount w.leaves
    w.frontierIn w.append
  /-- `:142` — `old_root === append.old_root`. -/
  old_root_def : w.oldRoot = w.append.oldRoot
  /-- `:143` — `new_root === append.new_root`. -/
  new_root_def : w.newRoot = w.append.newRoot
  /-- `:148` — inactive `cms` are zero. -/
  pad_cm : ∀ k, k < maxL → (1 - w.append.active k) * w.cms k = 0
  /-- `:149` — inactive `leaf_asset` are zero. -/
  pad_asset : ∀ k, k < maxL → (1 - w.append.active k) * w.leafAsset k = 0
  /-- `:150` — inactive `leaf_public_in` are zero. -/
  pad_public_in : ∀ k, k < maxL → (1 - w.append.active k) * w.leafPublicIn k = 0
  /-- `:151` — inactive `is_deposit` are zero. -/
  pad_is_deposit : ∀ k, k < maxL → (1 - w.append.active k) * w.isDeposit k = 0
  /-- `:160-161` — `leaf_asset_z = IsZero()` on `leaf_asset`. -/
  asset_isZero : ∀ k, k < maxL →
    IsZeroSat (w.leafAsset k) (w.assetInv k) (w.assetIsZero k)
  /-- `:162` — step 5: `leaf_asset_z[k].out * leaf_public_in[k] === 0`. No value under asset
  id 0. Ungated: `spend_zero_public_in` and `pad_public_in` force `leaf_public_in` to zero
  on spend and inactive slots. -/
  no_value_under_zero : ∀ k, k < maxL → w.assetIsZero k * w.leafPublicIn k = 0
  /-- `:166-178` — `pe = BatchCompress(MAX_L)`, wired to the public inputs, with `y <== pe.y`:
  public-input compression. Inside it, `pe = PolyEval(N)` over the `coeffs` array the layout
  `Lelantos.batchPiSlot` transcribes, at `src/lib/poly_eval.circom:209-214`. -/
  compress : PolyEvalSat (batchPiCount maxL) (batchCoeffs w) w.z w.zInv w.zIsZero w.peAcc w.y
  /-- `src/lib/poly_eval.circom:203-207` — `dg = CoeffDigest(N)` over the same `coeffs`, with
  `digest <== dg.out`. The circuit's public output is that signal:
  `digest <== pe.digest`, at `src/tree_update_batch.circom:179`. It is not a coefficient and
  is not evaluated into `y`. -/
  digest_def : CoeffDigestSat (batchPiCount maxL) (batchCoeffs w) w.dgBlock w.digest

variable {depth maxL countBits : ℕ} {zeros : ℕ → F} {w : BatchSignals depth maxL}

/-! ## The activity prefix -/

/-- **The count is in range.** `actual_count ∈ [1, maxL]`. -/
theorem batch_count_range (hs : BatchShape depth maxL countBits)
    (h : BatchSat countBits zeros w) :
    1 ≤ w.actualCount.val ∧ w.actualCount.val ≤ maxL :=
  batchAppend_count_range hs h.append

/-- **`active` is the prefix indicator** of `actual_count`. -/
theorem batch_active_spec (hs : BatchShape depth maxL countBits)
    (h : BatchSat countBits zeros w) :
    ∀ k, k < maxL → w.append.active k = ind (k < w.actualCount.val) :=
  batchAppend_active_spec hs h.append

/-- **Padding is zero.** Every verifier-visible field of an inactive leaf vanishes, so a
prover cannot smuggle values into the compressed public inputs through unused slots. -/
theorem batch_padding_zero (hs : BatchShape depth maxL countBits)
    (h : BatchSat countBits zeros w) {k : ℕ} (hk : k < maxL) (hge : w.actualCount.val ≤ k) :
    w.cms k = 0 ∧ w.leafAsset k = 0 ∧ w.leafPublicIn k = 0 ∧ w.isDeposit k = 0 := by
  have one : (1 : F) - w.append.active k = 1 := by
    rw [batch_active_spec hs h k hk, ind, if_neg (by omega)]; ring
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
    | simpa [one] using h.pad_cm k hk
    | simpa [one] using h.pad_asset k hk
    | simpa [one] using h.pad_public_in k hk
    | simpa [one] using h.pad_is_deposit k hk

/-! ## The leaf -/

/-- The leaf of a slot, with the two intermediate signals substituted: `cms[k]` plus
`is_deposit[k]` times the difference to the deposit commitment. -/
theorem batch_leaf_eq (h : BatchSat countBits zeros w) {k : ℕ} (hk : k < maxL) :
    w.leaves k = w.cms k + w.isDeposit k *
      (noteCommitment (w.leafAsset k) (w.leafPublicIn k) (w.cms k) - w.cms k) := by
  rw [h.leaf_def k hk, h.dep_delta_def k hk, h.dep_cm_def k hk]

/-- **A deposit slot's leaf is the note commitment over the public amount**,
`NoteCommitment(leaf_asset[k], leaf_public_in[k], cms[k])`: a function of three public
words. -/
theorem batch_deposit_leaf (h : BatchSat countBits zeros w) {k : ℕ} (hk : k < maxL)
    (hdep : w.isDeposit k = 1) :
    w.leaves k = noteCommitment (w.leafAsset k) (w.leafPublicIn k) (w.cms k) := by
  rw [batch_leaf_eq h hk, hdep]; ring

/-- **A spend slot's leaf is `cms[k]` itself**, the commitment a transact proof bound as
`out_cm`. -/
theorem batch_spend_leaf (h : BatchSat countBits zeros w) {k : ℕ} (hk : k < maxL)
    (hdep : w.isDeposit k = 0) : w.leaves k = w.cms k := by
  rw [batch_leaf_eq h hk, hdep]; ring

/-- Every slot is one of the two. -/
theorem batch_leaf_cases (h : BatchSat countBits zeros w) {k : ℕ} (hk : k < maxL) :
    (w.isDeposit k = 0 ∧ w.leaves k = w.cms k) ∨
      (w.isDeposit k = 1 ∧
        w.leaves k = noteCommitment (w.leafAsset k) (w.leafPublicIn k) (w.cms k)) := by
  rcases isBit_iff.mp (h.deposit_bit k hk) with h0 | h1
  · exact Or.inl ⟨h0, batch_spend_leaf h hk h0⟩
  · exact Or.inr ⟨h1, batch_deposit_leaf h hk h1⟩

/-- Both deposit fields are 64-bit on every slot, which is what makes the packing inside
the deposit commitment injective. -/
theorem batch_deposit_ranges (h : BatchSat countBits zeros w) {k : ℕ} (hk : k < maxL) :
    (w.leafAsset k).val < 2 ^ 64 ∧ (w.leafPublicIn k).val < 2 ^ 64 :=
  ⟨rangeCheck64_sound (h.asset_range k hk), rangeCheck64_sound (h.public_in_range k hk)⟩

/-- A spend slot carries no deposit fields, so neither is a free coefficient there. -/
theorem batch_spend_fields_zero (h : BatchSat countBits zeros w) {k : ℕ} (hk : k < maxL)
    (hdep : w.isDeposit k = 0) : w.leafAsset k = 0 ∧ w.leafPublicIn k = 0 := by
  have ha := h.spend_zero_asset k hk
  have hp := h.spend_zero_public_in k hk
  rw [hdep, sub_zero, one_mul] at ha hp
  exact ⟨ha, hp⟩

/-- **No value under asset id 0.** A slot declaring `leaf_asset = 0` declares
`leaf_public_in = 0`. `SpentNote` refuses id 0 on a real note, so a leaf minted there would
be unspendable. The converse is not constrained: a zero-value deposit leaf may name any
id. -/
theorem batch_no_value_under_zero (h : BatchSat countBits zeros w) {k : ℕ} (hk : k < maxL)
    (hasset : w.leafAsset k = 0) : w.leafPublicIn k = 0 := by
  have hz := isZero_sound (h.asset_isZero k hk)
  rw [if_pos hasset] at hz
  have hmul := h.no_value_under_zero k hk
  rwa [hz, one_mul] at hmul

/-- **A deposit leaf has one opening.** Under Poseidon collision resistance, any
`(asset, value, inner)` with both scalars 64-bit whose note commitment equals a deposit
slot's leaf is that slot's `(leaf_asset, leaf_public_in, cms)`. The opener's two range
checks are hypotheses; `SpentNote` applies them unconditionally
(`batch_deposit_spend_binds`).

`hcr` is unsatisfiable (`poseidon_collision`); this is an assumption recorded in the
statement. -/
theorem batch_deposit_opening_unique (hcr : ¬ PoseidonCollision)
    (h : BatchSat countBits zeros w) {k : ℕ} (hk : k < maxL) (hdep : w.isDeposit k = 1)
    {a v inner : F} (ha : a.val < 2 ^ 64) (hv : v.val < 2 ^ 64)
    (hcm : noteCommitment a v inner = w.leaves k) :
    a = w.leafAsset k ∧ v = w.leafPublicIn k ∧ inner = w.cms k := by
  rw [batch_deposit_leaf h hk hdep] at hcm
  exact noteCommitment_inj hcr ha hv (batch_deposit_ranges h hk).1 (batch_deposit_ranges h hk).2
    hcm

/-- **A deposit leaf can be spent only as its declared amount of its declared asset.** Any
`SpentNote` slot, of any transact shape, whose commitment is a deposit slot's leaf carries
`asset_id = leaf_asset`, `value = leaf_public_in`, and an `inner` equal to the word the
depositor published. The slot need not be real: `SpentNote` range-checks and commits on
dummies too. That the leaf is the one in the tree at the slot's position is
`TxBinding.membershipBinding`. -/
theorem batch_deposit_spend_binds (hcr : ¬ PoseidonCollision)
    (h : BatchSat countBits zeros w) {k : ℕ} (hk : k < maxL) (hdep : w.isDeposit k = 1)
    {d : ℕ} {s : SpentSlot d} (hs : SpentNoteSat s) (hcm : s.cm = w.leaves k) :
    s.assetId = w.leafAsset k ∧ s.value = w.leafPublicIn k ∧
      noteInner s.pk s.rho s.rcm = w.cms k := by
  have hopen := batch_deposit_opening_unique hcr h hk hdep (spentNote_assetRange hs)
    (spentNote_valueRange hs) (by rw [← hcm, hs.cm_def])
  rwa [hs.inner_def] at hopen

/-! ## The tree -/

/-- **The run fits the tree.** `start_index + actual_count ≤ 4^depth`. -/
theorem batch_capacity (hs : BatchShape depth maxL countBits)
    (h : BatchSat countBits zeros w) :
    w.startIndex.val + w.actualCount.val ≤ 4 ^ depth :=
  batchAppend_capacity hs h.append

/-- **No free frontier slot.** Every `frontier_in` slot at or above its level's digit of
`start_index` is zero. -/
theorem batch_frontier_canonical (hs : BatchShape depth maxL countBits)
    (h : BatchSat countBits zeros w) {d : ℕ} (hd : d < depth) {k : ℕ} (hk : k < 3)
    (hge : quatDigit w.startIndex.val d ≤ k) :
    w.frontierIn d k = 0 :=
  batchAppend_frontier_zero hs h.append hd hk hge

/-- **`old_root` is the tree before the append**: the tree holding `start_index` leaves whose
frontier is `frontier_in`. -/
theorem batch_old_root (hs : BatchShape depth maxL countBits) (hz : ZerosCoherent zeros)
    (h : BatchSat countBits zeros w) :
    w.oldRoot = batchTree w.startIndex.val 0 w.leaves w.frontierIn zeros depth 0 :=
  h.old_root_def.trans (batchAppend_old_root hs hz h.append)

/-- **The batch appends `actual_count` leaves.** `new_root` is the tree before the append
with the first `actual_count` leaves added at `start_index`. -/
theorem batch_advances_by_count (hs : BatchShape depth maxL countBits)
    (hz : ZerosCoherent zeros) (h : BatchSat countBits zeros w) :
    w.newRoot = batchTree w.startIndex.val w.actualCount.val w.leaves w.frontierIn zeros
      depth 0 :=
  h.new_root_def.trans (batchAppend_new_root hs hz h.append)

/-- **The batch appends at consecutive positions, starting at `start_index`.** `new_root` is
`appendRoot`, the root after a run of single-leaf inserts from `frontier_in`, one leaf per
position `start_index + k` for every `k` below `actual_count`. Each step of that run is an
`InsertsTo` by construction (`append_insertsTo`), and `InsertsTo.unique` makes it the
only run from `frontier_in` at those positions. -/
theorem batch_advances_at_positions (hs : BatchShape depth maxL countBits)
    (hz : ZerosCoherent zeros) (h : BatchSat countBits zeros w) :
    w.startIndex.val + w.actualCount.val ≤ 4 ^ depth ∧
      w.newRoot = appendRoot depth w.startIndex.val w.leaves w.frontierIn zeros
        (w.actualCount.val - 1) := by
  have hcap := batch_capacity hs h
  refine ⟨hcap, ?_⟩
  rw [batch_advances_by_count hs hz h,
    batchTree_eq_appendRoot hz (batch_count_range hs h).1 hcap]

/-- **The new root is determined by the public statement**, under Poseidon collision
resistance, whatever private frontier each proof supplied: the per-slot words `cms`,
`leaf_asset`, `leaf_public_in` and `is_deposit` fix every leaf (`batch_leaf_eq`), and
`old_root` pins every frontier slot a root reads (`batchTree_frontier_inj`). A relayer
cannot pair a real `old_root` with a forged frontier. This is not the commitment the
compression relies on (`batch_digest_public`). -/
theorem batch_new_root_determined (hcr : ¬ PoseidonCollision)
    (hs : BatchShape depth maxL countBits) (hz : ZerosCoherent zeros)
    {w' : BatchSignals depth maxL}
    (h : BatchSat countBits zeros w) (h' : BatchSat countBits zeros w')
    (hold : w.oldRoot = w'.oldRoot) (hstart : w.startIndex = w'.startIndex)
    (hcount : w.actualCount = w'.actualCount)
    (hcm : ∀ k, k < maxL → w.cms k = w'.cms k)
    (hasset : ∀ k, k < maxL → w.leafAsset k = w'.leafAsset k)
    (hpub : ∀ k, k < maxL → w.leafPublicIn k = w'.leafPublicIn k)
    (hdep : ∀ k, k < maxL → w.isDeposit k = w'.isDeposit k) :
    w.newRoot = w'.newRoot := by
  obtain ⟨_, hhi⟩ := batch_count_range hs h
  have hSlt := (batchAppend_start hs h.append).2
  have h0 : w.startIndex.val / 4 ^ depth ≤ 0 := by rw [Nat.div_eq_of_lt hSlt]
  have hL : ∀ k, k < w.actualCount.val → w.leaves k = w'.leaves k := fun k hk => by
    rw [batch_leaf_eq h (by omega), batch_leaf_eq h' (by omega), hcm k (by omega),
      hasset k (by omega), hpub k (by omega), hdep k (by omega)]
  -- The old roots agree, so the frontiers agree wherever a root reads them.
  have hold' : batchTree w.startIndex.val 0 w.leaves w.frontierIn zeros depth 0 =
      batchTree w.startIndex.val 0 w.leaves w'.frontierIn zeros depth 0 := by
    rw [← batch_old_root hs hz h, hold, batch_old_root hs hz h', ← hstart]
    exact batchTree_congr (fun _ _ _ _ => rfl) (fun k hk => absurd hk (Nat.not_lt_zero k))
      depth le_rfl 0 h0
  have hfr := batchTree_frontier_inj hcr hSlt hold'
  rw [batch_advances_by_count hs hz h, batch_advances_by_count hs hz h', ← hstart, ← hcount]
  exact batchTree_congr hfr hL depth le_rfl 0 h0

/-! ## The compression

The verifier's public signals are `(y, digest, z)`. The binding argument is the transact
circuit's ("Why the compression binds" in `Lelantos.Circuit.Transact`); the results below
are its two halves at the batch layout. The Fiat-Shamir step that joins them is not
formalised.
-/

/-- **`y` is the evaluation of the batch layout at `z`.** -/
theorem batch_compression (h : BatchSat countBits zeros w) :
    w.y = polyEval (batchCoeffs w) (batchPiCount maxL) w.z :=
  polyEval_sound h.compress

/-- **The batch challenge is nonzero**, so every coefficient reaches `y`. -/
theorem batch_challenge_nonzero (h : BatchSat countBits zeros w) : w.z ≠ 0 :=
  polyEvalSat_z_ne_zero h.compress

/-- **The public digest is the digest of the coefficient vector**: `coeffDigest_sound` on
the circuit's `CoeffDigest` instance, nine `Poseidon(5)` blocks at `MAX_L = 8`. -/
theorem batch_digest_public (h : BatchSat countBits zeros w) :
    w.digest = coeffDigest (batchCoeffs w) (batchPiCount maxL) :=
  coeffDigest_sound h.digest_def

/-- **A calldata vector with the witness's digest is the witness's vector**, under Poseidon
collision resistance: if the `CoeffDigest` of a calldata coefficient vector `c` equals the
public `digest` of a satisfying batch witness, `c` agrees with that witness's coefficient
vector. That calldata which verifies satisfies the hypothesis is the Fiat-Shamir step, which
is not formalised. -/
theorem batch_calldata_binding (hcr : ¬ PoseidonCollision) (h : BatchSat countBits zeros w)
    {c : ℕ → F} (hd : coeffDigest c (batchPiCount maxL) = w.digest) :
    ∀ k, k < batchPiCount maxL → c k = batchCoeffs w k :=
  digest_inj hcr (hd.trans (batch_digest_public h))

/-- **The public digest determines the coefficient vector**, under Poseidon collision
resistance. The two witnesses may be of circuits with different `COUNT_BITS` and
`EMPTY_SUBTREE`; only the layout is shared. -/
theorem batchCoeffs_determined_by_digest (hcr : ¬ PoseidonCollision)
    {w' : BatchSignals depth maxL} {countBits' : ℕ} {zeros' : ℕ → F}
    (h : BatchSat countBits zeros w) (h' : BatchSat countBits' zeros' w')
    (hd : w.digest = w'.digest) :
    ∀ k, k < batchPiCount maxL → batchCoeffs w k = batchCoeffs w' k :=
  batch_calldata_binding hcr h' ((batch_digest_public h).symm.trans hd)

/-- `batchCoeffs_determined_by_digest` per named public input: equal digests mean the same
roots, position and count, and the same four words on every slot. -/
theorem batchSlotValue_determined_by_digest (hcr : ¬ PoseidonCollision)
    {w' : BatchSignals depth maxL} {countBits' : ℕ} {zeros' : ℕ → F}
    (h : BatchSat countBits zeros w) (h' : BatchSat countBits' zeros' w')
    (hd : w.digest = w'.digest) {s : BatchPISlot} (hs : s.InRange maxL) :
    batchSlotValue w s = batchSlotValue w' s := by
  rw [← batchCoeffs_slotIndex w hs, ← batchCoeffs_slotIndex w' hs]
  exact batchCoeffs_determined_by_digest hcr h h' hd _ (batchSlotIndex_lt hs)

/-- **Public-input binding for the batch.** If two batches with different coefficient
vectors are accepted against the same `(z, y)`, then `z` is one of at most
`batchPiCount - 1` field elements, 35 out of `p ≈ 2^253.6` at `MAX_L = 8`.

This counts challenges for two vectors that are both fixed: the Schwartz-Zippel half. -/
theorem batch_pi_binding {w' : BatchSignals depth maxL} {countBits' : ℕ} {zeros' : ℕ → F}
    (h : BatchSat countBits zeros w) (h' : BatchSat countBits' zeros' w')
    (hz : w.z = w'.z) (hy : w.y = w'.y)
    (hne : ∃ k, k < batchPiCount maxL ∧ batchCoeffs w k ≠ batchCoeffs w' k) :
    w.z ∈ ({z : F | polyEval (batchCoeffs w) (batchPiCount maxL) z
              = polyEval (batchCoeffs w') (batchPiCount maxL) z} : Set F).toFinset
    ∧ ({z : F | polyEval (batchCoeffs w) (batchPiCount maxL) z
              = polyEval (batchCoeffs w') (batchPiCount maxL) z} : Set F).toFinset.card
        ≤ batchPiCount maxL - 1 := by
  classical
  refine ⟨?_, polyEval_binding (by unfold batchPiCount; omega) hne⟩
  simp only [Set.mem_toFinset, Set.mem_setOf_eq]
  rw [← batch_compression h, hy, batch_compression h', hz]

/-- **Public-input binding against calldata.** Let `c` be the coefficient vector a verifier
read from calldata, whose evaluation at the proof's challenge is the proof's `y`. If `c`
differs from the witness's coefficient vector anywhere, then `z` is one of at most
`batchPiCount - 1` field elements. -/
theorem batch_calldata_pi_binding (h : BatchSat countBits zeros w) {c : ℕ → F}
    (hy : polyEval c (batchPiCount maxL) w.z = w.y)
    (hne : ∃ k, k < batchPiCount maxL ∧ c k ≠ batchCoeffs w k) :
    w.z ∈ ({z : F | polyEval c (batchPiCount maxL) z
              = polyEval (batchCoeffs w) (batchPiCount maxL) z} : Set F).toFinset
    ∧ ({z : F | polyEval c (batchPiCount maxL) z
              = polyEval (batchCoeffs w) (batchPiCount maxL) z} : Set F).toFinset.card
        ≤ batchPiCount maxL - 1 := by
  classical
  refine ⟨?_, polyEval_binding (by unfold batchPiCount; omega) hne⟩
  simp only [Set.mem_toFinset, Set.mem_setOf_eq]
  rw [hy, batch_compression h]

example : batchPiCount 8 - 1 = 35 := by norm_num [batchPiCount]

/-! ### The deployed instantiation

`src/tree_update_batch.circom` instantiates `TreeUpdateBatch(11, 8)` with
`COUNT_BITS = 3`. `BatchShape.deployed` discharges the numeric side conditions there, so
the bounds the results above carry are jointly satisfiable. `ZerosCoherent` stays a
hypothesis; that it holds together with `BatchSat` on one assignment is
`batch_advances_witness` (`Proofs/BatchCompleteness.lean`).

`MAX_L = 8` is the minimum: `COUNT_BITS` requires a power of two, and a spend emits
`TRANSACT_OUT = 6` leaves that must fit one batch. -/

/-- The deployed shape meets every side condition. -/
theorem BatchShape.deployed : BatchShape 11 8 3 where
  pow_count := by norm_num
  count_lt_p := by unfold p; norm_num
  depth_lt_p := by unfold p; norm_num
  depth_pos := by norm_num

/-- The windows at the deployed `BatchAppend(11, 8)`, evaluated: eight leaves, then three, then
two per level, then the root. Their sum is `NODES` at `src/lib/batch_append.circom:191-198`, the
thirty `node` signals the compiled circuit carries, and each level above the leaves costs one
`Poseidon(5)` per slot — twenty-two. -/
theorem batchWindow_deployed :
    (List.range 12).map (batchWindow 11 8) = [8, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] ∧
      ((List.range 12).map (batchWindow 11 8)).sum = 30 := by
  decide

end Lelantos
