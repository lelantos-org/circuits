import Lelantos.Gadgets.BatchAppend
import Lelantos.Gadgets.Comparators
import Lelantos.Gadgets.ValueCommit
import Lelantos.Gadgets.Balance

/-!
# `src/tree_update_batch.circom` — the relayer batch tree-advance proof

The batch circuit hashes its leaves, hands them to `BatchAppend` (`Gadgets/BatchAppend.lean`,
whose circom header explains the tree), equates the two roots it returns with the public
`old_root` and `new_root`, and binds each deposit leaf to its declared value.

The constraint system is split in two — `BatchChainSat` (leaves, the tree and the padding) and
`BatchDepositSat` (the per-leaf deposit binding). The split is load-bearing for the trusted
base: only the deposit half mentions the curve, so every chain result below depends on
`p_prime` alone, which `expected/axioms.txt` records.

On the chain side, each over a `BatchShape`:

* `batch_count_range`, `batch_active_spec`, `batch_padding_zero` — `actual_count ∈ [1, MAX_L]`,
  `active` is its prefix, and every field of an inactive slot is zero, so padding cannot
  smuggle values into the compressed public inputs.
* `batch_capacity`, `batch_frontier_canonical` — the run fits the tree, and no frontier slot a
  root does not read carries a value.
* `batch_old_root` — `old_root` is the tree holding `start_index` leaves with this frontier.
* `batch_advances_by_count` — `new_root` is that tree after appending exactly the first
  `actual_count` leaves. `batch_advances_at_positions` states the same root as a run of
  single-leaf inserts at positions `start_index + k` (`appendRoot`).
* `batch_new_root_determined` — under Poseidon collision resistance, two proofs from the same
  `old_root`, `start_index`, `actual_count` and leaves reach the same `new_root`: the frontier
  is private, but `old_root` pins every slot of it a root reads.

The tree results assume `ZerosCoherent zeros`, that the `EMPTY_SUBTREE` table is the
empty-subtree chain (`Spec/QuatTree.lean`). The table is a parameter of the constraint system
rather than a signal, so every assignment of one circuit shares it.

and on the deposit side:

* `batch_deposit_opens` — an active deposit leaf's `cv_dep` opens to exactly
  `leaf_public_in` units of `leaf_asset`. Because the binding is *per leaf*, there is no
  aggregate whose split is free: an aggregate would fix only `Σvalue` modulo the subgroup
  order `ell`.

## Not covered

* **`BabyCheck`** (step 5) is not modelled: the development has no curve equation, only the
  opaque `coords`/`babyAdd` interface. `batch_deposit_opens` gets its point structure from the
  value-commitment gadget instead.
* **`BatchCompress`** (step 7) is not re-proved here; `polyEval_sound` and `polyEval_binding`
  cover the Horner chain, and the slot *order* is pinned by `batchPiSlot` below.
* Nothing here is a statement about `start_index` being the true tree size; that is the
  contract's obligation (`MASP._validateBatchHeader`).
-/

namespace Lelantos

/-- Every signal of one `TreeUpdateBatch(depth, maxL)` instance. Array signals are total
functions, read only below their declared length, per the convention in `Model.Bits`. -/
structure BatchSignals (depth maxL : ℕ) where
  -- Logical public inputs (`:110-118`).
  oldRoot : F
  newRoot : F
  startIndex : F
  actualCount : F
  cms : ℕ → F
  cvDep : ℕ → Pt
  leafAsset : ℕ → F
  leafPublicIn : ℕ → F
  isDeposit : ℕ → F
  -- Private inputs (`:121-122`).
  frontierIn : ℕ → ℕ → F
  rcv : ℕ → F
  -- Leaf hashes (`:125-136`).
  leaves : ℕ → F
  -- The tree (`:141-151`).
  append : BatchAppendSignals
  -- Deposit binding (`:187-273`).
  activeDep : ℕ → F
  gen : ℕ → Pt
  pubInBits : ℕ → ℕ → F
  rcvBits : ℕ → ℕ → F
  vT : ℕ → Pt
  rH : ℕ → Pt
  expected : ℕ → Pt
  assetInv : ℕ → F
  assetIsZero : ℕ → F
  pubInInv : ℕ → F
  pubInIsZero : ℕ → F

/-- The constraint system of `TreeUpdateBatch(depth, maxL)` with `COUNT_BITS = countBits` and
`EMPTY_SUBTREE = zeros`. Line numbers refer to `src/tree_update_batch.circom`. -/
structure BatchChainSat {depth maxL : ℕ} (countBits : ℕ) (zeros : ℕ → F)
    (w : BatchSignals depth maxL) : Prop where
  /-- `:128-135` — `leaf_k = Poseidon(TAG_LEAF, cm, cv_dep.x, cv_dep.y)`. -/
  leaf_def : ∀ k, k < maxL → w.leaves k = leafHash (w.cms k) (w.cvDep k).x (w.cvDep k).y
  /-- `:141-151` — one `BatchAppend(DEPTH, MAX_L)` over `start_index`, `actual_count`, the
  leaf hashes and `frontier_in`. -/
  append : BatchAppendSat depth maxL countBits zeros w.startIndex w.actualCount w.leaves
    w.frontierIn w.append
  /-- `:152` — `old_root === append.old_root`. -/
  old_root_def : w.oldRoot = w.append.oldRoot
  /-- `:153` — `new_root === append.new_root`. -/
  new_root_def : w.newRoot = w.append.newRoot
  /-- `:158` — inactive `cms` are zero. -/
  pad_cm : ∀ k, k < maxL → (1 - w.append.active k) * w.cms k = 0
  /-- `:159-160` — inactive `cv_dep` coordinates are zero. -/
  pad_cv_x : ∀ k, k < maxL → (1 - w.append.active k) * (w.cvDep k).x = 0
  pad_cv_y : ∀ k, k < maxL → (1 - w.append.active k) * (w.cvDep k).y = 0
  /-- `:161-163` — inactive deposit fields are zero. -/
  pad_asset : ∀ k, k < maxL → (1 - w.append.active k) * w.leafAsset k = 0
  pad_public_in : ∀ k, k < maxL → (1 - w.append.active k) * w.leafPublicIn k = 0
  pad_is_deposit : ∀ k, k < maxL → (1 - w.append.active k) * w.isDeposit k = 0
  /-- `:164` — inactive blinders are zero. -/
  pad_rcv : ∀ k, k < maxL → (1 - w.append.active k) * w.rcv k = 0
  /-- `:171` — `is_deposit` is boolean. -/
  deposit_bit : ∀ k, k < maxL → IsBit (w.isDeposit k)
  /-- `:172-173` — spend leaves carry no deposit fields. -/
  spend_zero_asset : ∀ k, k < maxL → (1 - w.isDeposit k) * w.leafAsset k = 0
  spend_zero_public_in : ∀ k, k < maxL → (1 - w.isDeposit k) * w.leafPublicIn k = 0

/-- The deposit-binding half of the constraint system (`:187-273`). Kept apart from
`BatchChainSat` deliberately: it is the only part mentioning the curve, so the chain
results below reach no curve axiom. `expected/axioms.txt` records the split. -/
structure BatchDepositSat {depth maxL : ℕ} (w : BatchSignals depth maxL) : Prop where
  /-- `:198` — `active_dep = active · is_deposit`. -/
  active_dep_def : ∀ k, k < maxL → w.activeDep k = w.append.active k * w.isDeposit k
  /-- `:203-204` — `HashToAssetGen(leaf_asset)`. -/
  gen_def : ∀ k, k < maxL → w.gen k = coords (assetGen (w.leafAsset k))
  /-- `:207-208` — `ValueTimesGen` range-checks `leaf_public_in` to 64 bits. -/
  public_in_range : ∀ k, k < maxL → RangeCheck64Sat (w.leafPublicIn k) (w.pubInBits k)
  /-- `:207-220` — `expected = leaf_public_in · V^asset + rcv · H`, which is exactly
  a `ValueCommit` over the public-input bits. -/
  expected_def : ∀ k, k < maxL →
    ValueCommitSat (w.pubInBits k) (w.gen k) (w.rcv k) (w.rcvBits k) (w.vT k) (w.rH k)
      (w.expected k)
  /-- `:200-201` — `IsZero(leaf_asset)`. -/
  asset_isZero : ∀ k, k < maxL →
    IsZeroSat (w.leafAsset k) (w.assetInv k) (w.assetIsZero k)
  /-- `:225-226` — `IsZero(leaf_public_in)`. -/
  public_in_isZero : ∀ k, k < maxL →
    IsZeroSat (w.leafPublicIn k) (w.pubInInv k) (w.pubInIsZero k)
  /-- `:272` — step 6a. On an active deposit leaf, `leaf_asset = 0` exactly when
  `leaf_public_in = 0`.

  Both directions matter and they are one constraint. A leaf carrying value must
  declare a non-zero asset: `SpentNote` rejects id 0 on every real note, so such a
  leaf would be committed and unspendable. A WORTHLESS leaf must declare asset 0,
  because `ValueTimesGen(0, gen)` is the curve identity for every `gen` — at
  `leaf_public_in = 0` the binding below degenerates to `cv_dep = rcv · H` and says
  nothing about the asset, which would leave `leaf_asset` a PolyEval coefficient
  held by nothing but a range check. Pinned to a constant is pinned. -/
  asset_matches_value : ∀ k, k < maxL →
    w.activeDep k * (w.assetIsZero k - w.pubInIsZero k) = 0
  /-- `:222-223` — the binding, gated on `active · is_deposit`. -/
  deposit_x : ∀ k, k < maxL → w.activeDep k * ((w.cvDep k).x - (w.expected k).x) = 0
  deposit_y : ∀ k, k < maxL → w.activeDep k * ((w.cvDep k).y - (w.expected k).y) = 0

/-- The whole circuit: both halves. -/
structure BatchSat {depth maxL : ℕ} (countBits : ℕ) (zeros : ℕ → F)
    (w : BatchSignals depth maxL) : Prop where
  chain : BatchChainSat countBits zeros w
  deposit : BatchDepositSat w

section Chain

variable {depth maxL countBits : ℕ} {zeros : ℕ → F} {w : BatchSignals depth maxL}

/-! ## The activity prefix -/

/-- Points are equal when both coordinates are. `Pt` carries no `@[ext]` attribute. -/
theorem pt_ext {a b : Pt} (hx : a.x = b.x) (hy : a.y = b.y) : a = b := by
  cases a; cases b; simp_all

/-- **The count is in range.** `actual_count ∈ [1, maxL]`. -/
theorem batch_count_range (hs : BatchShape depth maxL countBits)
    (h : BatchChainSat countBits zeros w) :
    1 ≤ w.actualCount.val ∧ w.actualCount.val ≤ maxL :=
  batchAppend_count_range hs h.append

/-- **`active` is the prefix indicator** of `actual_count`. -/
theorem batch_active_spec (hs : BatchShape depth maxL countBits)
    (h : BatchChainSat countBits zeros w) :
    ∀ k, k < maxL → w.append.active k = ind (k < w.actualCount.val) :=
  batchAppend_active_spec hs h.append

/-- **Padding is zero.** Every verifier-visible field of an inactive leaf vanishes, so a
prover cannot smuggle values into the compressed public inputs through unused slots. -/
theorem batch_padding_zero (hs : BatchShape depth maxL countBits)
    (h : BatchChainSat countBits zeros w) {k : ℕ} (hk : k < maxL) (hge : w.actualCount.val ≤ k) :
    w.cms k = 0 ∧ w.cvDep k = ⟨0, 0⟩ ∧ w.leafAsset k = 0 ∧ w.leafPublicIn k = 0 ∧
      w.isDeposit k = 0 ∧ w.rcv k = 0 := by
  have one : (1 : F) - w.append.active k = 1 := by
    rw [batch_active_spec hs h k hk, ind, if_neg (by omega)]; ring
  have hx := h.pad_cv_x k hk
  have hy := h.pad_cv_y k hk
  rw [one, one_mul] at hx hy
  refine ⟨?_, pt_ext hx hy, ?_, ?_, ?_, ?_⟩ <;>
    first
    | simpa [one] using h.pad_cm k hk
    | simpa [one] using h.pad_asset k hk
    | simpa [one] using h.pad_public_in k hk
    | simpa [one] using h.pad_is_deposit k hk
    | simpa [one] using h.pad_rcv k hk

/-! ## The tree -/

/-- **The run fits the tree.** `start_index + actual_count ≤ 4^depth`. -/
theorem batch_capacity (hs : BatchShape depth maxL countBits)
    (h : BatchChainSat countBits zeros w) :
    w.startIndex.val + w.actualCount.val ≤ 4 ^ depth :=
  batchAppend_capacity hs h.append

/-- **No free frontier slot.** Every `frontier_in` slot at or above its level's digit of
`start_index` is zero. -/
theorem batch_frontier_canonical (hs : BatchShape depth maxL countBits)
    (h : BatchChainSat countBits zeros w) {d : ℕ} (hd : d < depth) {k : ℕ} (hk : k < 3)
    (hge : quatDigit w.startIndex.val d ≤ k) :
    w.frontierIn d k = 0 :=
  batchAppend_frontier_zero hs h.append hd hk hge

/-- **`old_root` is the tree before the append**: the tree holding `start_index` leaves whose
frontier is `frontier_in`. -/
theorem batch_old_root (hs : BatchShape depth maxL countBits) (hz : ZerosCoherent zeros)
    (h : BatchChainSat countBits zeros w) :
    w.oldRoot = batchTree w.startIndex.val 0 w.leaves w.frontierIn zeros depth 0 :=
  h.old_root_def.trans (batchAppend_old_root hs hz h.append)

/-- **The batch appends exactly `actual_count` leaves.** `new_root` is the tree before the
append with the first `actual_count` leaves added at `start_index`. Nothing here mentions the
parity of `actual_count`: that is the whole content of the leaf-granular design. -/
theorem batch_advances_by_count (hs : BatchShape depth maxL countBits)
    (hz : ZerosCoherent zeros) (h : BatchChainSat countBits zeros w) :
    w.newRoot = batchTree w.startIndex.val w.actualCount.val w.leaves w.frontierIn zeros
      depth 0 :=
  h.new_root_def.trans (batchAppend_new_root hs hz h.append)

/-- **The batch appends at consecutive positions, starting at `start_index`.** `new_root` is
`appendRoot`, the root after a run of single-leaf inserts from `frontier_in`, one leaf per
position `start_index + k` for every `k` below `actual_count`. Each step of that run is a
genuine `InsertsTo` by construction (`append_insertsTo`), and `InsertsTo.unique` makes it the
only run from `frontier_in` at those positions. -/
theorem batch_advances_at_positions (hs : BatchShape depth maxL countBits)
    (hz : ZerosCoherent zeros) (h : BatchChainSat countBits zeros w) :
    w.startIndex.val + w.actualCount.val ≤ 4 ^ depth ∧
      w.newRoot = appendRoot depth w.startIndex.val w.leaves w.frontierIn zeros
        (w.actualCount.val - 1) := by
  have hcap := batch_capacity hs h
  refine ⟨hcap, ?_⟩
  rw [batch_advances_by_count hs hz h,
    batchTree_eq_appendRoot hz (batch_count_range hs h).1 hcap]

/-- **The new root is determined by the public statement**, under Poseidon collision
resistance. Two proofs from the same `old_root`, `start_index`, `actual_count`, commitments
and value commitments reach the same `new_root`, whatever private frontier each supplied:
`old_root` pins every frontier slot a root reads (`batchTree_frontier_inj`), and the new tree
reads no other. -/
theorem batch_new_root_determined (hcr : ¬ PoseidonCollision)
    (hs : BatchShape depth maxL countBits) (hz : ZerosCoherent zeros)
    {w' : BatchSignals depth maxL}
    (h : BatchChainSat countBits zeros w) (h' : BatchChainSat countBits zeros w')
    (hold : w.oldRoot = w'.oldRoot) (hstart : w.startIndex = w'.startIndex)
    (hcount : w.actualCount = w'.actualCount)
    (hcm : ∀ k, k < maxL → w.cms k = w'.cms k) (hcv : ∀ k, k < maxL → w.cvDep k = w'.cvDep k) :
    w.newRoot = w'.newRoot := by
  obtain ⟨_, hhi⟩ := batch_count_range hs h
  have hSlt := (batchAppend_start hs h.append).2
  have h0 : w.startIndex.val / 4 ^ depth ≤ 0 := by rw [Nat.div_eq_of_lt hSlt]
  have hL : ∀ k, k < w.actualCount.val → w.leaves k = w'.leaves k := fun k hk => by
    rw [h.leaf_def k (by omega), h'.leaf_def k (by omega), hcm k (by omega), hcv k (by omega)]
  -- The old roots agree, so the frontiers agree wherever a root reads them.
  have hold' : batchTree w.startIndex.val 0 w.leaves w.frontierIn zeros depth 0 =
      batchTree w.startIndex.val 0 w.leaves w'.frontierIn zeros depth 0 := by
    rw [← batch_old_root hs hz h, hold, batch_old_root hs hz h', ← hstart]
    exact batchTree_congr (fun _ _ _ _ => rfl) (fun k hk => absurd hk (Nat.not_lt_zero k))
      depth le_rfl 0 h0
  have hfr := batchTree_frontier_inj hcr hSlt hold'
  rw [batch_advances_by_count hs hz h, batch_advances_by_count hs hz h', ← hstart, ← hcount]
  exact batchTree_congr hfr hL depth le_rfl 0 h0

end Chain

/-! ### The deployed instantiation

`src/tree_update_batch.circom` instantiates `TreeUpdateBatch(11, 8)` with
`COUNT_BITS = 3`. `BatchShape.deployed` discharges the numeric side conditions at those
numbers, which shows the bounds the results above carry are *simultaneously satisfiable*.
`ZerosCoherent` is not numeric and stays a hypothesis; that it holds together with
`BatchChainSat` on one assignment is `batch_advances_witness` (`Proofs/BatchCompleteness.lean`).

`MAX_L = 8` is a floor rather than a choice: `COUNT_BITS` forces a power of two, and a
spend emits `TRANSACT_OUT = 6` leaves that must fit one batch. -/

/-- The deployed shape meets every side condition. -/
theorem BatchShape.deployed : BatchShape 11 8 3 where
  pow_count := by norm_num
  count_lt_p := by unfold p; norm_num
  depth_lt_p := by unfold p; norm_num
  depth_pos := by norm_num

/-- The windows at the deployed `BatchAppend(11, 8)`, evaluated: eight leaves, then three, then
two per level, then the root. Their sum is `NODES` at `src/lib/batch_append.circom:196-203`, the
thirty `node` signals the compiled circuit carries, and each level above the leaves costs one
`Poseidon(5)` per slot — twenty-two. -/
theorem batchWindow_deployed :
    (List.range 12).map (batchWindow 11 8) = [8, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] ∧
      ((List.range 12).map (batchWindow 11 8)).sum = 30 := by
  decide

/-! ## Deposit binding -/

/-- **An active deposit leaf's `cv_dep` opens to its own declared value.**

The binding is per leaf: `cv_dep[k] = leaf_public_in[k] · V^leaf_asset[k] + rcv[k] · H`,
with `leaf_public_in` the 64-bit range-checked signal and `V^asset` the generator for the
leaf's own asset id. No aggregate appears, so no split between leaves is available — which
is precisely what the earlier pair form, fixing only `Σvalue mod ell`, could not say. -/
theorem batch_deposit_opens {depth maxL : ℕ} {w : BatchSignals depth maxL}
    (h : BatchDepositSat w) {k : ℕ} (hk : k < maxL)
    (hact : w.append.active k = 1) (hdep : w.isDeposit k = 1) :
    w.cvDep k = coords (((w.leafPublicIn k).val : ZMod ell) • assetGen (w.leafAsset k)
      + ((w.rcv k).val : ZMod ell) • H) := by
  have hone : w.activeDep k = 1 := by rw [h.active_dep_def k hk, hact, hdep]; ring
  have hx : (w.cvDep k).x = (w.expected k).x := by
    have := h.deposit_x k hk
    rw [hone, one_mul, sub_eq_zero] at this
    exact this
  have hy : (w.cvDep k).y = (w.expected k).y := by
    have := h.deposit_y k hk
    rw [hone, one_mul, sub_eq_zero] at this
    exact this
  have hpt : w.cvDep k = w.expected k := pt_ext hx hy
  rw [hpt]
  have hgen := h.gen_def k hk
  have hcommit := h.expected_def k hk
  rw [hgen] at hcommit
  exact valueCommit_opens (h.public_in_range k hk) hcommit

/-! ## The public-input layout

`BatchCompress(MAX_L)` (`src/lib/poly_eval.circom:156-198`) folds the batch's public inputs
into `(z, y)` with the same Horner chain `TransactCompressN` uses, so `polyEval_sound` and
`polyEval_binding` already cover the evaluation. What they do not cover is the *order*, and
until this section existed Lean pinned no batch layout at all: `test/formal/batch_layout_parity.test.ts`
anchored on the published vector instead, and says in its own header that a Lean dump would
let it switch anchors without changing what it asserts. This is that dump.

The batch layout differs from the transact one in a way worth stating where the definition
is. All `4 + 6·MAX_L` words are coefficients. Transact evaluates 46 of its 69 because the
other 23 are not signals of `4x6.circom` and so can be bound through the challenge instead;
the batch has no such words, so evaluating every one is the only sound option — hashing a
signal into `z` binds nothing against a prover that reads `z` first. `polyEval_forge` is
why.
-/

/-- One coefficient position of `BatchCompress`. -/
inductive BatchPISlot where
  | oldRoot
  | newRoot
  | startIndex
  | actualCount
  | cms (k : ℕ)
  | cvDepX (k : ℕ)
  | cvDepY (k : ℕ)
  | leafAsset (k : ℕ)
  | leafPublicIn (k : ℕ)
  | isDeposit (k : ℕ)
deriving Repr, DecidableEq, Inhabited

/-- Number of `BatchCompress` coefficients: `4 + 6·MAX_L`
(`src/lib/poly_eval.circom:157`). At `MAX_L = 8` this is 52. -/
def batchPiCount (maxL : ℕ) : ℕ := 4 + 6 * maxL

example : batchPiCount 8 = 52 := by norm_num [batchPiCount]

/-- The layout of the `pe.coeffs` assignments — `src/lib/poly_eval.circom:173-197`.
Single source of truth, as `piSlot` is for the transact shapes. -/
def batchPiSlot (maxL : ℕ) (i : ℕ) : BatchPISlot :=
  let oCms := 4
  let oCv := oCms + maxL
  let oAsset := oCv + 2 * maxL
  let oPublicIn := oAsset + maxL
  let oDeposit := oPublicIn + maxL
  if i = 0 then .oldRoot
  else if i = 1 then .newRoot
  else if i = 2 then .startIndex
  else if i = 3 then .actualCount
  else if i < oCv then .cms (i - oCms)
  else if i < oAsset then
    (if (i - oCv) % 2 = 0 then .cvDepX ((i - oCv) / 2) else .cvDepY ((i - oCv) / 2))
  else if i < oPublicIn then .leafAsset (i - oAsset)
  else if i < oDeposit then .leafPublicIn (i - oPublicIn)
  else .isDeposit (i - oDeposit)

/-- The signal a batch slot names. -/
def batchSlotValue {depth maxL : ℕ} (w : BatchSignals depth maxL) : BatchPISlot → F
  | .oldRoot => w.oldRoot
  | .newRoot => w.newRoot
  | .startIndex => w.startIndex
  | .actualCount => w.actualCount
  | .cms k => w.cms k
  | .cvDepX k => (w.cvDep k).x
  | .cvDepY k => (w.cvDep k).y
  | .leafAsset k => w.leafAsset k
  | .leafPublicIn k => w.leafPublicIn k
  | .isDeposit k => w.isDeposit k

/-- The `PolyEval` coefficient vector of the batch circuit. The challenge and the
result are wired at `src/lib/poly_eval.circom:199-200`, and `y` reaches the circuit's
own output at `src/tree_update_batch.circom:290`. -/
def batchCoeffs {depth maxL : ℕ} (w : BatchSignals depth maxL) (i : ℕ) : F :=
  batchSlotValue w (batchPiSlot maxL i)

/-- The coefficient index a batch slot occupies — the inverse of `batchPiSlot`. -/
def batchSlotIndex (maxL : ℕ) : BatchPISlot → ℕ
  | .oldRoot => 0
  | .newRoot => 1
  | .startIndex => 2
  | .actualCount => 3
  | .cms k => 4 + k
  | .cvDepX k => 4 + maxL + 2 * k
  | .cvDepY k => 4 + maxL + 2 * k + 1
  | .leafAsset k => 4 + 3 * maxL + k
  | .leafPublicIn k => 4 + 4 * maxL + k
  | .isDeposit k => 4 + 5 * maxL + k

/-- The slots a `maxL` instance actually has. -/
def BatchPISlot.InRange (maxL : ℕ) : BatchPISlot → Prop
  | .cms k | .cvDepX k | .cvDepY k | .leafAsset k | .leafPublicIn k | .isDeposit k => k < maxL
  | _ => True

theorem batchSlotIndex_lt {maxL : ℕ} {s : BatchPISlot} (hs : s.InRange maxL) :
    batchSlotIndex maxL s < batchPiCount maxL := by
  cases s <;> simp only [BatchPISlot.InRange] at hs <;>
    simp only [batchSlotIndex, batchPiCount] <;> omega

/-- **`batchSlotIndex` is a section of `batchPiSlot`.** -/
theorem batchPiSlot_batchSlotIndex {maxL : ℕ} {s : BatchPISlot} (hs : s.InRange maxL) :
    batchPiSlot maxL (batchSlotIndex maxL s) = s := by
  cases s <;> simp only [BatchPISlot.InRange] at hs <;>
    simp only [batchSlotIndex, batchPiSlot] <;>
    repeat' first
      | rfl
      | rw [if_neg (by omega)]
      | rw [if_pos (by omega)]
      | (congr 1; omega)

/-- The layout as a list of slot names, for `lean/scripts/dump-layout.sh`. -/
def batchLayoutNames (maxL : ℕ) : List String :=
  (List.range (batchPiCount maxL)).map (fun i => reprStr (batchPiSlot maxL i))

end Lelantos
