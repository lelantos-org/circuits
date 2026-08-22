import Lelantos.Gadgets.Insert
import Lelantos.Gadgets.Comparators
import Lelantos.Gadgets.ValueCommit
import Lelantos.Gadgets.Balance

/-!
# `src/tree_update_batch.circom` — the relayer batch tree-advance proof

The batch circuit takes a frontier, a list of leaves, and a count, and produces the root
the commitment tree reaches after appending those leaves. It is **leaf-granular**:
`actual_count` counts leaves, not pairs, so a batch may commit any number in `[1, MAX_L]`,
odd included. Everything below is about that reading being real rather than intended.

The constraint system is split in two — `BatchChainSat` (the append machinery) and
`BatchDepositSat` (the per-leaf deposit binding). The split is load-bearing for the trusted
base: only the deposit half mentions the curve, so every chain result below depends on
`p_prime` alone, which `expected/axioms.txt` records.

On the chain side:

* `batch_count_range` — `actual_count ∈ [1, MAX_L]`. The `Num2Bits(COUNT_BITS)` on
  `actual_count - 1` is what rules out `0`, and it does so only because `2^COUNT_BITS < p`;
  at `actual_count = 0` the witness would need to decompose `p - 1`.
* `batch_active_spec` — `active[k]` really is the indicator of `k < actual_count`, hence
  monotone. Monotonicity is the load-bearing part: the mux chain means "append the first
  `actual_count` leaves" only if the active prefix is contiguous. A non-monotone `active`
  would append leaf `k` at slot `start_index + k` while slot `start_index + k - 1` was
  never filled, silently corrupting the tree.
* `batch_padding_zero` — every field of an inactive leaf is zero. These slots still feed
  `PolyEval`, so without this a prover could smuggle arbitrary `cv_dep` into the
  verifier-visible public inputs.
* `batch_advances_by_count` — the payoff, stated as one theorem with two halves: every step
  below `actual_count` is a genuine `InsertsTo` of that leaf over the running frontier, and
  `new_root` is the running root at index `actual_count`. Neither half alone is the wanted
  statement — see the theorem's own note. This is the formal content of "odd counts work",
  and `batch_advances_by_count_deployed` pins it at `TreeUpdateBatch(10, 4)`.

`InsertsTo` (`Gadgets/Insert.lean`) is the abstract meaning of an append. It is an
existential over the hash chain, but `InsertsTo.unique` shows the chain is determined by
`(leaf, digits, frontier)`, so "the root after `actual_count` appends" is a genuine
function of the inputs rather than something the witness gets to choose.

and one on the deposit side:

* `batch_deposit_opens` — an active deposit leaf's `cv_dep` opens to exactly
  `leaf_public_in` units of `leaf_asset`. Because the binding is *per leaf*, there is no
  aggregate whose split is free: the old pair form fixed only `Σvalue` modulo the subgroup
  order `ell`, which is what the pad leaf existed to patch. Here the value of each leaf is
  pinned on its own, so the statement is about that leaf and needs no companion.

## Not covered

* **`FrontierRoot`** (`src/lib/frontier_root.circom`, step 8) is not modelled, so
  `old_root === frontier_root.root` appears nowhere below. The chain results take the
  frontier as given; they say what the circuit *does with* `frontier_in`, not that
  `frontier_in` is the honest frontier for `old_root`. That binding is what stops a relayer
  pairing a real `old_root` with a forged frontier, and it remains unproved here.
* **`BabyCheck`** (step 6) is not modelled: the development has no curve equation, only the
  opaque `coords`/`babyAdd` interface. So "`cv_dep` is on the curve" is absent, and
  `batch_deposit_opens` gets its point structure from the value-commitment gadget instead.
* **`BatchCompress`** (step 11) is not re-proved here; `polyEval_sound` and
  `polyEval_binding` already cover the Horner chain, and the slot *order* is pinned by
  `src/test/tree_update_batch.test.ts` against `PubInputs.sol`, not in Lean.
* Nothing here is a statement about `start_index` being the true tree size; that is the
  contract's obligation (`MASP._validateBatchHeader`).
-/

namespace Lelantos

/-- Every signal of one `TreeUpdateBatch(depth, maxL)` instance. Array signals are total
functions, read only below their declared length, per the convention in `Model.Bits`. -/
structure BatchSignals (depth maxL : ℕ) where
  -- Logical public inputs (`:61-69`).
  oldRoot : F
  newRoot : F
  startIndex : F
  actualCount : F
  cms : ℕ → F
  cvDep : ℕ → Pt
  leafAsset : ℕ → F
  leafPublicIn : ℕ → F
  isDeposit : ℕ → F
  -- Private inputs (`:72-73`).
  frontierIn : ℕ → ℕ → F
  rcv : ℕ → F
  -- Activity (`:79-90`).
  cntBits : ℕ → F
  ltBits : ℕ → ℕ → F
  active : ℕ → F
  -- Leaf hashes (`:114-123`).
  leaves : ℕ → F
  -- Deposit binding (`:139-168`).
  activeDep : ℕ → F
  gen : ℕ → Pt
  pubInBits : ℕ → ℕ → F
  rcvBits : ℕ → ℕ → F
  vT : ℕ → Pt
  rH : ℕ → Pt
  expected : ℕ → Pt
  -- Insert indices (`:210-216`).
  idxBits : ℕ → ℕ → F
  idxDig : ℕ → ℕ → F
  -- Per-leaf insert instances (`:218-226`).
  zeros : ℕ → F
  insB : ℕ → ℕ → ℕ → F
  insS : ℕ → ℕ → ℕ → F
  insC : ℕ → ℕ → ℕ → F
  insCur : ℕ → ℕ → F
  insFrOut : ℕ → ℕ → ℕ → F
  insRoot : ℕ → F
  -- Running state and its mux (`:194-239`).
  fr : ℕ → ℕ → ℕ → F
  runningRoot : ℕ → F

/-- The constraint system of `TreeUpdateBatch(depth, maxL)` with `2 ^ countBits = maxL`.
Line numbers refer to `src/tree_update_batch.circom`. -/
structure BatchChainSat {depth maxL : ℕ} (countBits : ℕ)
    (w : BatchSignals depth maxL) : Prop where
  /-- `:79-80` — `Num2Bits(COUNT_BITS)` on `actual_count - 1`. -/
  count_bits : Num2BitsSat countBits (w.actualCount - 1) w.cntBits
  /-- `:85-90` — `active[k] = LessThan(COUNT_BITS+1)(k, actual_count)`. -/
  active_def : ∀ k, k < maxL →
    LessThanSat (countBits + 1) ((k : ℕ) : F) w.actualCount (w.ltBits k) (w.active k)
  /-- `:95` — inactive `cms` are zero. -/
  pad_cm : ∀ k, k < maxL → (1 - w.active k) * w.cms k = 0
  /-- `:96-97` — inactive `cv_dep` coordinates are zero. -/
  pad_cv_x : ∀ k, k < maxL → (1 - w.active k) * (w.cvDep k).x = 0
  pad_cv_y : ∀ k, k < maxL → (1 - w.active k) * (w.cvDep k).y = 0
  /-- `:98-101` — inactive deposit fields are zero. -/
  pad_asset : ∀ k, k < maxL → (1 - w.active k) * w.leafAsset k = 0
  pad_public_in : ∀ k, k < maxL → (1 - w.active k) * w.leafPublicIn k = 0
  pad_is_deposit : ∀ k, k < maxL → (1 - w.active k) * w.isDeposit k = 0
  /-- `:101` — inactive blinders are zero. -/
  pad_rcv : ∀ k, k < maxL → (1 - w.active k) * w.rcv k = 0
  /-- `:108` — `is_deposit` is boolean. -/
  deposit_bit : ∀ k, k < maxL → IsBit (w.isDeposit k)
  /-- `:109-110` — spend leaves carry no deposit fields. -/
  spend_zero_asset : ∀ k, k < maxL → (1 - w.isDeposit k) * w.leafAsset k = 0
  spend_zero_public_in : ∀ k, k < maxL → (1 - w.isDeposit k) * w.leafPublicIn k = 0
  /-- `:117-122` — `leaf_k = Poseidon(TAG_LEAF, cm, cv_dep.x, cv_dep.y)`. -/
  leaf_def : ∀ k, k < maxL → w.leaves k = leafHash (w.cms k) (w.cvDep k).x (w.cvDep k).y
  /-- `:211-212` — the insertion index `start_index + k`, range-checked to `2·depth` bits. -/
  idx_bits : ∀ k, k < maxL →
    Num2BitsSat (2 * depth) (w.startIndex + ((k : ℕ) : F)) (w.idxBits k)
  /-- `:214-216` — quaternary digits read off the bit decomposition. -/
  idx_dig : ∀ k, k < maxL → ∀ d, d < depth →
    w.idxDig k d = w.idxBits k (2 * d) + 2 * w.idxBits k (2 * d + 1)
  /-- `:219-226` — one `QuaternaryInsert` per leaf slot, over the running frontier. -/
  insert : ∀ k, k < maxL →
    QuaternaryInsertSat depth (w.leaves k) (w.idxDig k) (w.fr k) w.zeros
      (w.insB k) (w.insS k) (w.insC k) (w.insCur k) (w.insFrOut k) (w.insRoot k)
  /-- `:197-201` — the chain starts at `frontier_in`. -/
  fr_base : ∀ d, d < depth → ∀ s, s < 3 → w.fr 0 d s = w.frontierIn d s
  /-- `:202` — …and at `old_root`. -/
  root_base : w.runningRoot 0 = w.oldRoot
  /-- `:231-233` — the frontier mux. -/
  fr_mux : ∀ k, k < maxL → ∀ d, d < depth → ∀ s, s < 3 →
    w.fr (k + 1) d s = w.active k * w.insFrOut k d s + (1 - w.active k) * w.fr k d s
  /-- `:237-239` — the root mux. -/
  root_mux : ∀ k, k < maxL →
    w.runningRoot (k + 1) = w.active k * w.insRoot k + (1 - w.active k) * w.runningRoot k
  /-- `:243` — `new_root === running_root[MAX_L]`. -/
  new_root_def : w.newRoot = w.runningRoot maxL

/-- The deposit-binding half of the constraint system (`:139-168`). Kept apart from
`BatchChainSat` deliberately: it is the only part mentioning the curve, so the chain
results below reach no curve axiom. `expected/axioms.txt` records the split. -/
structure BatchDepositSat {depth maxL : ℕ} (w : BatchSignals depth maxL) : Prop where
  /-- `:145` — `active_dep = active · is_deposit`. -/
  active_dep_def : ∀ k, k < maxL → w.activeDep k = w.active k * w.isDeposit k
  /-- `:147-148` — `HashToAssetGen(leaf_asset)`. -/
  gen_def : ∀ k, k < maxL → w.gen k = coords (assetGen (w.leafAsset k))
  /-- `:151-152` — `ValueTimesGen` range-checks `leaf_public_in` to 64 bits. -/
  public_in_range : ∀ k, k < maxL → RangeCheck64Sat (w.leafPublicIn k) (w.pubInBits k)
  /-- `:151-164` — `expected = leaf_public_in · V^asset + rcv · H`, which is exactly a
  `ValueCommit` over the public-input bits. -/
  expected_def : ∀ k, k < maxL →
    ValueCommitSat (w.pubInBits k) (w.gen k) (w.rcv k) (w.rcvBits k) (w.vT k) (w.rH k)
      (w.expected k)
  /-- `:166-167` — the binding, gated on `active · is_deposit`. -/
  deposit_x : ∀ k, k < maxL → w.activeDep k * ((w.cvDep k).x - (w.expected k).x) = 0
  deposit_y : ∀ k, k < maxL → w.activeDep k * ((w.cvDep k).y - (w.expected k).y) = 0

/-- The whole circuit: both halves. -/
structure BatchSat {depth maxL : ℕ} (countBits : ℕ)
    (w : BatchSignals depth maxL) : Prop where
  chain : BatchChainSat countBits w
  deposit : BatchDepositSat w

/-! ## The activity prefix -/

/-- Points are equal when both coordinates are. `Pt` carries no `@[ext]` attribute. -/
theorem pt_ext {a b : Pt} (hx : a.x = b.x) (hy : a.y = b.y) : a = b := by
  cases a; cases b; simp_all

/-- The bit-width bookkeeping every batch result shares: `LessThan(countBits + 1)`
decomposes `countBits + 2` bits, so that is the width the field must accommodate, and it
comfortably covers `2 ^ countBits` too. -/
private theorem pow_countBits_lt_p {countBits : ℕ} (hp : 2 ^ (countBits + 2) ≤ p) :
    2 ^ countBits < p := by
  have h1 : 2 ^ (countBits + 1) = 2 ^ countBits * 2 := pow_succ 2 countBits
  have h2 : 2 ^ (countBits + 2) = 2 ^ (countBits + 1) * 2 := pow_succ 2 (countBits + 1)
  have := p_pos
  omega

/-- **The count is in range.** `actual_count ∈ [1, maxL]`.

`0` is excluded because `Num2Bits(countBits)` would have to decompose `(0 - 1).val = p - 1`,
which needs `2 ^ countBits` bits — and `2 ^ countBits < p`. This is the whole reason the
circuit range-checks `actual_count - 1` rather than `actual_count`. -/
theorem batch_count_range {depth maxL countBits : ℕ} {w : BatchSignals depth maxL}
    (hmax : 2 ^ countBits = maxL) (hp : 2 ^ countBits < p) (h : BatchChainSat countBits w) :
    1 ≤ w.actualCount.val ∧ w.actualCount.val ≤ maxL := by
  obtain ⟨hval, _⟩ := num2Bits_sound (le_of_lt hp) h.count_bits
  -- `m` is what the bits denote; `actual_count` is `m + 1`, which is what pins it to
  -- `[1, 2 ^ countBits]` in one step and never mentions `(-1).val`.
  have hlt : (w.actualCount - 1).val < 2 ^ countBits := by
    rw [hval]; exact bitsNat_lt _ _
  have hm : (((w.actualCount - 1).val : ℕ) : F) = w.actualCount - 1 := by
    simp [ZMod.natCast_val, ZMod.cast_id]
  have hsucc : w.actualCount = (((w.actualCount - 1).val + 1 : ℕ) : F) := by
    push_cast
    rw [hm]
    ring
  have hmp : (w.actualCount - 1).val + 1 < p := by omega
  rw [hsucc, ZMod.val_natCast_of_lt hmp]
  omega

/-- **`active` is the prefix indicator.** This is what makes the mux chain mean
"the first `actual_count` leaves": the active set is `{0, …, actual_count - 1}`, contiguous
and downward closed. -/
theorem batch_active_spec {depth maxL countBits : ℕ} {w : BatchSignals depth maxL}
    (hmax : 2 ^ countBits = maxL) (hp : 2 ^ (countBits + 2) ≤ p)
    (h : BatchChainSat countBits w) :
    ∀ k, k < maxL → w.active k = ind (k < w.actualCount.val) := by
  have hstep : 2 ^ (countBits + 1) = 2 ^ countBits * 2 := pow_succ 2 countBits
  have hstep2 : 2 ^ (countBits + 2) = 2 ^ (countBits + 1) * 2 := pow_succ 2 (countBits + 1)
  obtain ⟨hlo, hhi⟩ := batch_count_range hmax (pow_countBits_lt_p hp) h
  intro k hk
  have hkp : k < p := by have := p_pos; omega
  have hkval : (((k : ℕ) : F)).val = k := ZMod.val_natCast_of_lt hkp
  have hka : (((k : ℕ) : F)).val < 2 ^ (countBits + 1) := by omega
  have hca : w.actualCount.val < 2 ^ (countBits + 1) := by omega
  have := lessThan_sound hp hka hca (h.active_def k hk)
  rwa [hkval] at this

/-- An inactive slot has `active = 0`. -/
theorem batch_inactive_zero {depth maxL countBits : ℕ} {w : BatchSignals depth maxL}
    (hmax : 2 ^ countBits = maxL) (hp : 2 ^ (countBits + 2) ≤ p)
    (h : BatchChainSat countBits w) {k : ℕ} (hk : k < maxL) (hge : w.actualCount.val ≤ k) :
    w.active k = 0 := by
  rw [batch_active_spec hmax hp h k hk, ind, if_neg (by omega)]

/-- An active slot has `active = 1`. -/
theorem batch_active_one {depth maxL countBits : ℕ} {w : BatchSignals depth maxL}
    (hmax : 2 ^ countBits = maxL) (hp : 2 ^ (countBits + 2) ≤ p)
    (h : BatchChainSat countBits w) {k : ℕ} (hk : k < maxL) (hlt : k < w.actualCount.val) :
    w.active k = 1 := by
  rw [batch_active_spec hmax hp h k hk, ind, if_pos hlt]

/-- **Padding is zero.** Every verifier-visible field of an inactive leaf vanishes, so a
prover cannot smuggle values into the compressed public inputs through unused slots. -/
theorem batch_padding_zero {depth maxL countBits : ℕ} {w : BatchSignals depth maxL}
    (hmax : 2 ^ countBits = maxL) (hp : 2 ^ (countBits + 2) ≤ p)
    (h : BatchChainSat countBits w) {k : ℕ} (hk : k < maxL) (hge : w.actualCount.val ≤ k) :
    w.cms k = 0 ∧ w.cvDep k = ⟨0, 0⟩ ∧ w.leafAsset k = 0 ∧ w.leafPublicIn k = 0 ∧
      w.isDeposit k = 0 ∧ w.rcv k = 0 := by
  have hz := batch_inactive_zero hmax hp h hk hge
  have one : (1 : F) - w.active k = 1 := by rw [hz]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := h.pad_cm k hk; rw [one, one_mul] at this; exact this
  · have hx := h.pad_cv_x k hk
    have hy := h.pad_cv_y k hk
    rw [one, one_mul] at hx hy
    exact pt_ext hx hy
  · have := h.pad_asset k hk; rw [one, one_mul] at this; exact this
  · have := h.pad_public_in k hk; rw [one, one_mul] at this; exact this
  · have := h.pad_is_deposit k hk; rw [one, one_mul] at this; exact this
  · have := h.pad_rcv k hk; rw [one, one_mul] at this; exact this

/-! ## The insert chain -/

/-- **An active step really is the insert.** The running state after step `k` is what a
genuine `QuaternaryInsert` of leaf `k` over the running frontier produces — stated on the
running signals `fr (k+1)` / `runningRoot (k+1)`, not on the insert component's private
outputs, because those are what the next step consumes. -/
theorem batch_step_inserts {depth maxL countBits : ℕ} {w : BatchSignals depth maxL}
    (hmax : 2 ^ countBits = maxL) (hp : 2 ^ (countBits + 2) ≤ p)
    (h : BatchChainSat countBits w) {k : ℕ} (hk : k < maxL) (hlt : k < w.actualCount.val) :
    InsertsTo depth (w.leaves k) (w.idxDig k) (w.fr k) w.zeros (w.fr (k + 1))
      (w.runningRoot (k + 1)) := by
  have hone := batch_active_one hmax hp h hk hlt
  refine (quaternaryInsert_sound (h.insert k hk)).1.retarget ?_ ?_
  · intro d hd j hj
    rw [h.fr_mux k hk d hd j hj, hone]; ring
  · rw [h.root_mux k hk, hone]; ring

/-- An inactive step is a no-op: the mux carries the running state through untouched. -/
theorem batch_step_stalls {depth maxL countBits : ℕ} {w : BatchSignals depth maxL}
    (hmax : 2 ^ countBits = maxL) (hp : 2 ^ (countBits + 2) ≤ p)
    (h : BatchChainSat countBits w) {k : ℕ} (hk : k < maxL) (hge : w.actualCount.val ≤ k) :
    w.runningRoot (k + 1) = w.runningRoot k ∧
      ∀ d, d < depth → ∀ s, s < 3 → w.fr (k + 1) d s = w.fr k d s := by
  have hz := batch_inactive_zero hmax hp h hk hge
  refine ⟨?_, ?_⟩
  · rw [h.root_mux k hk, hz]; ring
  · intro d hd s hs
    rw [h.fr_mux k hk d hd s hs, hz]; ring

/-- The running root stops moving once the active prefix is exhausted. -/
private theorem runningRoot_stable {depth maxL countBits : ℕ} {w : BatchSignals depth maxL}
    (hmax : 2 ^ countBits = maxL) (hp : 2 ^ (countBits + 2) ≤ p)
    (h : BatchChainSat countBits w) :
    ∀ j, w.actualCount.val ≤ j → j ≤ maxL →
      w.runningRoot j = w.runningRoot w.actualCount.val := by
  intro j
  induction j with
  | zero =>
    intro hle _
    have hzero : w.actualCount.val = 0 := by omega
    rw [hzero]
  | succ m ih =>
    intro hle hlt
    rcases Nat.lt_or_ge w.actualCount.val (m + 1) with hgt | hle'
    · have hm : w.actualCount.val ≤ m := by omega
      rw [(batch_step_stalls hmax hp h (by omega) hm).1]
      exact ih hm (by omega)
    · have hEq : w.actualCount.val = m + 1 := by omega
      rw [hEq]

/-- **The batch appends exactly `actual_count` leaves.**

Two halves, and both are needed for the reading to be the intended one:

* every step below `actual_count` is a real `QuaternaryInsert` of that leaf over the
  frontier the previous step produced — so the leaves genuinely go into the tree, in order,
  starting at the frontier the circuit was given;
* `new_root` is the running root at index `actual_count` — so no *further* leaf is folded
  in past the active prefix.

`batch_active_spec` is what ties the two together: the active set is a contiguous prefix, so
"below `actual_count`" really is "the first `actual_count` slots" with no gap. A
non-monotone `active` would satisfy both bullets while appending leaf `k` at tree position
`start_index + k` with position `start_index + k - 1` never filled.

Nothing here mentions the parity of `actual_count`. That is the whole content of the
leaf-granular design: the pair-granular predecessor could only express even counts because
its chain advanced two leaves per step. -/
theorem batch_advances_by_count {depth maxL countBits : ℕ} {w : BatchSignals depth maxL}
    (hmax : 2 ^ countBits = maxL) (hp : 2 ^ (countBits + 2) ≤ p)
    (h : BatchChainSat countBits w) :
    (∀ k, k < w.actualCount.val →
      InsertsTo depth (w.leaves k) (w.idxDig k) (w.fr k) w.zeros (w.fr (k + 1))
        (w.runningRoot (k + 1))) ∧
      w.newRoot = w.runningRoot w.actualCount.val := by
  obtain ⟨_, hhi⟩ := batch_count_range hmax (pow_countBits_lt_p hp) h
  refine ⟨fun k hk => batch_step_inserts hmax hp h (by omega) hk, ?_⟩
  rw [h.new_root_def]
  exact runningRoot_stable hmax hp h maxL hhi le_rfl

/-! ### The deployed instantiation

`src/tree_update_batch.circom` instantiates `TreeUpdateBatch(10, 4)` with
`COUNT_BITS = 2`. Discharging the side conditions at those numbers is not decoration: it
shows the two bounds the results above carry are *simultaneously satisfiable*, so those
theorems are not conditional on an impossible hypothesis. -/

/-- The deployed shape meets both side conditions. -/
theorem batch_bounds_deployed : (2 : ℕ) ^ 2 = 4 ∧ (2 : ℕ) ^ (2 + 2) ≤ p := by
  refine ⟨by norm_num, ?_⟩
  unfold p
  norm_num

/-- `batch_advances_by_count` at `TreeUpdateBatch(10, 4)`, `COUNT_BITS = 2`. -/
theorem batch_advances_by_count_deployed {w : BatchSignals 10 4}
    (h : BatchChainSat 2 w) :
    (∀ k, k < w.actualCount.val →
      InsertsTo 10 (w.leaves k) (w.idxDig k) (w.fr k) w.zeros (w.fr (k + 1))
        (w.runningRoot (k + 1))) ∧
      w.newRoot = w.runningRoot w.actualCount.val :=
  batch_advances_by_count batch_bounds_deployed.1 batch_bounds_deployed.2 h

/-- `actual_count ∈ [1, 4]` at the deployed shape — odd values included. -/
theorem batch_count_range_deployed {w : BatchSignals 10 4} (h : BatchChainSat 2 w) :
    1 ≤ w.actualCount.val ∧ w.actualCount.val ≤ 4 :=
  batch_count_range batch_bounds_deployed.1
    (pow_countBits_lt_p batch_bounds_deployed.2) h

/-! ## Deposit binding -/

/-- **An active deposit leaf's `cv_dep` opens to its own declared value.**

The binding is per leaf: `cv_dep[k] = leaf_public_in[k] · V^leaf_asset[k] + rcv[k] · H`,
with `leaf_public_in` the 64-bit range-checked signal and `V^asset` the generator for the
leaf's own asset id. No aggregate appears, so no split between leaves is available — which
is precisely what the earlier pair form, fixing only `Σvalue mod ell`, could not say. -/
theorem batch_deposit_opens {depth maxL : ℕ} {w : BatchSignals depth maxL}
    (h : BatchDepositSat w) {k : ℕ} (hk : k < maxL)
    (hact : w.active k = 1) (hdep : w.isDeposit k = 1) :
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

end Lelantos
