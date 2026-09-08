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
  and `batch_advances_by_count_deployed` pins it at `TreeUpdateBatch(11, 8)`.

`InsertsTo` (`Gadgets/Insert.lean`) is the abstract meaning of an append. It is an
existential over the hash chain, but `InsertsTo.unique` shows the chain is determined by
`(leaf, digits, frontier)`, so "the root after `actual_count` appends" is a genuine
function of the inputs rather than something the witness gets to choose.

and one on the deposit side:

* `batch_deposit_opens` — an active deposit leaf's `cv_dep` opens to exactly
  `leaf_public_in` units of `leaf_asset`. Because the binding is *per leaf*, there is no
  aggregate whose split is free: an aggregate would fix only `Σvalue` modulo the subgroup
  order `ell`. Each leaf's value is pinned on its own, so the statement is about that leaf
  and needs no companion.

## Not covered

* **`FrontierRoot`** (`src/lib/frontier_root.circom`, step 8; `:290-299`) is not modelled, so
  `old_root === frontier_root.root` appears nowhere below. The chain results take the
  frontier as given; they say what the circuit *does with* `frontier_in`, not that
  `frontier_in` is the honest frontier for `old_root`. That binding is what stops a relayer
  pairing a real `old_root` with a forged frontier, and it remains unproved here.
* **`BabyCheck`** (step 6) is not modelled: the development has no curve equation, only the
  opaque `coords`/`babyAdd` interface. So "`cv_dep` is on the curve" is absent, and
  `batch_deposit_opens` gets its point structure from the value-commitment gadget instead.
* **`BatchCompress`** (step 11) is not re-proved here; `polyEval_sound` and
  `polyEval_binding` already cover the Horner chain, and the slot *order* is pinned by
  `test/formal/batch_layout_parity.test.ts`, not in Lean.
* Nothing here is a statement about `start_index` being the true tree size; that is the
  contract's obligation (`MASP._validateBatchHeader`).
-/

namespace Lelantos

/-- Every signal of one `TreeUpdateBatch(depth, maxL)` instance. Array signals are total
functions, read only below their declared length, per the convention in `Model.Bits`. -/
structure BatchSignals (depth maxL : ℕ) where
  -- Logical public inputs (`:113-121`).
  oldRoot : F
  newRoot : F
  startIndex : F
  actualCount : F
  cms : ℕ → F
  cvDep : ℕ → Pt
  leafAsset : ℕ → F
  leafPublicIn : ℕ → F
  isDeposit : ℕ → F
  -- Private inputs (`:124-125`).
  frontierIn : ℕ → ℕ → F
  rcv : ℕ → F
  -- Activity (`:138-148`).
  cntBits : ℕ → F
  ltBits : ℕ → ℕ → F
  active : ℕ → F
  -- Leaf hashes (`:173-183`).
  leaves : ℕ → F
  -- Deposit binding (`:199-236`).
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
  -- `start_index`'s own decomposition (`:287-288`).
  startIdxBits : ℕ → F
  -- Insert indices (`:331-336`).
  idxIn : ℕ → F
  idxBits : ℕ → ℕ → F
  idxDig : ℕ → ℕ → F
  -- Per-leaf insert instances (`:340-347`).
  zeros : ℕ → F
  insB : ℕ → ℕ → ℕ → F
  insS : ℕ → ℕ → ℕ → F
  insC : ℕ → ℕ → ℕ → F
  insCur : ℕ → ℕ → F
  insFrOut : ℕ → ℕ → ℕ → F
  insRoot : ℕ → F
  -- Running state and its mux (`:310-360`).
  fr : ℕ → ℕ → ℕ → F
  runningRoot : ℕ → F

/-- The constraint system of `TreeUpdateBatch(depth, maxL)` with `2 ^ countBits = maxL`.
Line numbers refer to `src/tree_update_batch.circom`. -/
structure BatchChainSat {depth maxL : ℕ} (countBits : ℕ)
    (w : BatchSignals depth maxL) : Prop where
  /-- `:138-139` — `Num2Bits(COUNT_BITS)` on `actual_count - 1`. -/
  count_bits : Num2BitsSat countBits (w.actualCount - 1) w.cntBits
  /-- `:145-148` — `active[k] = LessThan(COUNT_BITS+1)(k, actual_count)`. -/
  active_def : ∀ k, k < maxL →
    LessThanSat (countBits + 1) ((k : ℕ) : F) w.actualCount (w.ltBits k) (w.active k)
  /-- `:154` — inactive `cms` are zero. -/
  pad_cm : ∀ k, k < maxL → (1 - w.active k) * w.cms k = 0
  /-- `:155-156` — inactive `cv_dep` coordinates are zero. -/
  pad_cv_x : ∀ k, k < maxL → (1 - w.active k) * (w.cvDep k).x = 0
  pad_cv_y : ∀ k, k < maxL → (1 - w.active k) * (w.cvDep k).y = 0
  /-- `:157-159` — inactive deposit fields are zero. -/
  pad_asset : ∀ k, k < maxL → (1 - w.active k) * w.leafAsset k = 0
  pad_public_in : ∀ k, k < maxL → (1 - w.active k) * w.leafPublicIn k = 0
  pad_is_deposit : ∀ k, k < maxL → (1 - w.active k) * w.isDeposit k = 0
  /-- `:160` — inactive blinders are zero. -/
  pad_rcv : ∀ k, k < maxL → (1 - w.active k) * w.rcv k = 0
  /-- `:167` — `is_deposit` is boolean. -/
  deposit_bit : ∀ k, k < maxL → IsBit (w.isDeposit k)
  /-- `:168-169` — spend leaves carry no deposit fields. -/
  spend_zero_asset : ∀ k, k < maxL → (1 - w.isDeposit k) * w.leafAsset k = 0
  spend_zero_public_in : ∀ k, k < maxL → (1 - w.isDeposit k) * w.leafPublicIn k = 0
  /-- `:176-183` — `leaf_k = Poseidon(TAG_LEAF, cm, cv_dep.x, cv_dep.y)`. -/
  leaf_def : ∀ k, k < maxL → w.leaves k = leafHash (w.cms k) (w.cvDep k).x (w.cvDep k).y
  /-- `:287-288` — `Num2Bits(2·DEPTH)(start_index)`.

  Modelled even though the `FrontierRoot` instance it feeds is not: on its own it says
  `start_index < 4^depth`, which is what makes `active[k] · (start_index + k)` a
  *position* rather than a field element that happens to decompose. Without it
  `batch_active_index` cannot rule out `start_index` wrapping the modulus. -/
  start_index_bits : Num2BitsSat (2 * depth) w.startIndex w.startIdxBits
  /-- `:331` — the insertion index, gated on `active[k]`. -/
  idx_in_def : ∀ k, k < maxL →
    w.idxIn k = w.active k * (w.startIndex + ((k : ℕ) : F))
  /-- `:333` — that gated index, range-checked to `2·depth` bits.

  The gate is load-bearing for fidelity, not a convenience: the circuit decomposes
  `active[k] · (start_index + k)`, so a model demanding the decomposition of
  `start_index + k` for EVERY slot would assume something a prover need not
  satisfy — the dangerous direction of the table in `FIDELITY.md`. It would also
  be false of the circuit, which deliberately admits a batch whose last active
  index is the final leaf of the tree. On an active slot `active[k] = 1` and the
  two coincide; `batch_active_index` below is where that is used. -/
  idx_bits : ∀ k, k < maxL →
    Num2BitsSat (2 * depth) (w.idxIn k) (w.idxBits k)
  /-- `:336` — quaternary digits read off the bit decomposition. -/
  idx_dig : ∀ k, k < maxL → ∀ d, d < depth →
    w.idxDig k d = w.idxBits k (2 * d) + 2 * w.idxBits k (2 * d + 1)
  /-- `:340-347` — one `QuaternaryInsert` per leaf slot, over the running frontier. -/
  insert : ∀ k, k < maxL →
    QuaternaryInsertSat depth (w.leaves k) (w.idxDig k) (w.fr k) w.zeros
      (w.insB k) (w.insS k) (w.insC k) (w.insCur k) (w.insFrOut k) (w.insRoot k)
  /-- `:313-315` — the chain starts at `frontier_in`. -/
  fr_base : ∀ d, d < depth → ∀ s, s < 3 → w.fr 0 d s = w.frontierIn d s
  /-- `:318` — …and at `old_root`. -/
  root_base : w.runningRoot 0 = w.oldRoot
  /-- `:352-354` — the frontier mux. -/
  fr_mux : ∀ k, k < maxL → ∀ d, d < depth → ∀ s, s < 3 →
    w.fr (k + 1) d s = w.active k * w.insFrOut k d s + (1 - w.active k) * w.fr k d s
  /-- `:358-360` — the root mux. -/
  root_mux : ∀ k, k < maxL →
    w.runningRoot (k + 1) = w.active k * w.insRoot k + (1 - w.active k) * w.runningRoot k
  /-- `:364` — `new_root === running_root[MAX_L]`. -/
  new_root_def : w.newRoot = w.runningRoot maxL

/-- The deposit-binding half of the constraint system (`:199-282`). Kept apart from
`BatchChainSat` deliberately: it is the only part mentioning the curve, so the chain
results below reach no curve axiom. `expected/axioms.txt` records the split. -/
structure BatchDepositSat {depth maxL : ℕ} (w : BatchSignals depth maxL) : Prop where
  /-- `:208` — `active_dep = active · is_deposit`. -/
  active_dep_def : ∀ k, k < maxL → w.activeDep k = w.active k * w.isDeposit k
  /-- `:213` — `HashToAssetGen(leaf_asset)`. -/
  gen_def : ∀ k, k < maxL → w.gen k = coords (assetGen (w.leafAsset k))
  /-- `:217` — `ValueTimesGen` range-checks `leaf_public_in` to 64 bits. -/
  public_in_range : ∀ k, k < maxL → RangeCheck64Sat (w.leafPublicIn k) (w.pubInBits k)
  /-- `:217-230` — `expected = leaf_public_in · V^asset + rcv · H`, which is exactly
  a `ValueCommit` over the public-input bits. -/
  expected_def : ∀ k, k < maxL →
    ValueCommitSat (w.pubInBits k) (w.gen k) (w.rcv k) (w.rcvBits k) (w.vT k) (w.rH k)
      (w.expected k)
  /-- `:210-211` — `IsZero(leaf_asset)`. -/
  asset_isZero : ∀ k, k < maxL →
    IsZeroSat (w.leafAsset k) (w.assetInv k) (w.assetIsZero k)
  /-- `:235-236` — `IsZero(leaf_public_in)`. -/
  public_in_isZero : ∀ k, k < maxL →
    IsZeroSat (w.leafPublicIn k) (w.pubInInv k) (w.pubInIsZero k)
  /-- `:282` — step 7a. On an active deposit leaf, `leaf_asset = 0` exactly when
  `leaf_public_in = 0`.

  Both directions matter and they are one constraint. A leaf carrying value must
  declare a non-zero asset: `SpentNote` rejects id 0 on every real note, so such a
  leaf would be committed and unspendable. A WORTHLESS leaf must declare asset 0,
  because `ValueTimesGen(0, gen)` is the curve identity for every `gen` — at
  `leaf_public_in = 0` the binding below degenerates to `cv_dep = rcv · H` and says
  nothing about the asset, which would leave `leaf_asset` a PolyEval coefficient
  held by nothing but a range check. Pinned to a constant is pinned.

  Nothing here refers to a neighbouring slot: the circuit is agnostic to how a
  consumer lays deposits out across the batch. -/
  asset_matches_value : ∀ k, k < maxL →
    w.activeDep k * (w.assetIsZero k - w.pubInIsZero k) = 0
  /-- `:232-233` — the binding, gated on `active · is_deposit`. -/
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

/-! ## Where the leaves land

`batch_advances_by_count` says each active step is a genuine insert *at the digits the
witness supplied*. It does not say which tree position those digits name, and until it does,
"append leaf `k` at `start_index + k`" is prose: `idx_in_def`, `idx_bits` and `idx_dig` sit
in `BatchChainSat` with nothing consuming them, and a witness free to choose `idx_dig`
could fold every leaf into the same slot.

`batch_active_index` is the missing step. It reads the digits back off the range check —
`bitNat_eq_digit` for uniqueness of the decomposition, `quatDigit_eq_bits` for the pairing —
and lands on the *position*, `start_index + k`, as a natural number below `4 ^ depth`.

`start_index_bits` is what makes the last part true rather than merely stated. Without it
`start_index` could be any field element and `start_index.val + k` need not be the natural
the index decomposes to. -/

/-- **The active insertion index is the tree position `start_index + k`**, digit by digit,
and that position is inside the tree. -/
theorem batch_active_index {depth maxL countBits : ℕ} {w : BatchSignals depth maxL}
    (hmax : 2 ^ countBits = maxL) (hp : 2 ^ (countBits + 2) ≤ p)
    (hpd : 2 ^ (2 * depth) + maxL ≤ p) (h : BatchChainSat countBits w)
    {k : ℕ} (hk : k < maxL) (hlt : k < w.actualCount.val) :
    w.startIndex.val + k < 4 ^ depth ∧
      ∀ d, d < depth →
        w.idxDig k d = ((quatDigit (w.startIndex.val + k) d : ℕ) : F) := by
  have hdp : 2 ^ (2 * depth) ≤ p := by omega
  -- `start_index` is a genuine position, so `start_index + k` does not wrap.
  have hstart : w.startIndex.val < 2 ^ (2 * depth) :=
    (num2Bits_sound hdp h.start_index_bits).2
  have hsum : w.startIndex.val + k < p := by omega
  -- On an active slot the gate is transparent.
  have hone := batch_active_one hmax hp h hk hlt
  have hidx : w.idxIn k = (((w.startIndex.val + k : ℕ)) : F) := by
    rw [h.idx_in_def k hk, hone, one_mul]
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]
  have hval : (w.idxIn k).val = w.startIndex.val + k := by
    rw [hidx, ZMod.val_natCast_of_lt hsum]
  obtain ⟨hbits, hlt2⟩ := num2Bits_sound hdp (h.idx_bits k hk)
  rw [hval] at hbits hlt2
  refine ⟨by rwa [show (4 : ℕ) ^ depth = 2 ^ (2 * depth) by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]], fun d hd => ?_⟩
  -- The two bits the circuit pairs are the two bits of the position, by uniqueness of the
  -- decomposition; pairing them is the quaternary digit.
  have hb : ∀ i, i < 2 * depth → IsBit (w.idxBits k i) := (h.idx_bits k hk).bits
  have hq := quatDigit_eq_bits (bs := w.idxBits k) (n := 2 * depth) (d := d) (by omega)
  rw [← hbits] at hq
  rw [h.idx_dig k hk d hd, hq]
  push_cast
  rw [cast_bitNat (hb (2 * d) (by omega)), cast_bitNat (hb (2 * d + 1) (by omega))]

/-- **The batch appends at consecutive positions, starting at `start_index`.**

`batch_advances_by_count` with the digit vector replaced by the digits of the position, so
the statement names where each leaf goes rather than deferring to a private signal. Together
with `batch_active_spec`'s contiguity this is the full reading of the circuit: leaf `k` is
inserted at tree position `start_index + k`, for every `k` below `actual_count` and no
other, and `new_root` is what the tree reaches after those inserts.

The one thing it still does not say is that `frontier_in` is the honest frontier for
`old_root`. That is `FrontierRoot`, modelled nowhere — see the module note. -/
theorem batch_advances_at_positions {depth maxL countBits : ℕ} {w : BatchSignals depth maxL}
    (hmax : 2 ^ countBits = maxL) (hp : 2 ^ (countBits + 2) ≤ p)
    (hpd : 2 ^ (2 * depth) + maxL ≤ p) (h : BatchChainSat countBits w) :
    (∀ k, k < w.actualCount.val →
        w.startIndex.val + k < 4 ^ depth ∧
        InsertsTo depth (w.leaves k)
          (fun d => ((quatDigit (w.startIndex.val + k) d : ℕ) : F))
          (w.fr k) w.zeros (w.fr (k + 1)) (w.runningRoot (k + 1))) ∧
      w.newRoot = w.runningRoot w.actualCount.val := by
  obtain ⟨_, hhi⟩ := batch_count_range hmax (pow_countBits_lt_p hp) h
  refine ⟨fun k hk => ?_, (batch_advances_by_count hmax hp h).2⟩
  have hkm : k < maxL := by omega
  obtain ⟨hfits, hdig⟩ := batch_active_index hmax hp hpd h hkm hk
  exact ⟨hfits,
    ((batch_advances_by_count hmax hp h).1 k hk).digits_congr fun d hd => (hdig d hd).symm⟩

/-! ### The deployed instantiation

`src/tree_update_batch.circom` instantiates `TreeUpdateBatch(11, 8)` with
`COUNT_BITS = 3`. Discharging the side conditions at those numbers is not decoration: it
shows the three bounds the results above carry are *simultaneously satisfiable*, so those
theorems are not conditional on an impossible hypothesis.

`MAX_L = 8` is a floor rather than a choice: `COUNT_BITS` forces a power of two, and a
spend emits `TRANSACT_OUT = 6` leaves that must fit one batch. Six is not a power of two,
so the floor is eight — which is also why `flushBatch` carries four deposits per batch
rather than two. -/

/-- The deployed shape meets both count-side conditions. -/
theorem batch_bounds_deployed : (2 : ℕ) ^ 3 = 8 ∧ (2 : ℕ) ^ (3 + 2) ≤ p := by
  refine ⟨by norm_num, ?_⟩
  unfold p
  norm_num

/-- …and the depth-side one: a `4^11`-leaf tree plus a full batch is far inside the field,
so `batch_active_index` is not vacuous at the deployed shape either. -/
theorem batch_depth_bound_deployed : (2 : ℕ) ^ (2 * 11) + 8 ≤ p := by
  unfold p
  norm_num

/-- `batch_advances_by_count` at `TreeUpdateBatch(11, 8)`, `COUNT_BITS = 3`. -/
theorem batch_advances_by_count_deployed {w : BatchSignals 11 8}
    (h : BatchChainSat 3 w) :
    (∀ k, k < w.actualCount.val →
      InsertsTo 11 (w.leaves k) (w.idxDig k) (w.fr k) w.zeros (w.fr (k + 1))
        (w.runningRoot (k + 1))) ∧
      w.newRoot = w.runningRoot w.actualCount.val :=
  batch_advances_by_count batch_bounds_deployed.1 batch_bounds_deployed.2 h

/-- **`batch_advances_at_positions` at `TreeUpdateBatch(11, 8)`.** Leaf `k` of the batch is
appended at tree position `start_index + k`, that position is inside the tree, and
`new_root` is what the tree reaches after exactly `actual_count` such appends. -/
theorem batch_advances_at_positions_deployed {w : BatchSignals 11 8}
    (h : BatchChainSat 3 w) :
    (∀ k, k < w.actualCount.val →
        w.startIndex.val + k < 4 ^ 11 ∧
        InsertsTo 11 (w.leaves k)
          (fun d => ((quatDigit (w.startIndex.val + k) d : ℕ) : F))
          (w.fr k) w.zeros (w.fr (k + 1)) (w.runningRoot (k + 1))) ∧
      w.newRoot = w.runningRoot w.actualCount.val :=
  batch_advances_at_positions batch_bounds_deployed.1 batch_bounds_deployed.2
    batch_depth_bound_deployed h

/-- `actual_count ∈ [1, 8]` at the deployed shape — odd values included. -/
theorem batch_count_range_deployed {w : BatchSignals 11 8} (h : BatchChainSat 3 w) :
    1 ≤ w.actualCount.val ∧ w.actualCount.val ≤ 8 :=
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
own output at `src/tree_update_batch.circom:381`. -/
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
