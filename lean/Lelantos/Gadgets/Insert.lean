import Lelantos.Gadgets.Common
import Lelantos.Gadgets.Note

/-!
# `src/lib/insert.circom` — incremental quaternary insert

`QuaternaryInsertLevel` (`src/lib/insert.circom:24`) is the append-only sibling of
`MerkleLevel4`. Where a Merkle *proof* surrounds `cur` with three witnessed siblings, an
*insert* knows that everything to the right of the insertion point is still empty, so the
level fills its four children from the frontier on the left and the level's empty-subtree
hash `z` on the right:

                         slot 0     slot 1     slot 2     slot 3
       digit = 0         cur        z          z          z
       digit = 1         f[0]       cur        z          z
       digit = 2         f[0]       f[1]       cur        z
       digit = 3         f[0]       f[1]       f[2]       cur

`insertSlots` is that table, and `quaternaryInsertLevel_sound` shows the four child
equations really compute it — for every digit, so the "everything right of `cur` is empty"
reading is a theorem about the arithmetic rather than a comment.

The frontier update is the second half: `frontier_out[k] = (k == digit) ? cur : f[k]` for
the three stored slots, which is `frontierUpd`. Note it is *not* the same mux as the child
arithmetic — slot 1 needs `(1-s1)·f[1]` where child 1 needs `(s2+s3)·f[1]` — and the circom
comment at `:81-87` flags exactly that. Both are proved here, so a future edit that
collapses them is caught.

As in `MerkleLevel4`, one-hotness of the selector is a prerequisite and not a convenience:
without it the same arithmetic could place `cur` in two slots at once.
-/

namespace Lelantos

/-- The four children of a level: `cur` at the insertion digit, frontier siblings to its
left, empty-subtree hash to its right. Mirrors the table in `src/lib/insert.circom:14-18`. -/
def insertSlots (t : ℕ) (cur : F) (fr : ℕ → F) (zero : F) : ℕ → F := fun k =>
  if k = t then cur else if k < t then fr k else zero

/-- The stored frontier after the insert: slot `t` takes `cur`, the others are unchanged.
Mirrors `src/lib/insert.circom:20`. -/
def frontierUpd (t : ℕ) (cur : F) (fr : ℕ → F) : ℕ → F := fun k =>
  if k = t then cur else fr k

/-- The constraint system of `QuaternaryInsertLevel` — `src/lib/insert.circom:24-96`. -/
structure QuaternaryInsertLevelSat (cur : F) (fr : ℕ → F) (zero idx : F)
    (b s c : ℕ → F) (curNext : F) (fout : ℕ → F) : Prop where
  /-- `:34-35` — the one-hot selector, which also range-checks the digit. -/
  selectors : PathIndexSelectorsSat idx b s
  /-- `:41-43` — `c0 = s0·cur + (1-s0)·f[0]`. -/
  c0_def : c 0 = s 0 * cur + (1 - s 0) * fr 0
  /-- `:50-53` — `c1 = s0·z + s1·cur + (s2+s3)·f[1]`. -/
  c1_def : c 1 = s 0 * zero + s 1 * cur + (s 2 + s 3) * fr 1
  /-- `:60-63` — `c2 = (s0+s1)·z + s2·cur + s3·f[2]`. -/
  c2_def : c 2 = (s 0 + s 1) * zero + s 2 * cur + s 3 * fr 2
  /-- `:69-71` — `c3 = (s0+s1+s2)·z + s3·cur`. -/
  c3_def : c 3 = (s 0 + s 1 + s 2) * zero + s 3 * cur
  /-- `:73-79` — `cur_next = Poseidon(TAG_MERKLE, c0, c1, c2, c3)`. -/
  out_def : curNext = merkleNode c
  /-- `:93` — `frontier_out[0] = s0·cur + (1-s0)·f[0]`. -/
  fout0_def : fout 0 = s 0 * cur + (1 - s 0) * fr 0
  /-- `:94` — `frontier_out[1] = s1·cur + (1-s1)·f[1]`. -/
  fout1_def : fout 1 = s 1 * cur + (1 - s 1) * fr 1
  /-- `:95` — `frontier_out[2] = s2·cur + (1-s2)·f[2]`. -/
  fout2_def : fout 2 = s 2 * cur + (1 - s 2) * fr 2

/-- **Soundness of `QuaternaryInsertLevel`.** The digit is quaternary, the parent hashes
the fill table, and the frontier is updated at exactly the insertion slot. -/
theorem quaternaryInsertLevel_sound {cur zero idx curNext : F} {fr b s c fout : ℕ → F}
    (h : QuaternaryInsertLevelSat cur fr zero idx b s c curNext fout) :
    idx.val < 4 ∧ curNext = merkleNode (insertSlots idx.val cur fr zero) ∧
      ∀ k, k < 3 → fout k = frontierUpd idx.val cur fr k := by
  obtain ⟨hsel, hc0, hc1, hc2, hc3, hout, hf0, hf1, hf2⟩ := h
  obtain ⟨hlt, hone⟩ := pathIndexSelectors_sound hsel
  have h0 := hone 0 (by norm_num)
  have h1 := hone 1 (by norm_num)
  have h2 := hone 2 (by norm_num)
  have h3 := hone 3 (by norm_num)
  clear hone hsel
  refine ⟨hlt, ?_, ?_⟩
  · -- One case per digit; the selector is one-hot, so each child equation collapses to
    -- the corresponding row of the fill table.
    have key : ∀ k, k < 4 → c k = insertSlots idx.val cur fr zero k := by
      intro k hk
      interval_cases hidx : idx.val <;> norm_num at h0 h1 h2 h3 <;>
        rw [h0] at hc0 hc1 hc2 hc3 <;> rw [h1] at hc1 hc2 hc3 <;>
        rw [h2] at hc1 hc2 hc3 <;> rw [h3] at hc1 hc2 hc3 <;>
        interval_cases k <;> simp only [insertSlots, hc0, hc1, hc2, hc3] <;> norm_num
    rw [hout, merkleNode, merkleNode, key 0 (by norm_num), key 1 (by norm_num),
      key 2 (by norm_num), key 3 (by norm_num)]
  · intro k hk
    interval_cases hidx : idx.val <;> norm_num at h0 h1 h2 <;>
      rw [h0] at hf0 <;> rw [h1] at hf1 <;> rw [h2] at hf2 <;>
      interval_cases k <;> simp only [frontierUpd, hf0, hf1, hf2] <;> norm_num

/-- The constraint system of `QuaternaryInsert(depth)` — `src/lib/insert.circom:99-128`.
`cur` is the chain of running nodes, `frIn`/`frOut` the per-level frontier arrays. -/
structure QuaternaryInsertSat (depth : ℕ) (leaf : F) (dig : ℕ → F)
    (frIn : ℕ → ℕ → F) (zeros : ℕ → F) (b s c : ℕ → ℕ → F)
    (cur : ℕ → F) (frOut : ℕ → ℕ → F) (root : F) : Prop where
  /-- `:111` — the chain starts at the leaf. -/
  base : cur 0 = leaf
  /-- `:113-125` — one `QuaternaryInsertLevel` per level. -/
  level : ∀ d, d < depth →
    QuaternaryInsertLevelSat (cur d) (frIn d) (zeros d) (dig d) (b d) (s d) (c d)
      (cur (d + 1)) (frOut d)
  /-- `:127` — the root is the top of the chain. -/
  top : root = cur depth

/-- What an insert *means*, with no reference to selector or intermediate signals: a hash
chain folding the leaf upwards through the fill table, together with the frontier it leaves
behind. The counterpart of `MerkleMember` for the append direction. -/
def InsertsTo (depth : ℕ) (leaf : F) (dig : ℕ → F) (frIn : ℕ → ℕ → F) (zeros : ℕ → F)
    (frOut : ℕ → ℕ → F) (root : F) : Prop :=
  ∃ chain : ℕ → F,
    chain 0 = leaf ∧
    (∀ d, d < depth →
      chain (d + 1) = merkleNode (insertSlots (dig d).val (chain d) (frIn d) (zeros d))) ∧
    root = chain depth ∧
    ∀ d, d < depth → ∀ j, j < 3 → frOut d j = frontierUpd (dig d).val (chain d) (frIn d) j

/-- **The insert is a function of its inputs.** Two `InsertsTo` witnesses over the same
leaf, digits, frontier and empty-subtree hashes produce the same root and the same frontier.

This is what stops `InsertsTo` being the near-tautology `MerkleMember` is. There the chain is
witnessed and only Poseidon collision resistance ties it to the root (`merkleMember_inj`);
here `chain 0 = leaf` and the step equation determine every node outright, so the root is
pinned by plain induction and no hash assumption appears. -/
theorem InsertsTo.unique {depth : ℕ} {leaf root root' : F} {dig zeros : ℕ → F}
    {frIn frOut frOut' : ℕ → ℕ → F}
    (h : InsertsTo depth leaf dig frIn zeros frOut root)
    (h' : InsertsTo depth leaf dig frIn zeros frOut' root') :
    root = root' ∧ ∀ d, d < depth → ∀ j, j < 3 → frOut d j = frOut' d j := by
  obtain ⟨c, hb, hs, ht, hf⟩ := h
  obtain ⟨c', hb', hs', ht', hf'⟩ := h'
  have hall : ∀ d, d ≤ depth → c d = c' d := by
    intro d
    induction d with
    | zero => intro _; rw [hb, hb']
    | succ m ih =>
      intro hm
      rw [hs m (by omega), hs' m (by omega), ih (by omega)]
  refine ⟨by rw [ht, ht', hall depth le_rfl], fun d hd j hj => ?_⟩
  rw [hf d hd j hj, hf' d hd j hj, hall d (by omega)]

/-- `InsertsTo` only constrains `frOut` below `depth` and `3`, and `root` up to equality, so
an assignment agreeing there inserts to the same place. Used to move the statement off a
circuit's private output signals and onto whatever the caller muxes them into. -/
theorem InsertsTo.retarget {depth : ℕ} {leaf root root' : F} {dig zeros : ℕ → F}
    {frIn frOut frOut' : ℕ → ℕ → F}
    (h : InsertsTo depth leaf dig frIn zeros frOut root)
    (hfr : ∀ d, d < depth → ∀ j, j < 3 → frOut' d j = frOut d j) (hroot : root' = root) :
    InsertsTo depth leaf dig frIn zeros frOut' root' := by
  obtain ⟨chain, hbase, hstep, htop, hfrontier⟩ := h
  exact ⟨chain, hbase, hstep, hroot.trans htop,
    fun d hd j hj => (hfr d hd j hj).trans (hfrontier d hd j hj)⟩

/-- **Soundness of `QuaternaryInsert`.** A satisfying assignment exhibits a genuine insert:
every level hashes the fill table, every frontier slot is updated at exactly the insertion
position, and every digit is a valid quaternary digit. -/
theorem quaternaryInsert_sound {depth : ℕ} {leaf root : F} {dig zeros : ℕ → F}
    {frIn frOut b s c : ℕ → ℕ → F} {cur : ℕ → F}
    (h : QuaternaryInsertSat depth leaf dig frIn zeros b s c cur frOut root) :
    InsertsTo depth leaf dig frIn zeros frOut root ∧ ∀ d, d < depth → (dig d).val < 4 :=
  ⟨⟨cur, h.base,
      fun d hd => (quaternaryInsertLevel_sound (h.level d hd)).2.1,
      h.top,
      fun d hd => (quaternaryInsertLevel_sound (h.level d hd)).2.2⟩,
    fun d hd => (quaternaryInsertLevel_sound (h.level d hd)).1⟩

end Lelantos
