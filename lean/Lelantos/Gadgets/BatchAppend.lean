import Lelantos.Spec.QuatTree
import Lelantos.Gadgets.Comparators

/-!
# `src/lib/batch_append.circom` — the tree before and after a batch

`BatchAppend(DEPTH, MAX_L)` (`src/lib/batch_append.circom:107-249`) computes both roots of a
batch append from one frontier, and owns every range check its reading rests on. The
construction is explained once, in that file's header; this module transcribes the constraint
system (`BatchAppendSat`) and proves it computes the specification in `Spec/QuatTree.lean`:

* `batchAppend_count_range`, `batchAppend_active_spec` — `actual_count ∈ [1, MAX_L]` and the
  exported `active` is the prefix indicator.
* `batchAppend_start`, `batchAppend_capacity` — `start_index` is the position its bits
  denote, and the run fits the tree.
* `batchAppend_frontier_zero` — every frontier slot no digit reads is zero.
* `batchAppend_old_root` — the old root is `batchTree … 0 …`, the tree before the append.
* `batchAppend_new_root` — the new root is that tree after the append; `batchAppend_window`
  is the same statement at every window node.
* `batchAppend_sound` — capacity and both roots together.

Every result takes a `BatchShape`, the numeric side conditions of an instance. Both roots
read a frontier slot as a plain linear term, which is sound only under the zero pin
(`frontier_pin`): `frontier_term_zero` is where that is used.
-/

namespace Lelantos

/-! ## The window width -/

/-- `BATCH_WINDOW(DEPTH, n, d)` — `src/lib/batch_append.circom:58-71`. The worst-case number
of level-`d` nodes that `n` consecutive leaves change: `n` at the leaves, then
`(n - 2) \ 4^d + 2` capped at the level's width `4^(DEPTH - d)`. -/
def batchWindow (depth n d : ℕ) : ℕ :=
  if d = 0 then n else min (if 2 ≤ n then (n - 2) / 4 ^ d + 2 else 1) (4 ^ (depth - d))

/-- The top window is the single root node — `src/lib/batch_append.circom:204`,
`assert(W[DEPTH] == 1)`. -/
theorem batchWindow_top {depth maxL : ℕ} (hd : 1 ≤ depth) : batchWindow depth maxL depth = 1 := by
  have hA : 1 ≤ (if 2 ≤ maxL then (maxL - 2) / 4 ^ depth + 2 else 1) := by
    split
    · exact le_trans (by norm_num) (Nat.le_add_left 2 _)
    · exact le_rfl
  simp only [batchWindow, if_neg (show depth ≠ 0 by omega), Nat.sub_self, pow_zero]
  exact min_eq_right hA

/-- **The window is wide enough.** For every start position and every count up to `maxL`
that fits the tree, the level-`d` nodes the run touches, `S / 4^d` through
`(S + n - 1) / 4^d`, all lie inside the window. -/
theorem batchWindow_covers {depth maxL S n d : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ maxL)
    (hcap : S + n ≤ 4 ^ depth) (hd : d ≤ depth) :
    (S + n - 1) / 4 ^ d + 1 ≤ S / 4 ^ d + batchWindow depth maxL d := by
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · simp [batchWindow]; omega
  have hm := four_pow_pos d
  set m := 4 ^ d with hm_def
  set a := S / m with ha
  set c := (S + n - 1) / m with hc
  clear_value a c
  simp only [batchWindow, if_neg (show d ≠ 0 by omega)]
  rw [← min_add_add_left]
  apply le_min
  · -- The run spans at most `(n - 2) / m + 2` nodes: its first sits at `a`, and every
    -- further node needs a full `m` more leaves.
    have hSa : S < m * (a + 1) := ha ▸ Nat.lt_mul_div_succ S hm
    have hcS : c * m ≤ S + n - 1 := hc ▸ Nat.div_mul_le_self _ _
    split
    · rename_i h2
      have he : n - 2 < m * ((n - 2) / m + 1) := Nat.lt_mul_div_succ (n - 2) hm
      have hmono : (n - 2) / m ≤ (maxL - 2) / m := Nat.div_le_div_right (by omega)
      have hsplit : ∀ x : ℕ, (a + x + 2) * m = m * (a + 1) + m * (x + 1) := fun x => by ring
      generalize (n - 2) / m = e at he hmono hsplit ⊢
      generalize (maxL - 2) / m = E at hmono ⊢
      by_contra hlt
      have hge : a + e + 2 ≤ c := by omega
      have hmul := Nat.mul_le_mul_right m hge
      have := hsplit e
      generalize m * (a + 1) = X at hSa this
      generalize m * (e + 1) = Y at he this
      generalize (a + e + 2) * m = Z at hmul this
      generalize c * m = W at hcS hmul
      omega
    · have hn1' : n = 1 := by omega
      subst hn1'
      have : S + 1 - 1 = S := by omega
      rw [this] at hc
      omega
  · -- …and never past the level's own width, since the run ends inside the tree.
    have htop : S + n - 1 < 4 ^ (depth - d) * m := by
      rw [hm_def, ← pow_add, Nat.sub_add_cancel hd]; omega
    have : (S + n - 1) / m < 4 ^ (depth - d) := (Nat.div_lt_iff_lt_mul hm).2 htop
    rw [← hc] at this
    generalize 4 ^ (depth - d) = K at this ⊢
    omega

/-! ## Selectors -/

/-- The digit selectors — `src/lib/batch_append.circom:155-158`, `s[d][r]` as a linear
combination of the two bits `b0`, `b1` and their product `bb`. -/
def batchSel (b0 b1 bb : F) (r : ℕ) : F :=
  if r = 0 then 1 - b0 - b1 + bb else if r = 1 then b0 - bb else if r = 2 then b1 - bb else bb

/-- With boolean bits and `bb = b0·b1`, the selector is one-hot at `b0 + 2·b1`. -/
theorem batchSel_onehot {b0 b1 bb : F} (h0 : IsBit b0) (h1 : IsBit b1) (hbb : bb = b0 * b1)
    {r : ℕ} (hr : r < 4) :
    batchSel b0 b1 bb r = if r = bitNat b0 + 2 * bitNat b1 then 1 else 0 := by
  subst hbb
  rcases isBit_iff.mp h0 with rfl | rfl <;> rcases isBit_iff.mp h1 with rfl | rfl <;>
    interval_cases r <;> simp [batchSel, bitNat]

/-! ## Sources -/

/-- Where a child reads from. -/
inductive BatchSrc where
  | frontier
  | node (p : ℕ)
  | empty

/-- The source of child `k` of window slot `j`, at digit `r`, over a lower window of width
`w` — the classification `p = 4j + k - r` at `src/lib/batch_append.circom:76-85`. -/
def batchSrc (w j k r : ℕ) : BatchSrc :=
  if 4 * j + k < r then .frontier else if 4 * j + k - r < w then .node (4 * j + k - r)
  else .empty

/-! ### The classification, against the circuit's own arithmetic

`batchSrc` works in `ℕ`, where `4j + k - r` truncates. The circuit computes `p = 4 * j + k - r`
as a circom `var`, a field element, and `p < 0` compares in circom's signed reading of the
field, which for these small values is the integer value. `circomSrc` is that computation in
`ℤ`, transcribed literally, and `batchSrc_eq_circom` shows the two agree everywhere — so the
`ℕ` phrasing loses nothing. The same holds for `BATCH_WINDOW`'s clamp against `batchWindow`'s
`min`, at every shape. -/

/-- `BATCH_SRC` at `:76-85` in `ℤ`, as circom evaluates it. -/
def circomSrc (w j k r : ℕ) : BatchSrc :=
  let p : ℤ := 4 * (j : ℤ) + k - r
  if p < 0 then .frontier else if p < (w : ℤ) then .node p.toNat else .empty

theorem batchSrc_eq_circom (w j k r : ℕ) : batchSrc w j k r = circomSrc w j k r := by
  unfold batchSrc circomSrc
  simp only
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- `BATCH_WINDOW` (`src/lib/batch_append.circom:58-71`) as circom writes it: a clamp rather
than a `min`. `BatchAppend` evaluates it only at `d ≤ DEPTH`, where `4 ** (DEPTH - d)` on the
field is the natural `4 ^ (DEPTH - d)`. -/
def circomWindow (DEPTH n d : ℕ) : ℕ :=
  if d = 0 then n else
  let w := if n ≥ 2 then (n - 2) / 4 ^ d + 2 else 1
  let cap := 4 ^ (DEPTH - d)
  if w > cap then cap else w

theorem batchWindow_eq_circom (DEPTH n d : ℕ) : batchWindow DEPTH n d = circomWindow DEPTH n d := by
  unfold batchWindow circomWindow
  split_ifs <;> simp only [min_def] <;> split_ifs <;> omega

/-- The value a source names. -/
def BatchSrc.val (fr node : ℕ → F) (zero : F) (k : ℕ) : BatchSrc → F
  | .frontier => fr k
  | .node p => node p
  | .empty => zero

/-- The coefficient a frontier slot is read with: the selectors for digits above it —
`read` at `src/lib/batch_append.circom:164-167`. -/
def batchRead (sel : ℕ → F) (k : ℕ) : F := ∑ r ∈ Finset.Ico (k + 1) 4, sel r

/-- Under one-hot selectors, frontier slot `k` is read exactly when the digit lies above it. -/
theorem batchRead_onehot {b0 b1 : F} (h0 : IsBit b0) (h1 : IsBit b1) (k : ℕ) :
    batchRead (batchSel b0 b1 (b0 * b1)) k = if k < bitNat b0 + 2 * bitNat b1 then 1 else 0 := by
  unfold batchRead
  rw [Finset.sum_congr rfl fun r hr => by
    rw [batchSel_onehot h0 h1 rfl (by simp only [Finset.mem_Ico] at hr; omega)]]
  rw [Finset.sum_ite_eq']
  have := bitNat_le_one b0
  have := bitNat_le_one b1
  simp only [Finset.mem_Ico]
  split_ifs <;> first | rfl | omega

/-! ## The two kinds of child -/

/-- Child `k` of the old-root node at a level: the frontier slot as a linear term (`k < 3`),
the running node weighted by its digit's selector, and the empty subtree weighted by the
selectors below `k`. -/
def oldChild (sel : ℕ → F) (fr : ℕ → F) (cur zero : F) (k : ℕ) : F :=
  (if k < 3 then fr k else 0) + sel k * cur + (∑ r ∈ Finset.range k, sel r) * zero

/-- Child `k` of window slot `j` in the new root: the frontier slot as a linear term exactly
when some digit reads it (`4j + k < 3`), plus the selector-weighted window node or empty
subtree each digit names. A frontier source contributes nothing to the sum. -/
def batchChild (sel : ℕ → F) (w j k : ℕ) (fr node : ℕ → F) (zero : F) : F :=
  (if 4 * j + k < 3 then fr k else 0) +
    ∑ r ∈ Finset.range 4, sel r * (batchSrc w j k r).val (fun _ => 0) node zero k

/-! ## The constraint system -/

/-- The numeric side conditions of a `BatchAppend(depth, maxL)` instance with
`COUNT_BITS = countBits`. `BatchShape.deployed` discharges them at the deployed shape. -/
structure BatchShape (depth maxL countBits : ℕ) : Prop where
  /-- `assert((1 << COUNT_BITS) == MAX_L)` at `src/lib/batch_append.circom:130`. -/
  pow_count : 2 ^ countBits = maxL
  /-- `LessThan(COUNT_BITS + 1)` decomposes `COUNT_BITS + 2` bits without aliasing. -/
  count_lt_p : 2 ^ (countBits + 2) ≤ p
  /-- `Num2Bits(2·DEPTH)` of `start_index + actual_count - 1` does not alias. -/
  depth_lt_p : 2 ^ (2 * depth) + maxL ≤ p
  /-- There is a level above the leaves, so the top window is the root. -/
  depth_pos : 1 ≤ depth

theorem BatchShape.pow_count_lt_p {depth maxL countBits : ℕ}
    (hs : BatchShape depth maxL countBits) : 2 ^ countBits < p := by
  have h1 : 2 ^ (countBits + 1) = 2 ^ countBits * 2 := pow_succ 2 countBits
  have h2 : 2 ^ (countBits + 2) = 2 ^ (countBits + 1) * 2 := pow_succ 2 (countBits + 1)
  have := hs.count_lt_p
  have := p_pos
  omega

/-- The signals `BatchAppend` declares beyond its inputs. Array signals are total functions,
read only below their declared length; `node d t` is the flat `node[OFF[d] + t]`. -/
structure BatchAppendSignals where
  cntBits : ℕ → F
  ltBits : ℕ → ℕ → F
  active : ℕ → F
  idxBits : ℕ → F
  lastIdxBits : ℕ → F
  bb : ℕ → F
  oldNode : ℕ → F
  node : ℕ → ℕ → F
  oldRoot : F
  newRoot : F

/-- The paired-bit products `bb[d] = bits[2d] · bits[2d+1]`. -/
abbrev bitPairs (bits : ℕ → F) : ℕ → F := fun d => bits (2 * d) * bits (2 * d + 1)

/-- The digit selectors of level `d` over the index bits. -/
abbrev appendSel (idxBits bb : ℕ → F) (d : ℕ) : ℕ → F :=
  batchSel (idxBits (2 * d)) (idxBits (2 * d + 1)) (bb d)

/-- The constraint system of `BatchAppend(depth, maxL)` with `COUNT_BITS = countBits` —
`src/lib/batch_append.circom:107-249` — over the inputs `start_index`, `actual_count`,
`leaves` and `frontier_in`. `zeros` is `EMPTY_SUBTREE`, a free parameter as everywhere else
in the model. -/
structure BatchAppendSat (depth maxL countBits : ℕ) (zeros : ℕ → F) (startIndex actualCount : F)
    (leaves : ℕ → F) (frIn : ℕ → ℕ → F) (a : BatchAppendSignals) : Prop where
  /-- `:131-132` — `Num2Bits(COUNT_BITS)` on `actual_count - 1`. -/
  count_bits : Num2BitsSat countBits (actualCount - 1) a.cntBits
  /-- `:134-140` — `active[k] = LessThan(COUNT_BITS+1)(k, actual_count)`. -/
  active_def : ∀ k, k < maxL →
    LessThanSat (countBits + 1) ((k : ℕ) : F) actualCount (a.ltBits k) (a.active k)
  /-- `:145-146` — `idx_bits = Num2Bits(BITS)(start_index)`. -/
  index_bits : Num2BitsSat (2 * depth) startIndex a.idxBits
  /-- `:147-148` — `last_idx_bits.in <== start_index + actual_count - 1`. -/
  last_idx_bits : Num2BitsSat (2 * depth) (startIndex + actualCount - 1) a.lastIdxBits
  /-- `:154` — `bb[d] <== idx_bits.out[2 * d] * idx_bits.out[2 * d + 1]`. -/
  bb_def : ∀ d, d < depth → a.bb d = bitPairs a.idxBits d
  /-- `:162-170` — `(1 - read) * frontier_in[d][k] === 0`. -/
  frontier_pin : ∀ d, d < depth → ∀ k, k < 3 →
    (1 - batchRead (appendSel a.idxBits a.bb d) k) * frIn d k = 0
  /-- `:176` — `old_node[0] <== 0`. -/
  old_base : a.oldNode 0 = 0
  /-- `:177-192` — each old-root node hashes its four children, `old_prod[d][k] <== s[d][k] *
  old_node[d]` among them. -/
  old_def : ∀ d, d < depth →
    a.oldNode (d + 1) =
      merkleNode (oldChild (appendSel a.idxBits a.bb d) (frIn d) (a.oldNode d) (zeros d))
  /-- `:193` — `old_root <== old_node[DEPTH]`. -/
  old_root_def : a.oldRoot = a.oldNode depth
  /-- `:207-209` — `node[OFF[0] + t] <== active[t] * leaves[t]`. -/
  leaf_def : ∀ t, t < maxL → a.node 0 t = a.active t * leaves t
  /-- `:225-241` — each window node's four children, `prod[pi] <== s[d][r] * node[OFF[d] +
  src]` among them, hashed into `node` at `:243` with `h[hi].inputs[0] <== tag` at `:223`. -/
  node_def : ∀ d, d < depth → ∀ j, j < batchWindow depth maxL (d + 1) →
    a.node (d + 1) j = merkleNode (fun k =>
      batchChild (appendSel a.idxBits a.bb d) (batchWindow depth maxL d) j k (frIn d) (a.node d)
        (zeros d))
  /-- `:248` — `new_root <== node[OFF[DEPTH]]`. -/
  new_root_def : a.newRoot = a.node depth 0

/-! ## Soundness -/

section Soundness

variable {depth maxL countBits : ℕ} {zeros : ℕ → F} {startIndex actualCount : F}
  {leaves : ℕ → F} {frIn : ℕ → ℕ → F} {a : BatchAppendSignals}

/-- **The count is in range.** `actual_count ∈ [1, maxL]`: `0` would need `Num2Bits` to
decompose `p - 1`, which is why the circuit checks `actual_count - 1`. -/
theorem batchAppend_count_range (hs : BatchShape depth maxL countBits)
    (h : BatchAppendSat depth maxL countBits zeros startIndex actualCount leaves frIn a) :
    1 ≤ actualCount.val ∧ actualCount.val ≤ maxL := by
  have hp := hs.pow_count_lt_p
  obtain ⟨hval, _⟩ := num2Bits_sound (le_of_lt hp) h.count_bits
  have hlt : (actualCount - 1).val < 2 ^ countBits := by
    rw [hval]; exact bitsNat_lt _ _
  have hsucc : actualCount = (((actualCount - 1).val + 1 : ℕ) : F) := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    ring
  have hmp : (actualCount - 1).val + 1 < p := by omega
  rw [hsucc, ZMod.val_natCast_of_lt hmp]
  have := hs.pow_count
  omega

/-- **`active` is the prefix indicator** of `actual_count`. -/
theorem batchAppend_active_spec (hs : BatchShape depth maxL countBits)
    (h : BatchAppendSat depth maxL countBits zeros startIndex actualCount leaves frIn a) :
    ∀ k, k < maxL → a.active k = ind (k < actualCount.val) := by
  have hstep : 2 ^ (countBits + 1) = 2 ^ countBits * 2 := pow_succ 2 countBits
  have hmax := hs.pow_count
  obtain ⟨hlo, hhi⟩ := batchAppend_count_range hs h
  intro k hk
  have hkp : k < p := by have := hs.pow_count_lt_p; omega
  have hkval : (((k : ℕ) : F)).val = k := ZMod.val_natCast_of_lt hkp
  have hka : (((k : ℕ) : F)).val < 2 ^ (countBits + 1) := by omega
  have hca : actualCount.val < 2 ^ (countBits + 1) := by omega
  have := lessThan_sound hs.count_lt_p hka hca (h.active_def k hk)
  rwa [hkval] at this

/-- **`start_index` is the position its bits denote**, inside the tree. -/
theorem batchAppend_start (hs : BatchShape depth maxL countBits)
    (h : BatchAppendSat depth maxL countBits zeros startIndex actualCount leaves frIn a) :
    startIndex.val = bitsNat a.idxBits (2 * depth) ∧ startIndex.val < 4 ^ depth := by
  obtain ⟨hval, hlt⟩ := num2Bits_sound (by have := hs.depth_lt_p; omega) h.index_bits
  exact ⟨hval, by rw [four_pow_eq_two_pow]; exact hlt⟩

/-- **The run fits the tree.** `start_index + actual_count ≤ 4^depth`. -/
theorem batchAppend_capacity (hs : BatchShape depth maxL countBits)
    (h : BatchAppendSat depth maxL countBits zeros startIndex actualCount leaves frIn a) :
    startIndex.val + actualCount.val ≤ 4 ^ depth := by
  obtain ⟨hlo, hhi⟩ := batchAppend_count_range hs h
  obtain ⟨_, hS⟩ := batchAppend_start hs h
  have hpd := hs.depth_lt_p
  rw [four_pow_eq_two_pow] at hS ⊢
  obtain ⟨_, hlast⟩ := num2Bits_sound (by omega) h.last_idx_bits
  have hsum : startIndex.val + (actualCount.val - 1) < p := by omega
  have heq : startIndex + actualCount - 1 =
      (((startIndex.val + (actualCount.val - 1) : ℕ)) : F) := by
    rw [Nat.cast_add, Nat.cast_sub hlo, Nat.cast_one, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val]
    ring
  rw [heq, ZMod.val_natCast_of_lt hsum] at hlast
  omega

/-- On a satisfying assignment the level-`d` selector is one-hot at digit `d` of
`start_index`. -/
theorem batchAppend_sel (hs : BatchShape depth maxL countBits)
    (h : BatchAppendSat depth maxL countBits zeros startIndex actualCount leaves frIn a)
    {d : ℕ} (hd : d < depth) {r : ℕ} (hr : r < 4) :
    appendSel a.idxBits a.bb d r = if r = quatDigit startIndex.val d then 1 else 0 := by
  rw [appendSel, batchSel_onehot (h.index_bits.bits _ (by omega)) (h.index_bits.bits _ (by omega))
    (h.bb_def d hd) hr, (batchAppend_start hs h).1, quatDigit_eq_bits (by omega)]

/-- **No free frontier slot.** Every slot at or above its level's digit of `start_index` is
zero. -/
theorem batchAppend_frontier_zero (hs : BatchShape depth maxL countBits)
    (h : BatchAppendSat depth maxL countBits zeros startIndex actualCount leaves frIn a)
    {d : ℕ} (hd : d < depth) {k : ℕ} (hk : k < 3) (hge : quatDigit startIndex.val d ≤ k) :
    frIn d k = 0 := by
  have hpin := h.frontier_pin d hd k hk
  rw [(batchAppend_start hs h).1, quatDigit_eq_bits (by omega)] at hge
  rwa [appendSel, h.bb_def d hd, bitPairs,
    batchRead_onehot (h.index_bits.bits _ (by omega)) (h.index_bits.bits _ (by omega)) k,
    if_neg (by omega), sub_zero, one_mul] at hpin

/-- The pin, as both roots use it: a frontier term guarded by `c < 3`, for a slot `k ≤ c`
at or above the digit whenever the guard holds, vanishes. -/
private theorem frontier_term_zero (hs : BatchShape depth maxL countBits)
    (h : BatchAppendSat depth maxL countBits zeros startIndex actualCount leaves frIn a)
    {d : ℕ} (hd : d < depth) {c k : ℕ} (hkc : k ≤ c)
    (hge : c < 3 → quatDigit startIndex.val d ≤ k) :
    (if c < 3 then frIn d k else 0) = 0 := by
  split_ifs with h3
  · exact batchAppend_frontier_zero hs h hd (by omega) (hge h3)
  · rfl

/-- A selector-weighted sum over the four digits picks out the digit's term. -/
private theorem sum_sel (hs : BatchShape depth maxL countBits)
    (h : BatchAppendSat depth maxL countBits zeros startIndex actualCount leaves frIn a)
    {d : ℕ} (hd : d < depth) {m : ℕ} (hm : m ≤ 4) (f : ℕ → F) :
    ∑ r ∈ Finset.range m, appendSel a.idxBits a.bb d r * f r =
      if quatDigit startIndex.val d < m then f (quatDigit startIndex.val d) else 0 := by
  rw [Finset.sum_congr rfl fun r hr => by
    rw [batchAppend_sel hs h hd (by simp only [Finset.mem_range] at hr; omega)]]
  simp [ite_mul, Finset.sum_ite_eq', Finset.mem_range]

/-- **The old root's children are the fill table.** Under the pin, `oldChild` is
`insertSlots` at the level's digit: frontier to the left, the running node at the digit, the
empty subtree to the right. -/
private theorem old_child (hs : BatchShape depth maxL countBits)
    (h : BatchAppendSat depth maxL countBits zeros startIndex actualCount leaves frIn a)
    {d : ℕ} (hd : d < depth) (cur : F) {k : ℕ} (hk : k < 4) :
    oldChild (appendSel a.idxBits a.bb d) (frIn d) cur (zeros d) k =
      insertSlots (quatDigit startIndex.val d) cur (frIn d) (zeros d) k := by
  have hlow := sum_sel hs h hd (show k ≤ 4 by omega) (fun _ => (1 : F))
  simp only [mul_one] at hlow
  have hfz : ∀ {k'}, quatDigit startIndex.val d ≤ k' → (if k' < 3 then frIn d k' else 0) = 0 :=
    fun hge => frontier_term_zero hs h hd le_rfl fun _ => hge
  have hr4 := quatDigit_lt startIndex.val d
  unfold oldChild insertSlots
  rw [batchAppend_sel hs h hd hk, hlow]
  generalize quatDigit startIndex.val d = r at hr4 hfz ⊢
  by_cases hkr : k = r
  · subst hkr
    simp [hfz le_rfl]
  · by_cases hlt : k < r
    · simp [hkr, hlt, show k < 3 by omega, show ¬ r < k by omega]
    · simp [hfz (show r ≤ k by omega), hkr, hlt, show r < k by omega]

/-- **The new root's children are the sources.** Under the pin, `batchChild` is the value of
the source its level's digit selects. -/
private theorem new_child (hs : BatchShape depth maxL countBits)
    (h : BatchAppendSat depth maxL countBits zeros startIndex actualCount leaves frIn a)
    {d : ℕ} (hd : d < depth) (w j k : ℕ) :
    batchChild (appendSel a.idxBits a.bb d) w j k (frIn d) (a.node d) (zeros d) =
      (batchSrc w j k (quatDigit startIndex.val d)).val (frIn d) (a.node d) (zeros d) k := by
  have hr4 := quatDigit_lt startIndex.val d
  unfold batchChild
  rw [sum_sel hs h hd le_rfl, if_pos hr4]
  by_cases hf : 4 * j + k < quatDigit startIndex.val d
  · simp [batchSrc, hf, show 4 * j + k < 3 by omega, BatchSrc.val]
  · rw [frontier_term_zero (c := 4 * j + k) hs h hd (by omega) (fun _ => by omega), zero_add]
    simp only [batchSrc, if_neg hf]
    split_ifs <;> rfl

/-- **The old path is the tree before the append.** `old_node[d]` is the level-`d` node on
the insertion path of the tree holding `start_index` leaves with this frontier. -/
theorem batchAppend_old (hs : BatchShape depth maxL countBits) (hz : ZerosCoherent zeros)
    (h : BatchAppendSat depth maxL countBits zeros startIndex actualCount leaves frIn a) :
    ∀ d, d ≤ depth →
      a.oldNode d = batchTree startIndex.val 0 leaves frIn zeros d (startIndex.val / 4 ^ d) := by
  set S := startIndex.val with hS
  intro d
  induction d with
  | zero =>
    intro _
    simp only [pow_zero, Nat.div_one]
    rw [h.old_base, batchTree_leaf le_rfl, if_neg (by omega), hz.1]
  | succ d ih =>
    intro hd
    have hdd : d < depth := by omega
    have hsplit := div_four_pow_split S d
    have hr := quatDigit_lt S d
    rw [h.old_def d hdd, batchTree_node le_rfl]
    apply merkleNode_congr
    intro c hc
    rw [old_child hs h hdd _ hc, ← hS]
    unfold insertSlots
    split_ifs with heq hlt
    · rw [ih (by omega)]
      congr 1
      omega
    · rw [batchTree_frontier (by omega)]
      congr 1
      omega
    · have := (Nat.div_lt_iff_lt_mul (four_pow_pos d)).1
        (show S / 4 ^ d < 4 * (S / 4 ^ (d + 1)) + c by omega)
      rw [batchTree_empty hz d _ (by omega) (by omega)]

/-- **Every window node is the tree node it stands for** after the append. -/
theorem batchAppend_window (hs : BatchShape depth maxL countBits) (hz : ZerosCoherent zeros)
    (h : BatchAppendSat depth maxL countBits zeros startIndex actualCount leaves frIn a) :
    ∀ d, d ≤ depth → ∀ t, t < batchWindow depth maxL d →
      a.node d t = batchTree startIndex.val actualCount.val leaves frIn zeros d
        (startIndex.val / 4 ^ d + t) := by
  obtain ⟨hn1, hn⟩ := batchAppend_count_range hs h
  have hcap := batchAppend_capacity hs h
  have hact := batchAppend_active_spec hs h
  set S := startIndex.val with hS
  set n := actualCount.val with hn_def
  intro d
  induction d with
  | zero =>
    intro _ t ht
    have ht' : t < maxL := by simpa [batchWindow] using ht
    simp only [pow_zero, Nat.div_one]
    rw [h.leaf_def t ht', batchTree_leaf (Nat.le_add_right S t), hact t ht',
      Nat.add_sub_cancel_left, ind]
    by_cases htn : t < n
    · rw [if_pos htn, if_pos (by omega), one_mul]
    · rw [if_neg htn, if_neg (by omega), zero_mul, hz.1]
  | succ d ih =>
    intro hd t ht
    have hdd : d < depth := by omega
    have hsplit := div_four_pow_split S d
    have hr := quatDigit_lt S d
    set r := quatDigit S d with hr_def
    set lo := S / 4 ^ (d + 1) with hlo
    rw [h.node_def d hdd t ht, batchTree_node (show lo ≤ lo + t by omega)]
    apply merkleNode_congr
    intro k hk
    rw [new_child hs h hdd, ← hS, ← hr_def]
    unfold batchSrc
    split_ifs with hf hn'
    · have ht0 : t = 0 := by omega
      subst ht0
      simp only [BatchSrc.val]
      rw [batchTree_frontier (show 4 * (lo + 0) + k < S / 4 ^ d by omega)]
      congr 1
      omega
    · simp only [BatchSrc.val]
      rw [ih (by omega) _ hn']
      congr 1
      omega
    · simp only [BatchSrc.val]
      have hcov := batchWindow_covers (maxL := maxL) hn1 hn hcap (show d ≤ depth by omega)
      have hlt : S + n - 1 < (4 * (lo + t) + k) * 4 ^ d :=
        (Nat.div_lt_iff_lt_mul (four_pow_pos d)).1 (by omega)
      rw [batchTree_empty hz d _ (by omega) (by omega)]

/-- **The old root is the tree before the append**: the tree holding `start_index` leaves
whose frontier is `frontier_in`. -/
theorem batchAppend_old_root (hs : BatchShape depth maxL countBits) (hz : ZerosCoherent zeros)
    (h : BatchAppendSat depth maxL countBits zeros startIndex actualCount leaves frIn a) :
    a.oldRoot = batchTree startIndex.val 0 leaves frIn zeros depth 0 := by
  rw [h.old_root_def, batchAppend_old hs hz h depth le_rfl,
    Nat.div_eq_of_lt (batchAppend_start hs h).2]

/-- **The new root is the tree after the append** of the first `actual_count` leaves. -/
theorem batchAppend_new_root (hs : BatchShape depth maxL countBits) (hz : ZerosCoherent zeros)
    (h : BatchAppendSat depth maxL countBits zeros startIndex actualCount leaves frIn a) :
    a.newRoot = batchTree startIndex.val actualCount.val leaves frIn zeros depth 0 := by
  rw [h.new_root_def, batchAppend_window hs hz h depth le_rfl 0
    (by rw [batchWindow_top hs.depth_pos]; norm_num), Nat.div_eq_of_lt (batchAppend_start hs h).2]

/-- **Soundness of `BatchAppend`.** The run fits the tree, the old root is the tree holding
`start_index` leaves with this frontier, and the new root is that tree after appending the
first `actual_count` leaves. -/
theorem batchAppend_sound (hs : BatchShape depth maxL countBits) (hz : ZerosCoherent zeros)
    (h : BatchAppendSat depth maxL countBits zeros startIndex actualCount leaves frIn a) :
    startIndex.val + actualCount.val ≤ 4 ^ depth ∧
      a.oldRoot = batchTree startIndex.val 0 leaves frIn zeros depth 0 ∧
      a.newRoot = batchTree startIndex.val actualCount.val leaves frIn zeros depth 0 :=
  ⟨batchAppend_capacity hs h, batchAppend_old_root hs hz h, batchAppend_new_root hs hz h⟩

end Soundness

/-! ## A canonical satisfying assignment -/

/-- The old-root nodes the constraints compute. -/
noncomputable def batchOldNodes (bits : ℕ → F) (frIn : ℕ → ℕ → F) (zeros : ℕ → F) : ℕ → F
  | 0 => 0
  | d + 1 => merkleNode
      (oldChild (appendSel bits (bitPairs bits) d) (frIn d) (batchOldNodes bits frIn zeros d)
        (zeros d))

/-- The window nodes the constraints compute. -/
noncomputable def batchNodes (depth maxL : ℕ) (leaves active bits : ℕ → F)
    (frIn : ℕ → ℕ → F) (zeros : ℕ → F) : ℕ → ℕ → F
  | 0, t => active t * leaves t
  | d + 1, j => merkleNode (fun k =>
      batchChild (appendSel bits (bitPairs bits) d) (batchWindow depth maxL d) j k (frIn d)
        (batchNodes depth maxL leaves active bits frIn zeros d) (zeros d))

/-- The `LessThan` output for slot `k` against count `n`: the top bit of the shifted
difference, negated. -/
def lessThanActive (countBits n : ℕ) (k : ℕ) : F :=
  1 - natBits (k + 2 ^ (countBits + 1) - n) (countBits + 1)

/-- Every `BatchAppend` signal, defined as exactly the expression its constraint requires. -/
noncomputable def batchAppendWitness (depth maxL countBits S n : ℕ) (leaves : ℕ → F)
    (frIn : ℕ → ℕ → F) (zeros : ℕ → F) : BatchAppendSignals where
  cntBits := natBits (n - 1)
  ltBits k := natBits (k + 2 ^ (countBits + 1) - n)
  active := lessThanActive countBits n
  idxBits := natBits S
  lastIdxBits := natBits (S + n - 1)
  bb := bitPairs (natBits S)
  oldNode := batchOldNodes (natBits S) frIn zeros
  node := batchNodes depth maxL leaves (lessThanActive countBits n) (natBits S) frIn zeros
  oldRoot := batchOldNodes (natBits S) frIn zeros depth
  newRoot := batchNodes depth maxL leaves (lessThanActive countBits n) (natBits S) frIn zeros
    depth 0

/-- The digits `natBits S` denotes are the digits of `S`. -/
theorem natBits_quatDigit {depth S d : ℕ} (hS : S < 4 ^ depth) (hdp : 2 ^ (2 * depth) ≤ p)
    (hd : d < depth) :
    bitNat (natBits S (2 * d)) + 2 * bitNat (natBits S (2 * d + 1)) = quatDigit S d := by
  have hS' : S < 2 ^ (2 * depth) := by rwa [← four_pow_eq_two_pow]
  obtain ⟨hval, _⟩ := num2Bits_sound hdp (num2Bits_witness (n := 2 * depth) hS')
  rw [ZMod.val_natCast_of_lt (show S < p by omega)] at hval
  rw [← quatDigit_eq_bits (bs := natBits S) (n := 2 * depth) (d := d) (by omega), ← hval]

/-- **`BatchAppend(depth, maxL)` is satisfiable** at every start, every count and every
frontier that is zero where honest writers zero it. The frontier may hold anything in the
slots the digits read, so the pin is not over-strict. -/
theorem batchAppend_witness {depth maxL countBits S n : ℕ} (hs : BatchShape depth maxL countBits)
    (hn1 : 1 ≤ n) (hn : n ≤ maxL) (hcap : S + n ≤ 4 ^ depth) (leaves : ℕ → F)
    (frIn : ℕ → ℕ → F) (zeros : ℕ → F) (hfr : ∀ d k, quatDigit S d ≤ k → frIn d k = 0) :
    BatchAppendSat depth maxL countBits zeros ((S : ℕ) : F) ((n : ℕ) : F) leaves frIn
      (batchAppendWitness depth maxL countBits S n leaves frIn zeros) where
  count_bits := by
    have hcast : ((n - 1 : ℕ) : F) = ((n : ℕ) : F) - 1 := by rw [Nat.cast_sub hn1]; simp
    exact hcast ▸ num2Bits_witness (by have := hs.pow_count; omega)
  active_def k hk := by
    have h1 : 2 ^ (countBits + 1) = 2 ^ countBits * 2 := pow_succ 2 countBits
    have := hs.pow_count
    exact lessThan_witness (by omega) (by omega)
  index_bits := num2Bits_witness (by rw [← four_pow_eq_two_pow]; omega)
  last_idx_bits := by
    have hcast : ((S + n - 1 : ℕ) : F) = ((S : ℕ) : F) + ((n : ℕ) : F) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    exact hcast ▸ num2Bits_witness (by rw [← four_pow_eq_two_pow]; omega)
  bb_def _ _ := rfl
  frontier_pin d hd k hk := by
    have hpd := hs.depth_lt_p
    simp only [appendSel, batchAppendWitness, bitPairs]
    rw [batchRead_onehot (natBits_isBit _ _) (natBits_isBit _ _) k,
      natBits_quatDigit (by omega) (by omega) hd]
    split_ifs with hread
    · rw [sub_self, zero_mul]
    · rw [hfr d k (by omega), mul_zero]
  old_base := rfl
  old_def _ _ := rfl
  old_root_def := rfl
  leaf_def _ _ := rfl
  node_def _ _ _ _ := rfl
  new_root_def := rfl

end Lelantos
