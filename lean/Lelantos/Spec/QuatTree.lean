import Lelantos.Gadgets.Note

/-!
# The quaternary commitment tree

The specification the batch circuit is proved against, with no signals: the tree an append run
produces, and the single-leaf insert that run is made of. Nothing here mirrors a template;
`Gadgets/BatchAppend.lean` proves its constraint system computes these objects.

* `ZerosCoherent` — the `EMPTY_SUBTREE` table is the empty-subtree chain, the one hypothesis
  every tree result carries.
* `insertSlots`, `frontierUpd` and `InsertsTo` — one insert, as a hash chain through the fill
  table, and the frontier it leaves. `InsertsTo.unique` shows it is a function of its inputs.
* `batchTree S n L fr zeros d q` — the level-`d` node at position `q` after appending `n`
  leaves `L` at position `S` over the frontier `fr`. At `n = 0` it is the tree before the
  append, so one definition gives both roots of a batch.
* `batchTree_eq_appendRoot` — that tree is the root a run of `n` single-leaf inserts reaches,
  each an `InsertsTo` at position `S + k` (`append_insertsTo`).
* `batchTree_frontier_inj` — under Poseidon collision resistance the tree before the append
  determines every frontier slot it reads, so a root pins the frontier that rebuilds it.

The layer sits above `Gadgets.Note` (for `merkleNode`) and the digit arithmetic of
`Model.Bits`, and below the gadget that uses it.
-/

namespace Lelantos

/-- A node's leaves are four times its parent level's, counted one level down. -/
theorem mul_four_pow_succ (x d : ℕ) : x * 4 ^ (d + 1) = 4 ^ d * (4 * x) := by ring

/-! ## The empty-subtree chain

`EMPTY_SUBTREE(d)` (`src/lib/common.circom:29-58`) is a table of constants, pinned by
`test/gadgets/merkle.test.ts` to the chain `zeros[0] = 0`, `zeros[d+1] = Poseidon(TAG_MERKLE, zeros[d] ×
4)`. Lean treats Poseidon as opaque and cannot evaluate the constants, so the model keeps
`zeros` a free parameter and states the chain as a hypothesis wherever a result needs it.
`ZerosCoherent.eq_emptyChain` shows the hypothesis pins the table completely.
-/

/-- The fills are the empty-subtree chain. -/
def ZerosCoherent (zeros : ℕ → F) : Prop :=
  zeros 0 = 0 ∧ ∀ d, zeros (d + 1) = merkleNode (fun _ => zeros d)

/-- The chain itself, so that `ZerosCoherent` is satisfiable. -/
noncomputable def emptyChain : ℕ → F
  | 0 => 0
  | d + 1 => merkleNode (fun _ => emptyChain d)

theorem emptyChain_coherent : ZerosCoherent emptyChain := ⟨rfl, fun _ => rfl⟩

/-- There is exactly one coherent table. -/
theorem ZerosCoherent.eq_emptyChain {zeros : ℕ → F} (h : ZerosCoherent zeros) :
    ∀ d, zeros d = emptyChain d := by
  intro d
  induction d with
  | zero => exact h.1
  | succ d ih => rw [h.2 d, emptyChain, ih]

/-! ## One insert -/

/-- The four children of a level: `cur` at the insertion digit, frontier siblings to its
left, empty-subtree hash to its right — the OLD ROOT table in the header of
`src/lib/batch_append.circom:34-39`. -/
def insertSlots (t : ℕ) (cur : F) (fr : ℕ → F) (zero : F) : ℕ → F := fun k =>
  if k = t then cur else if k < t then fr k else zero

/-- The stored frontier after the insert: slot `t` takes `cur`, the others are unchanged. -/
def frontierUpd (t : ℕ) (cur : F) (fr : ℕ → F) : ℕ → F := fun k =>
  if k = t then cur else fr k

/-- The meaning of an insert, with no reference to selector or intermediate signals: a hash
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

Unlike `MerkleMember`, whose witnessed chain is tied to the root only by Poseidon collision
resistance (`merkleMember_inj`), here `chain 0 = leaf` and the step equation determine
every node, so the root is pinned by induction with no hash assumption. -/
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

/-! ## The tree after an append -/

/-- The level-`d` node at position `q` of the tree reached by appending `n` leaves `L` at
position `S`, over the frontier `fr`. Meaningful for `q ≥ 4 · (S / 4^(d+1))`: positions left
of `S / 4^d` in that range are the frontier's filled siblings, the rest are built. -/
noncomputable def batchTree (S n : ℕ) (L : ℕ → F) (fr : ℕ → ℕ → F) (zeros : ℕ → F) :
    ℕ → ℕ → F
  | d, q =>
    if q < S / 4 ^ d then fr d (q - 4 * (S / 4 ^ (d + 1))) else
      match d with
      | 0 => if q < S + n then L (q - S) else zeros 0
      | d' + 1 => merkleNode (fun c => batchTree S n L fr zeros d' (4 * q + c))

variable {S n : ℕ} {L : ℕ → F} {fr : ℕ → ℕ → F} {zeros : ℕ → F}

theorem batchTree_frontier {d q : ℕ} (hq : q < S / 4 ^ d) :
    batchTree S n L fr zeros d q = fr d (q - 4 * (S / 4 ^ (d + 1))) := by
  unfold batchTree
  rw [if_pos hq]

theorem batchTree_leaf {q : ℕ} (hq : S ≤ q) :
    batchTree S n L fr zeros 0 q = if q < S + n then L (q - S) else zeros 0 := by
  unfold batchTree
  rw [if_neg (Nat.not_lt.mpr (by simpa using hq))]

theorem batchTree_node {d q : ℕ} (hq : S / 4 ^ (d + 1) ≤ q) :
    batchTree S n L fr zeros (d + 1) q =
      merkleNode (fun c => batchTree S n L fr zeros d (4 * q + c)) := by
  rw [batchTree.eq_def]
  dsimp only
  rw [if_neg (Nat.not_lt.mpr hq)]

/-- **Past the run the tree is empty.** A node at or right of the frontier path whose
leaves all come after the last appended one is the empty-subtree hash. -/
theorem batchTree_empty (hz : ZerosCoherent zeros) :
    ∀ d q, S / 4 ^ d ≤ q → S + n ≤ q * 4 ^ d → batchTree S n L fr zeros d q = zeros d := by
  intro d
  induction d with
  | zero =>
    intro q h1 h2
    simp only [pow_zero, Nat.div_one, mul_one] at h1 h2
    rw [batchTree_leaf h1, if_neg (by omega), hz.1]
  | succ d ih =>
    intro q h1 h2
    rw [batchTree_node h1, hz.2 d]
    apply merkleNode_congr
    intro c _
    rw [mul_four_pow_succ] at h2
    have hle : 4 ^ d * (4 * q) ≤ 4 ^ d * (4 * q + c) := Nat.mul_le_mul_left _ (by omega)
    exact ih _ (Nat.div_le_of_le_mul (by omega)) (by rw [Nat.mul_comm]; omega)

/-- **Left of the run's end the tree is frozen.** A node whose leaves all precede position
`S + n` is the same in every longer run. -/
theorem batchTree_frozen {n' : ℕ} (hnn : n ≤ n') :
    ∀ d q, (q + 1) * 4 ^ d ≤ S + n →
      batchTree S n L fr zeros d q = batchTree S n' L fr zeros d q := by
  intro d
  induction d with
  | zero =>
    intro q hq
    simp only [pow_zero, mul_one] at hq
    by_cases hS : S ≤ q
    · rw [batchTree_leaf hS, batchTree_leaf hS, if_pos (by omega), if_pos (by omega)]
    · rw [batchTree_frontier (by simpa using hS), batchTree_frontier (by simpa using hS)]
  | succ d ih =>
    intro q hq
    by_cases hS : S / 4 ^ (d + 1) ≤ q
    · rw [batchTree_node hS, batchTree_node hS]
      apply merkleNode_congr
      intro c hc
      apply ih
      rw [mul_four_pow_succ] at hq
      have hle : (4 * q + c + 1) * 4 ^ d ≤ 4 ^ d * (4 * (q + 1)) := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
      omega
    · rw [batchTree_frontier (by omega), batchTree_frontier (by omega)]

/-- **The tree reads the frontier only where it is filled, and the leaves only in the run.**
Two frontiers agreeing below each level's digit, and two leaf vectors agreeing below `n`,
build the same tree. -/
theorem batchTree_congr {depth : ℕ} {L' : ℕ → F} {fr' : ℕ → ℕ → F}
    (hfr : ∀ d, d < depth → ∀ k, k < quatDigit S d → fr d k = fr' d k)
    (hL : ∀ k, k < n → L k = L' k) :
    ∀ d, d ≤ depth → ∀ q, S / 4 ^ d ≤ q →
      batchTree S n L fr zeros d q = batchTree S n L' fr' zeros d q := by
  intro d
  induction d with
  | zero =>
    intro _ q hq
    simp only [pow_zero, Nat.div_one] at hq
    rw [batchTree_leaf hq, batchTree_leaf hq]
    split_ifs with h
    · exact hL _ (by omega)
    · rfl
  | succ d ih =>
    intro hd q hq
    rw [batchTree_node hq, batchTree_node hq]
    apply merkleNode_congr
    intro c hc
    have hsplit := div_four_pow_split S d
    have hr := quatDigit_lt S d
    by_cases hpos : S / 4 ^ d ≤ 4 * q + c
    · exact ih (by omega) _ hpos
    · rw [batchTree_frontier (by omega), batchTree_frontier (by omega)]
      have hq' : q = S / 4 ^ (d + 1) := by omega
      subst hq'
      rw [show 4 * (S / 4 ^ (d + 1)) + c - 4 * (S / 4 ^ (d + 1)) = c by omega]
      exact hfr d (by omega) c (by omega)

/-- **The tree before the append pins the frontier it reads**, under Poseidon collision
resistance. Two frontiers rebuilding the same root at `start_index = S` agree on every filled
slot: the root's preimage is its children, the child at the digit is the next root down, and
the children below the digit are the frontier itself. -/
theorem batchTree_frontier_inj (hcr : ¬ PoseidonCollision) {depth : ℕ} {fr' : ℕ → ℕ → F}
    (hS : S < 4 ^ depth)
    (h : batchTree S 0 L fr zeros depth 0 = batchTree S 0 L fr' zeros depth 0) :
    ∀ d, d < depth → ∀ k, k < quatDigit S d → fr d k = fr' d k := by
  -- The node on the insertion path agrees at every level, from the root down.
  have hpath : ∀ e, e ≤ depth →
      batchTree S 0 L fr zeros (depth - e) (S / 4 ^ (depth - e)) =
        batchTree S 0 L fr' zeros (depth - e) (S / 4 ^ (depth - e)) := by
    intro e
    induction e with
    | zero =>
      intro _
      rwa [Nat.sub_zero, Nat.div_eq_of_lt hS]
    | succ e ih =>
      intro he
      have hd : depth - e = (depth - (e + 1)) + 1 := by omega
      have hup := ih (by omega)
      rw [hd, batchTree_node le_rfl, batchTree_node le_rfl] at hup
      have hc := merkleNode_inj hcr hup (quatDigit S (depth - (e + 1))) (quatDigit_lt _ _)
      rwa [← div_four_pow_split] at hc
  intro d hd k hk
  have hup := hpath (depth - (d + 1)) (by omega)
  rw [show depth - (depth - (d + 1)) = d + 1 by omega, batchTree_node le_rfl,
    batchTree_node le_rfl] at hup
  have hc := merkleNode_inj hcr hup k (by have := quatDigit_lt S d; omega)
  have hsplit := div_four_pow_split S d
  rwa [batchTree_frontier (by omega), batchTree_frontier (by omega),
    show 4 * (S / 4 ^ (d + 1)) + k - 4 * (S / 4 ^ (d + 1)) = k by omega] at hc

/-! ## The same tree, one leaf at a time -/

/-- The running nodes of one insert of `leaf` at position `N`: `insertSlots` at each level,
over the frontier `fr`. -/
noncomputable def insChain (leaf : F) (N : ℕ) (fr : ℕ → ℕ → F) (zeros : ℕ → F) : ℕ → F
  | 0 => leaf
  | d + 1 => merkleNode (insertSlots (quatDigit N d) (insChain leaf N fr zeros d) (fr d) (zeros d))

/-- The frontier after the first `k` of a run of inserts starting at `S`. -/
noncomputable def seqFr (S : ℕ) (L : ℕ → F) (frIn : ℕ → ℕ → F) (zeros : ℕ → F) :
    ℕ → ℕ → ℕ → F
  | 0 => frIn
  | k + 1 => fun d j =>
      frontierUpd (quatDigit (S + k) d) (insChain (L k) (S + k) (seqFr S L frIn zeros k) zeros d)
        (seqFr S L frIn zeros k d) j

/-- The root after inserting leaf `k` of the run, i.e. after `k + 1` appends. -/
noncomputable def appendRoot (depth S : ℕ) (L : ℕ → F) (frIn : ℕ → ℕ → F) (zeros : ℕ → F)
    (k : ℕ) : F :=
  insChain (L k) (S + k) (seqFr S L frIn zeros k) zeros depth

/-- **Each step of the run is an insert**, at tree position `S + k`. -/
theorem append_insertsTo (depth S : ℕ) (L : ℕ → F) (frIn : ℕ → ℕ → F) (zeros : ℕ → F)
    (k : ℕ) :
    InsertsTo depth (L k) (fun d => ((quatDigit (S + k) d : ℕ) : F)) (seqFr S L frIn zeros k)
      zeros (seqFr S L frIn zeros (k + 1)) (appendRoot depth S L frIn zeros k) := by
  have hval : ∀ d, (((quatDigit (S + k) d : ℕ) : F)).val = quatDigit (S + k) d := fun d =>
    ZMod.val_natCast_of_lt (lt_trans (quatDigit_lt _ _) four_lt_p)
  refine ⟨insChain (L k) (S + k) (seqFr S L frIn zeros k) zeros, rfl, fun d _ => ?_, rfl,
    fun d _ j _ => ?_⟩
  · rw [hval]; rfl
  · rw [hval]; rfl

section Sequential

variable {depth S n : ℕ} {L : ℕ → F} {frIn : ℕ → ℕ → F} {zeros : ℕ → F}

/-- The frontier invariant: after `k` inserts, every slot below a level's digit holds the
filled sibling the final tree has there. -/
def SeqFrInv (depth S n : ℕ) (L : ℕ → F) (frIn : ℕ → ℕ → F) (zeros : ℕ → F) (k : ℕ) : Prop :=
  ∀ d, d < depth → ∀ j, j < 3 → j < quatDigit (S + k) d →
    seqFr S L frIn zeros k d j = batchTree S n L frIn zeros d (4 * ((S + k) / 4 ^ (d + 1)) + j)

/-- Under the invariant, insert `k`'s running node at level `d` is the tree node its position
names, in the tree of the first `k + 1` leaves. -/
theorem insChain_eq_batchTree (hz : ZerosCoherent zeros) {k : ℕ} (hk : k + 1 ≤ n)
    (hinv : SeqFrInv depth S n L frIn zeros k) :
    ∀ d, d ≤ depth →
      insChain (L k) (S + k) (seqFr S L frIn zeros k) zeros d =
        batchTree S (k + 1) L frIn zeros d ((S + k) / 4 ^ d) := by
  intro d
  induction d with
  | zero =>
    intro _
    simp only [insChain, pow_zero, Nat.div_one]
    rw [batchTree_leaf (Nat.le_add_right S k), if_pos (by omega), Nat.add_sub_cancel_left]
  | succ d ih =>
    intro hd
    set N := S + k with hN
    have hsplit := div_four_pow_split N d
    have ht := quatDigit_lt N d
    set t := quatDigit N d with ht_def
    set q := N / 4 ^ (d + 1) with hq
    have hSq : S / 4 ^ (d + 1) ≤ q := Nat.div_le_div_right (by omega)
    simp only [insChain]
    rw [← ht_def, batchTree_node hSq]
    apply merkleNode_congr
    intro c hc
    have hm := four_pow_pos d
    unfold insertSlots
    split_ifs with hct hlt
    · -- The insertion slot carries the chain.
      subst hct
      rw [ih (by omega)]
      congr 1
    · -- A filled sibling: read from the frontier, frozen since the final tree agrees there.
      rw [hinv d (by omega) c (by omega) hlt]
      symm
      apply batchTree_frozen hk
      have := (Nat.le_div_iff_mul_le hm).1 (show 4 * q + c + 1 ≤ N / 4 ^ d by omega)
      omega
    · -- Right of the insertion point: empty, since no leaf of the first `k + 1` lies there.
      symm
      apply batchTree_empty hz
      · have : S / 4 ^ d ≤ N / 4 ^ d := Nat.div_le_div_right (by omega)
        omega
      · have := (Nat.div_lt_iff_lt_mul hm).1 (show N / 4 ^ d < 4 * q + c by omega)
        omega

/-- **The frontier invariant holds all along the run.** -/
theorem seqFr_inv (hz : ZerosCoherent zeros) :
    ∀ k, k ≤ n → SeqFrInv depth S n L frIn zeros k := by
  intro k
  induction k with
  | zero =>
    intro _ d _ j _ hj
    simp only [seqFr, Nat.add_zero] at hj ⊢
    have hsplit := div_four_pow_split S d
    rw [batchTree_frontier (by omega)]
    congr 1
    omega
  | succ k ih =>
    intro hk d hd j hj3 hj
    have hinv := ih (by omega)
    have hN' : S + (k + 1) = S + k + 1 := by omega
    rw [hN'] at hj ⊢
    simp only [seqFr]
    unfold frontierUpd
    have hsucc : (S + k + 1) / 4 ^ d = (S + k) / 4 ^ d + if 4 ^ d ∣ S + k + 1 then 1 else 0 :=
      Nat.succ_div
    have hdmc : 4 ^ d ∣ S + k + 1 → (S + k + 1) / 4 ^ d * 4 ^ d = S + k + 1 :=
      Nat.div_mul_cancel
    have hq0 : ∀ j, j < 3 → j < quatDigit (S + k) d →
        seqFr S L frIn zeros k d j =
          batchTree S n L frIn zeros d (4 * ((S + k) / 4 ^ d / 4) + j) := by
      intro j hj3 hj
      rw [hinv d hd j hj3 hj, div_four_pow_succ]
    have hchain := insChain_eq_batchTree hz hk hinv d (by omega)
    have hdig : quatDigit (S + k) d = (S + k) / 4 ^ d % 4 := rfl
    have hdig' : quatDigit (S + k + 1) d = (S + k + 1) / 4 ^ d % 4 := rfl
    rw [div_four_pow_succ (S + k + 1) d, hsucc, hdig]
    rw [hdig', hsucc] at hj
    rw [hdig] at hq0
    by_cases hdvd : 4 ^ d ∣ S + k + 1
    · -- A carry reaches this level: the node at `(S + k) / 4^d` has just filled.
      have hfull := hdmc hdvd
      rw [hsucc, if_pos hdvd] at hfull
      rw [if_pos hdvd] at hj ⊢
      generalize (S + k) / 4 ^ d = X at hq0 hchain hj hfull ⊢
      split_ifs with hjt
      · rw [hchain]
        have hpos : 4 * ((X + 1) / 4) + j = X := by omega
        rw [hpos]
        exact batchTree_frozen (show k + 1 ≤ n by omega) d X (by omega)
      · rw [hq0 j hj3 (by omega)]
        congr 1
        omega
    · rw [if_neg hdvd, Nat.add_zero] at hj ⊢
      generalize (S + k) / 4 ^ d = X at hq0 hj ⊢
      rw [if_neg (show j ≠ X % 4 by omega), hq0 j hj3 hj]

/-- **The batched tree is the tree the run of inserts reaches.** -/
theorem batchTree_eq_appendRoot (hz : ZerosCoherent zeros) (hn1 : 1 ≤ n)
    (hcap : S + n ≤ 4 ^ depth) :
    appendRoot depth S L frIn zeros (n - 1) = batchTree S n L frIn zeros depth 0 := by
  have hinv := seqFr_inv (depth := depth) (S := S) (n := n) (L := L) (frIn := frIn) hz (n - 1)
    (by omega)
  have h := insChain_eq_batchTree hz (show n - 1 + 1 ≤ n by omega) hinv depth le_rfl
  have hn' : n - 1 + 1 = n := by omega
  have h0 : (S + (n - 1)) / 4 ^ depth = 0 := Nat.div_eq_of_lt (by omega)
  rw [hn', h0] at h
  exact h

end Sequential

end Lelantos
