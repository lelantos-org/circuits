import Lelantos.Gadgets.Common
import Lelantos.Note

/-!
# `src/lib/merkle.circom` — quaternary Merkle proofs

`MerkleLevel4` (`src/lib/merkle.circom:19`) reconstructs a node's four children from the
current node, three siblings, and the one-hot selector produced by `PathIndexSelectors`:

    c0 <== s0*cur + (1-s0)*sib0;
    c1 <== s1*cur + s0*sib0 + (s2+s3)*sib1;
    c2 <== s2*cur + (s0+s1)*sib1 + s3*sib2;
    c3 <== s3*cur + (1-s3)*sib2;

`merkleLevel4_sound` shows this arithmetic really is the insertion of `cur` at position
`path_index` into the sibling list — `slots` below — for every one of the four cases. If
the selector were not one-hot the same arithmetic could duplicate `cur` into two slots or
drop a sibling, which is why `pathIndexSelectors_sound` is a prerequisite rather than a
convenience.

`merkleProofOrDummy_sound` is the payoff: a slot with `is_dummy = 0` genuinely proves
membership of its leaf under `root`. A slot with `is_dummy = 1` proves *nothing at all* —
the path is entirely unconstrained — which is sound only because `DummyZeroValue` forces
such a slot to carry value `0`. That asymmetry is stated explicitly rather than hidden,
because it is a real obligation on the rest of the system.
-/

namespace Lelantos

/-- Insert `cur` at position `t` into the three siblings, preserving sibling order.
This is what the slot arithmetic in `MerkleLevel4` computes. -/
def slots (t : ℕ) (cur : F) (sib : ℕ → F) : ℕ → F := fun k =>
  if k = t then cur else if k < t then sib k else sib (k - 1)

/-- The constraint system of `MerkleLevel4` — `src/lib/merkle.circom:19-73`. -/
structure MerkleLevel4Sat (cur : F) (sib : ℕ → F) (idx : F) (b s c : ℕ → F) (out : F) : Prop where
  /-- `:25-34` — the one-hot selector for this level's path index. -/
  selectors : PathIndexSelectorsSat idx b s
  /-- `:42-47` — `c0 = s0·cur + (1-s0)·sib[0]`. -/
  c0_def : c 0 = s 0 * cur + (1 - s 0) * sib 0
  /-- `:49-56` — `c1 = s1·cur + s0·sib[0] + (s2+s3)·sib[1]`. -/
  c1_def : c 1 = s 1 * cur + s 0 * sib 0 + (s 2 + s 3) * sib 1
  /-- `:58-65` — `c2 = s2·cur + (s0+s1)·sib[1] + s3·sib[2]`. -/
  c2_def : c 2 = s 2 * cur + (s 0 + s 1) * sib 1 + s 3 * sib 2
  /-- `:67-72` — `c3 = s3·cur + (1-s3)·sib[2]`. -/
  c3_def : c 3 = s 3 * cur + (1 - s 3) * sib 2
  /-- `:74-80` — `out = Poseidon(TAG_MERKLE, c0, c1, c2, c3)`. -/
  out_def : out = merkleNode c

/-- **Soundness of `MerkleLevel4`.** The slot arithmetic is insertion of `cur` at
`path_index`, and the index is a valid quaternary digit. -/
theorem merkleLevel4_sound {cur idx out : F} {sib b s c : ℕ → F}
    (h : MerkleLevel4Sat cur sib idx b s c out) :
    idx.val < 4 ∧ out = merkleNode (slots idx.val cur sib) := by
  obtain ⟨hsel, hc0, hc1, hc2, hc3, hout⟩ := h
  obtain ⟨hlt, hone⟩ := pathIndexSelectors_sound hsel
  refine ⟨hlt, ?_⟩
  have h0 := hone 0 (by norm_num)
  have h1 := hone 1 (by norm_num)
  have h2 := hone 2 (by norm_num)
  have h3 := hone 3 (by norm_num)
  clear hone hsel
  -- One case per value of `path_index`. In each, the selector is one-hot, so the four slot
  -- equations collapse to the corresponding row of the fill table above.
  have key : ∀ k, k < 4 → c k = slots idx.val cur sib k := by
    intro k hk
    interval_cases hidx : idx.val <;> norm_num at h0 h1 h2 h3 <;>
      rw [h0] at hc0 hc1 hc2 <;> rw [h1] at hc1 hc2 <;> rw [h2] at hc1 hc2 <;>
      rw [h3] at hc1 hc2 hc3 <;>
      interval_cases k <;> simp only [slots, hc0, hc1, hc2, hc3] <;> norm_num
  -- `merkleNode` reads only indices 0..3, so matching those four slots is enough.
  rw [hout, merkleNode, merkleNode, key 0 (by norm_num), key 1 (by norm_num),
    key 2 (by norm_num), key 3 (by norm_num)]

/-- The constraint system of `MerkleRoot(depth)` — `src/lib/merkle.circom:76-97`.
`cur` is the chain of intermediate nodes, `pe` / `pi` the path elements and indices. -/
structure MerkleRootSat (depth : ℕ) (leaf : F) (pe : ℕ → ℕ → F) (pi : ℕ → F)
    (b s c : ℕ → ℕ → F) (cur : ℕ → F) (root : F) : Prop where
  /-- `:92` — the chain starts at the leaf. -/
  base : cur 0 = leaf
  /-- `:94-102` — one `MerkleLevel4` per level. -/
  level : ∀ d, d < depth →
    MerkleLevel4Sat (cur d) (pe d) (pi d) (b d) (s d) (c d) (cur (d + 1))
  /-- `:104` — the root is the top of the chain. -/
  top : root = cur depth

/-- What it *means* for a leaf to sit under a root along a given path: the abstract
hash chain, with no reference to selector signals. -/
def MerkleMember (depth : ℕ) (leaf : F) (pe : ℕ → ℕ → F) (pi : ℕ → F) (root : F) : Prop :=
  ∃ chain : ℕ → F,
    chain 0 = leaf ∧
    (∀ d, d < depth → chain (d + 1) = merkleNode (slots (pi d).val (chain d) (pe d))) ∧
    root = chain depth

/-- **Soundness of `MerkleRoot`.** A satisfying assignment exhibits a genuine hash chain,
and every path index is a valid quaternary digit. -/
theorem merkleRoot_sound {depth : ℕ} {leaf root : F} {pe : ℕ → ℕ → F} {pi : ℕ → F}
    {b s c : ℕ → ℕ → F} {curChain : ℕ → F}
    (h : MerkleRootSat depth leaf pe pi b s c curChain root) :
    MerkleMember depth leaf pe pi root ∧ ∀ d, d < depth → (pi d).val < 4 :=
  ⟨⟨curChain, h.base, fun d hd => (merkleLevel4_sound (h.level d hd)).2, h.top⟩,
    fun d hd => (merkleLevel4_sound (h.level d hd)).1⟩

/-- The constraint system of `MerkleProofOrDummy(depth)` — `src/lib/merkle.circom:100-121`:

    is_dummy * (is_dummy - 1) === 0;
    diff <== MerkleRoot(...).root - root;
    (1 - is_dummy) * diff === 0;
-/
structure MerkleProofOrDummySat (depth : ℕ) (leaf : F) (pe : ℕ → ℕ → F) (pi : ℕ → F)
    (root isDummy diff computed : F) (b s c : ℕ → ℕ → F) (curChain : ℕ → F) : Prop where
  /-- `:115` — the dummy flag is boolean. -/
  dummy_bit : IsBit isDummy
  /-- `:117-124` — the recomputed root. -/
  recomputed : MerkleRootSat depth leaf pe pi b s c curChain computed
  /-- `:127` — `diff <== mr.root - root`. -/
  diff_def : diff = computed - root
  /-- `:128` — the difference is forced to zero for real slots only. -/
  matches_root : (1 - isDummy) * diff = 0

/-- **Soundness of `MerkleProofOrDummy`.** A non-dummy slot proves membership.

The dummy branch is deliberately absent from the conclusion: when `is_dummy = 1` nothing
about the path is constrained, so no membership statement is available or intended. -/
theorem merkleProofOrDummy_sound {depth : ℕ} {leaf root isDummy diff computed : F}
    {pe : ℕ → ℕ → F} {pi : ℕ → F} {b s c : ℕ → ℕ → F} {curChain : ℕ → F}
    (h : MerkleProofOrDummySat depth leaf pe pi root isDummy diff computed b s c curChain)
    (hreal : isDummy = 0) : MerkleMember depth leaf pe pi root := by
  have hzero := h.matches_root
  rw [hreal] at hzero
  simp only [sub_zero, one_mul] at hzero
  rw [h.diff_def, sub_eq_zero] at hzero
  obtain ⟨mem, _⟩ := merkleRoot_sound h.recomputed
  rwa [hzero] at mem

/-! ## Binding

`MerkleMember` on its own is close to tautological: it says a hash chain *exists*, and the
witness supplies one. What makes membership a real commitment is that the root determines
the chain — which needs Poseidon collision resistance. That is `merkleMember_inj`, and it
is the reason `spentNote_sound`'s `member` field is worth anything.
-/

/-- Inserting at a fixed position is injective: matching all four slots forces the same
current node and the same siblings. Requires the position to be a valid quaternary digit,
which `pathIndexSelectors_sound` supplies. -/
theorem slots_inj {t : ℕ} (ht : t < 4) {cur cur' : F} {sib sib' : ℕ → F}
    (h : ∀ k, k < 4 → slots t cur sib k = slots t cur' sib' k) :
    cur = cur' ∧ ∀ k, k < 3 → sib k = sib' k := by
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  refine ⟨by simpa [slots] using h t ht, ?_⟩
  intro k hk
  interval_cases t <;> simp only [slots] at h0 h1 h2 h3 <;> norm_num at h0 h1 h2 h3 <;>
    interval_cases k <;> assumption

/-- **Merkle membership is binding.** Two membership proofs at the same position under the
same root have the same leaf and the same siblings — unless the prover found a Poseidon
collision.

This is what upgrades `MerkleMember` from "a chain exists" to "the root commits to this
leaf at this position". -/
theorem merkleMember_inj (hnc : ¬ PoseidonCollision)
    {depth : ℕ} {leaf leaf' root : F} {pe pe' : ℕ → ℕ → F} {pi : ℕ → F}
    (hidx : ∀ d, d < depth → (pi d).val < 4)
    (h : MerkleMember depth leaf pe pi root)
    (h' : MerkleMember depth leaf' pe' pi root) :
    leaf = leaf' ∧ ∀ d, d < depth → ∀ k, k < 3 → pe d k = pe' d k := by
  obtain ⟨c, hc0, hcs, hcr⟩ := h
  obtain ⟨c', hc0', hcs', hcr'⟩ := h'
  -- Peel the chain from the root downwards.
  have step : ∀ d, d < depth → c (d + 1) = c' (d + 1) →
      c d = c' d ∧ ∀ k, k < 3 → pe d k = pe' d k := by
    intro d hd hnext
    rw [hcs d hd, hcs' d hd] at hnext
    exact slots_inj (hidx d hd) (merkleNode_inj hnc hnext)
  have down : ∀ m, m ≤ depth → c (depth - m) = c' (depth - m) := by
    intro m
    induction m with
    | zero => intro _; rw [Nat.sub_zero, ← hcr, ← hcr']
    | succ n ih =>
      intro hn
      have hd : depth - (n + 1) < depth := by omega
      have hsucc : depth - (n + 1) + 1 = depth - n := by omega
      have hnext : c (depth - (n + 1) + 1) = c' (depth - (n + 1) + 1) := by
        rw [hsucc]; exact ih (by omega)
      exact (step _ hd hnext).1
  have all : ∀ d, d ≤ depth → c d = c' d := by
    intro d hd
    have := down (depth - d) (by omega)
    rwa [show depth - (depth - d) = d by omega] at this
  refine ⟨by rw [← hc0, ← hc0', all 0 (by omega)], ?_⟩
  intro d hd k hk
  exact (step d hd (all (d + 1) (by omega))).2 k hk

/-- Every path index of a `MerkleProofOrDummy` is a valid quaternary digit. Needed to
apply `merkleMember_inj`. -/
theorem merkleProofOrDummy_idx {depth : ℕ} {leaf root isDummy diff computed : F}
    {pe : ℕ → ℕ → F} {pi : ℕ → F} {b s c : ℕ → ℕ → F} {curChain : ℕ → F}
    (h : MerkleProofOrDummySat depth leaf pe pi root isDummy diff computed b s c curChain) :
    ∀ d, d < depth → (pi d).val < 4 :=
  (merkleRoot_sound h.recomputed).2

/-- A dummy slot is boolean-flagged; this is the only thing its constraints give us. -/
theorem merkleProofOrDummy_bit {depth : ℕ} {leaf root isDummy diff computed : F}
    {pe : ℕ → ℕ → F} {pi : ℕ → F} {b s c : ℕ → ℕ → F} {curChain : ℕ → F}
    (h : MerkleProofOrDummySat depth leaf pe pi root isDummy diff computed b s c curChain) :
    isDummy = 0 ∨ isDummy = 1 :=
  isBit_iff.mp h.dummy_bit

end Lelantos
