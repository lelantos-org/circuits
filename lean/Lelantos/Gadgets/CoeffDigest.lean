import Lelantos.Model.Poseidon
import Lelantos.Gadgets.Note
import Mathlib.Tactic.Ring

/-!
# `CoeffDigest` — the commitment to the coefficients

`CoeffDigest(M)` (`src/lib/poly_eval.circom:43-69`) is a `Poseidon(5)` fold over `M` field
elements, four words per block:

    h_0     = Poseidon(TAG_DIGEST, in[0..3])
    h_{b+1} = Poseidon(h_b,        in[4b+4 .. 4b+7])

with the last block zero-padded, and `out` the last block's output. Both compressors feed it
their whole coefficient vector and expose the result as a public output:
`TransactCompressN` over `M = 3 + N_IN + N_OUT` words (13 at 4x6, four blocks),
`BatchCompress` over `M = 4 + 4·MAX_L` words (36 at `MAX_L = 8`, nine blocks). The digest is
not a coefficient and is not evaluated into `y`.

* `coeffDigest_sound` — the block chain computes `coeffDigest`, a function of the `M`
  inputs.
* `digest_inj` † — under Poseidon collision resistance, equal digests of two length-`M`
  vectors force the vectors equal. `M` is a template parameter, so both sides have the same
  length and the zero padding is not ambiguous.

## What the digest is for, and what is proved about it

The contract reads the digest word `d` from calldata, derives
`z = keccak(coefficients, d, challenge-only words) mod r`, computes `y` over the calldata
coefficients, and verifies the proof against the public signals `(y, d, z)`. The proof
shows a witness `w` with `CoeffDigest(w) = d` and `Σ w_k z^k = y`.

`d` is in the preimage of `z`, so under collision resistance the witness vector is fixed
before `z`, as is the calldata vector `c`. If `w ≠ c`, they agree at a random `z` with
probability at most `(M − 1)/r`. This assumes Poseidon(5) is collision resistant and
keccak256 behaves as a random oracle.

Proved in Lean:

* the digest binds the vector: `digest_inj` †, and its circuit-level forms
  `Lelantos.transact_calldata_binding` † and `Lelantos.batch_calldata_binding` †;
* distinct vectors agree on at most `M − 1` challenges: `Lelantos.polyEval_binding`,
  unconditional.

Not formalised: combining the two into "no forged calldata verifies except with negligible
probability", the Fiat-Shamir random-oracle argument. It is prose, in `lean/README.md`.
-/

namespace Lelantos

/-- Word `k` of the zero-padded input: `in[k]` below `m`, `0` from `m` on
(`src/lib/poly_eval.circom:61-65`). -/
def padded (c : ℕ → F) (m k : ℕ) : F := if k < m then c k else 0

theorem padded_of_lt {c : ℕ → F} {m k : ℕ} (hk : k < m) : padded c m k = c k := if_pos hk

/-- The padded input reads only the first `m` words. -/
theorem padded_congr {c c' : ℕ → F} {m : ℕ} (h : ∀ k, k < m → c k = c' k) (k : ℕ) :
    padded c m k = padded c' m k := by
  unfold padded
  split
  · exact h k ‹_›
  · rfl

/-- The output of block `b` of the fold. Block 0 leads with `TAG_DIGEST`; every later block
leads with the previous block's output. -/
noncomputable def digestBlock (c : ℕ → F) (m : ℕ) : ℕ → F
  | 0 => poseidon [TAG_DIGEST, padded c m 0, padded c m 1, padded c m 2, padded c m 3]
  | b + 1 => poseidon [digestBlock c m b, padded c m (4 * b + 4), padded c m (4 * b + 5),
      padded c m (4 * b + 6), padded c m (4 * b + 7)]

/-- `BLOCKS = (M + 3) \ 4` — `src/lib/poly_eval.circom:45`. -/
def digestBlocks (m : ℕ) : ℕ := (m + 3) / 4

/-- `CoeffDigest(m)`: the output of the last block. -/
noncomputable def coeffDigest (c : ℕ → F) (m : ℕ) : F := digestBlock c m (digestBlocks m - 1)

example : digestBlocks 13 = 4 := by decide
example : digestBlocks 36 = 9 := by decide

theorem digestBlock_congr {c c' : ℕ → F} {m : ℕ} (h : ∀ k, k < m → c k = c' k) (b : ℕ) :
    digestBlock c m b = digestBlock c' m b := by
  induction b with
  | zero => simp only [digestBlock, padded_congr h]
  | succ b ih => simp only [digestBlock, padded_congr h, ih]

/-- The digest is a function of the first `m` words. -/
theorem coeffDigest_congr {c c' : ℕ → F} {m : ℕ} (h : ∀ k, k < m → c k = c' k) :
    coeffDigest c m = coeffDigest c' m :=
  digestBlock_congr h _

/-- The constraint system of `CoeffDigest(m)` — `src/lib/poly_eval.circom:43-69`. `h` is
the array of block outputs `h[b].out`. The template asserts `M >= 1`, so block 0 always
exists. -/
structure CoeffDigestSat (m : ℕ) (inp h : ℕ → F) (out : F) : Prop where
  /-- `:51-67` at `b == 0` — block 0 hashes `TAG_DIGEST` and the first four words. -/
  block_zero : h 0 = poseidon [TAG_DIGEST, padded inp m 0, padded inp m 1, padded inp m 2,
    padded inp m 3]
  /-- `:51-67` at `b > 0` — `h[b].inputs[0] <== h[b - 1].out`, then the next four words,
  zero past `M`. -/
  block_succ : ∀ b, b + 1 < digestBlocks m →
    h (b + 1) = poseidon [h b, padded inp m (4 * b + 4), padded inp m (4 * b + 5),
      padded inp m (4 * b + 6), padded inp m (4 * b + 7)]
  /-- `:68` — `out <== h[BLOCKS - 1].out`. -/
  out_def : out = h (digestBlocks m - 1)

/-- **Soundness of `CoeffDigest`.** The block chain computes `coeffDigest`. -/
theorem coeffDigest_sound {m : ℕ} {inp h : ℕ → F} {out : F} (hs : CoeffDigestSat m inp h out) :
    out = coeffDigest inp m := by
  have key : ∀ b, b ≤ digestBlocks m - 1 → h b = digestBlock inp m b := by
    intro b
    induction b with
    | zero => intro _; exact hs.block_zero
    | succ b ih =>
      intro hb
      rw [hs.block_succ b (by omega), ih (by omega), digestBlock]
  rw [hs.out_def, key _ le_rfl, coeffDigest]

/-- **The honest assignment.** The block outputs are `digestBlock`, for any vector that
agrees with `c` on the words the digest reads. -/
theorem coeffDigestSat_witness {m : ℕ} {c c' : ℕ → F} (h : ∀ k, k < m → c k = c' k) :
    CoeffDigestSat m c' (digestBlock c m) (coeffDigest c m) where
  block_zero := by simp only [digestBlock, padded_congr h]
  block_succ b _ := by simp only [digestBlock, padded_congr h]
  out_def := rfl

/-- Equal block outputs force equal padded inputs over every block up to that one. -/
theorem digestBlock_inj (hcr : ¬ PoseidonCollision) {c c' : ℕ → F} {m : ℕ} :
    ∀ b, digestBlock c m b = digestBlock c' m b →
      ∀ k, k < 4 * (b + 1) → padded c m k = padded c' m k := by
  intro b
  induction b with
  | zero =>
    intro h k hk
    have h' := poseidon_inj hcr h
    simp only [List.cons.injEq, and_true] at h'
    obtain ⟨_, h0, h1, h2, h3⟩ := h'
    obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    exacts [h0, h1, h2, h3]
  | succ b ih =>
    intro h k hk
    have h' := poseidon_inj hcr h
    simp only [List.cons.injEq, and_true] at h'
    obtain ⟨hprev, h0, h1, h2, h3⟩ := h'
    by_cases hlow : k < 4 * (b + 1)
    · exact ih hprev k hlow
    · obtain rfl | rfl | rfl | rfl :
          k = 4 * b + 4 ∨ k = 4 * b + 5 ∨ k = 4 * b + 6 ∨ k = 4 * b + 7 := by omega
      exacts [h0, h1, h2, h3]

/-- **The digest is injective on length-`m` vectors**, under Poseidon collision resistance:
equal `CoeffDigest(m)` outputs force the input vectors to agree on all `m` words.

`hcr` is unsatisfiable (`poseidon_collision`); it is an assumption recorded in the
statement. -/
theorem digest_inj (hcr : ¬ PoseidonCollision) {c c' : ℕ → F} {m : ℕ}
    (h : coeffDigest c m = coeffDigest c' m) : ∀ k, k < m → c k = c' k := by
  intro k hk
  have hpad := digestBlock_inj hcr (digestBlocks m - 1) h k (by unfold digestBlocks; omega)
  rwa [padded_of_lt hk, padded_of_lt hk] at hpad

/-- **Block 0 of a digest is never a Merkle node.** Both are `Poseidon(5)`; the leading
`TAG_DIGEST` and `TAG_MERKLE` separate them (`src/lib/poly_eval.circom:40-41`). A later
block leads with a hash output instead of a tag, and nothing is claimed about it. -/
theorem digestBlock_zero_ne_merkleNode (hcr : ¬ PoseidonCollision) (c : ℕ → F) (m : ℕ)
    (n : ℕ → F) : digestBlock c m 0 ≠ merkleNode n := by
  intro h
  have h' := poseidon_inj hcr h
  simp only [List.cons.injEq, and_true] at h'
  have hne : (TAG_DIGEST : F) ≠ TAG_MERKLE := by
    simpa [TAG_DIGEST, TAG_MERKLE] using tag_ne (m := 15) (n := 5) (by norm_num) (by norm_num)
      (by norm_num)
  exact hne h'.1

end Lelantos
