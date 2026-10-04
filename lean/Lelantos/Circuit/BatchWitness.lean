import Lelantos.Gadgets.BatchAppend
import Lelantos.Gadgets.PolyEval

/-!
# The `TreeUpdateBatch` signal set

The signals of `TreeUpdateBatch(DEPTH, MAX_L)`: the three public signals `(y, digest, z)`,
the public statement (both roots, the position, the leaves' fields), the private frontier,
and the intermediates of the leaf construction, the tree, the asset guard and the
compression. What the circuit constrains over them is `Lelantos.Circuit.TreeUpdateBatch`;
the order in which they are evaluated into `y` and folded into `digest` is
`Lelantos.Circuit.BatchLayout`.

The append gadget's own signals are `BatchAppendSignals` (`Gadgets/BatchAppend.lean`),
reached through the `append` field.

`cms[k]` is read by `is_deposit[k]`: on a spend slot it is the note commitment a transact
proof bound as `out_cm`, and it is the leaf; on a deposit slot it is the depositor's
`inner`, and the leaf is built from it and the public amount.
-/

namespace Lelantos

/-- Every signal of one `TreeUpdateBatch(depth, maxL)` instance. Array signals are total
functions, read only below their declared length, per the convention in `Model.Bits`. -/
structure BatchSignals (depth maxL : ℕ) where
  -- The public signals, `(y, digest, z)` in the verifier's order
  -- (`src/tree_update_batch.circom:104-106`). `digest` is the `CoeffDigest` of the
  -- coefficient vector; it is not a coefficient and is not evaluated into `y`.
  z : F
  y : F
  digest : F
  -- Logical public inputs (`:109-116`).
  oldRoot : F
  newRoot : F
  startIndex : F
  actualCount : F
  cms : ℕ → F
  leafAsset : ℕ → F
  leafPublicIn : ℕ → F
  isDeposit : ℕ → F
  -- Private input (`:119`).
  frontierIn : ℕ → ℕ → F
  -- The leaf (`:137-156`): two range checks, the deposit commitment, the mux.
  assetBits : ℕ → ℕ → F
  pubInBits : ℕ → ℕ → F
  depCm : ℕ → F
  depDelta : ℕ → F
  leaves : ℕ → F
  -- The tree (`:161-171`).
  append : BatchAppendSignals
  -- The asset guard (`:191-196`).
  assetInv : ℕ → F
  assetIsZero : ℕ → F
  -- `CoeffDigest` inside `BatchCompress`: the block outputs.
  dgBlock : ℕ → F
  -- `PolyEval` inside `BatchCompress`: the accumulator and the `IsZero` signals of the
  -- `z != 0` check.
  peAcc : ℕ → F
  zInv : F
  zIsZero : F

end Lelantos
