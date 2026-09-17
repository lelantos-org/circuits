import Lelantos.Model.Jubjub
import Lelantos.Gadgets.BatchAppend

/-!
# The `TreeUpdateBatch` signal set

The signals of `TreeUpdateBatch(DEPTH, MAX_L)`: the public statement (both roots, the
position, the leaves' fields), the private frontier and blinders, and the intermediates of
the tree and of the deposit binding. What the circuit constrains over them is
`Lelantos.Circuit.TreeUpdateBatch`; how they are ordered into `(z, y)` is
`Lelantos.Circuit.BatchLayout`.

The append gadget's own signals are `BatchAppendSignals` (`Gadgets/BatchAppend.lean`),
reached through the `append` field.
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
  -- Leaf hashes (`:124-136`).
  leaves : ℕ → F
  -- The tree (`:141-151`).
  append : BatchAppendSignals
  -- Deposit binding (`:187-258`).
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


end Lelantos
