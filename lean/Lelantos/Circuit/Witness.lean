import Lelantos.Circuit.Spent
import Lelantos.Circuit.Output

/-!
# The `Transact` signal set

The signals of `Transact(DEPTH, N_IN, N_OUT)`: the two slot arrays, the transparent bucket,
the three public signals `(y, digest, z)` and the dummy-count accumulator. The constraints
are in `Lelantos.Circuit.Transact`, the public-input order in `Lelantos.Circuit.Layout`.

Each field names a signal of the compiled circuit; `lean/expected/signal-map.json` records
which, and `test/formal/signal_parity.test.ts` checks the name against `build/*.sym`.
-/

namespace Lelantos

/-- Every signal of `Transact(depth, nIn, nOut)`. -/
structure TxWitness (depth nIn nOut : ℕ) where
  /-- The public signals, `(y, digest, z)` in the verifier's order
  (`src/lib/transact.circom:37-39`). `z` is the challenge, an input; `y` and `digest` are
  outputs. -/
  z : F
  y : F
  /-- The coefficient digest: `CoeffDigest` of the coefficient vector, a public output. It is
  not a coefficient and is not evaluated into `y`. -/
  digest : F
  /-- Logical public inputs: private signals of the circuit, bound through `y` and
  `digest`. -/
  merkleRoot : F
  publicAssetId : F
  publicOut : F
  /-- Per-slot sub-circuits. -/
  spent : ℕ → SpentSlot depth
  out : ℕ → OutputSlot
  /-- Transparent-bucket signals: the two range checks and `IsZero(public_out)`. -/
  pubAssetBits : ℕ → F
  pubOutBits : ℕ → F
  pubOutInv : F
  pubOutIsZero : F
  /-- `PerAssetValueBalance` intermediates. -/
  vbPubInv : ℕ → F
  vbPubEq : ℕ → F
  vbInInv : ℕ → ℕ → F
  vbInEq : ℕ → ℕ → F
  vbOutInv : ℕ → ℕ → F
  vbOutEq : ℕ → ℕ → F
  vbInTerm : ℕ → ℕ → F
  vbOutTerm : ℕ → ℕ → F
  vbLhs : ℕ → ℕ → F
  vbRhs : ℕ → ℕ → F
  /-- `CoeffDigest` block outputs. -/
  dgBlock : ℕ → F
  /-- `PolyEval`: the accumulator and the `IsZero` signals of the `z != 0` check. -/
  peAcc : ℕ → F
  zInv : F
  zIsZero : F
  /-- Running count of dummy input slots, and the `IsEqual` comparing it to `nIn`.
  `src/lib/transact.circom` rejects the all-dummy witness with it; see
  `TransactSat.not_all_dummy`. -/
  dummyAcc : ℕ → F
  dummyAllInv : F
  dummyAllOut : F

variable {depth nIn nOut : ℕ}

/-- Input asset ids, as `PerAssetValueBalance` sees them. -/
def inAsset (w : TxWitness depth nIn nOut) (i : ℕ) : F := (w.spent i).assetId
/-- Input values. -/
def inValue (w : TxWitness depth nIn nOut) (i : ℕ) : F := (w.spent i).value
/-- Output asset ids. -/
def outAsset (w : TxWitness depth nIn nOut) (j : ℕ) : F := (w.out j).assetId
/-- Output values. -/
def outValue (w : TxWitness depth nIn nOut) (j : ℕ) : F := (w.out j).value

end Lelantos
