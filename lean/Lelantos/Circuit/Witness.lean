import Lelantos.Circuit.Spent
import Lelantos.Circuit.Output

/-!
# The `Transact` signal set

The signals of `Transact(DEPTH, N_IN, N_OUT)`: the two slot arrays, the public bucket, the
compression pair and the dummy-count accumulator. Nothing here says what the circuit
constrains — that is `Lelantos.Circuit.Transact` — and nothing here says how the public
inputs are ordered, which is `Lelantos.Circuit.Layout`.

Each field names a signal of the compiled circuit; `lean/expected/signal-map.json` records
which, and `test/formal/signal_parity.test.ts` checks the name against `build/*.sym`.
-/

namespace Lelantos

/-- Every signal of `Transact(depth, nIn, nOut)`. -/
structure TxWitness (depth nIn nOut : ℕ) where
  /-- The only verifier-visible pair. -/
  z : F
  y : F
  /-- Logical public inputs. -/
  merkleRoot : F
  publicAssetId : F
  publicIn : F
  publicOut : F
  /-- Per-slot sub-circuits. -/
  spent : ℕ → SpentSlot depth
  out : ℕ → OutputSlot
  /-- Deposit value commitments, forwarded to `tree_update_batch`. -/
  outCvDep : ℕ → Pt
  /-- Public-bucket signals. -/
  pubGen : Pt
  pubAssetBits : ℕ → F
  pubInBits : ℕ → F
  pubOutBits : ℕ → F
  pubInPt : Pt
  pubOutPt : Pt
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
  /-- `PolyEval` accumulator. -/
  peAcc : ℕ → F
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
