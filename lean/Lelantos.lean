-- The ambient objects the circuit is written over: the field, bit decompositions, the hash,
-- and the curve group. None of these mirrors a circom template.
import Lelantos.Model.Field
import Lelantos.Model.Bits
import Lelantos.Model.Poseidon
import Lelantos.Model.Jubjub

-- One module per circomlib or `src/lib` template, each carrying its constraint system and
-- the theorem stating what those constraints buy.
import Lelantos.Gadgets.Comparators
import Lelantos.Gadgets.Common
import Lelantos.Gadgets.Note
import Lelantos.Gadgets.PolyEval
import Lelantos.Gadgets.Balance
import Lelantos.Gadgets.Merkle
import Lelantos.Gadgets.Insert
import Lelantos.Gadgets.ValueCommit
import Lelantos.Gadgets.PointBalance

-- The transact circuit: the two slot templates, its signals and public-input layout, and
-- the top-level constraint system with `transact_sound`.
import Lelantos.Circuit.Spent
import Lelantos.Circuit.Output
import Lelantos.Circuit.Witness
import Lelantos.Circuit.Transact

-- The relayer batch tree-advance circuit: `src/tree_update_batch.circom`.
import Lelantos.Circuit.TreeUpdateBatch

-- Results about the finished system: which assignments exist, and which cannot.
import Lelantos.Proofs.Completeness
import Lelantos.Proofs.BatchCompleteness
import Lelantos.Proofs.Rejection

/-!
# `Lelantos` — a machine-checked soundness proof for `src/2x2.circom`

Importing this module brings in the whole development. The layers are strictly ordered:
`Model` depends on nothing else here, `Gadgets` on `Model`, `Circuit` on both, and `Proofs`
on the finished circuit. `Meta` sits outside that chain — it imports this module and reports
on it, which is why `lakefile.toml` names it as a separate build target.
-/
