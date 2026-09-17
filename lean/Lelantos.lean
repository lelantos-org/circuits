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

-- The quaternary tree the tree gadgets are proved against: no signals, only the tree an append
-- produces and the insert it is made of. Built on the hash definitions above.
import Lelantos.Spec.QuatTree

import Lelantos.Gadgets.PolyEval
import Lelantos.Gadgets.Balance
import Lelantos.Gadgets.Merkle
import Lelantos.Gadgets.BatchAppend
import Lelantos.Gadgets.ValueCommit
import Lelantos.Gadgets.PointBalance

-- The transact circuit, one module per job: the two slot templates, the signal set, the
-- public-input layout, and the constraint system with `transact_sound`.
import Lelantos.Circuit.Spent
import Lelantos.Circuit.Output
import Lelantos.Circuit.Witness
import Lelantos.Circuit.Layout
import Lelantos.Circuit.Transact

-- The relayer batch tree-advance circuit (`src/tree_update_batch.circom`), split the same
-- way: signals, layout, constraint system.
import Lelantos.Circuit.BatchWitness
import Lelantos.Circuit.BatchLayout
import Lelantos.Circuit.TreeUpdateBatch

-- What neither circuit can enforce and its verifier must, for both of them.
import Lelantos.Circuit.Obligations

-- Results about the finished system: which assignments exist, and which cannot.
import Lelantos.Proofs.Completeness
import Lelantos.Proofs.BatchCompleteness
import Lelantos.Proofs.Rejection

/-!
# `Lelantos` — a machine-checked soundness proof for the transact circuit

Importing this module brings in the whole development. The layers are strictly ordered:
`Model` depends on nothing else here, `Gadgets` on `Model`, `Spec` on the hash definitions in
`Gadgets.Note` and `Gadgets.Common` (and the tree gadgets on `Spec`), `Circuit` on the gadgets,
and `Proofs` on the finished circuit. `Meta` imports this module and reports on it, so
`lakefile.toml` declares it as a separate build target.
-/
