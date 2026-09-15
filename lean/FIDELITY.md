# Fidelity: does the Lean model match the circuit?

The proofs in `lean/` are about `Lelantos.TransactSat`, a hand-written Lean model. They
are only worth something if that model mirrors the circuit: `Transact` and its transitive
closure, instantiated by `src/4x6.circom`. This file is the argument that it does, and the
list of where that argument is still thin.

## Which direction of error is dangerous

| Discrepancy | Effect on `transact_sound` | Caught by |
|---|---|---|
| Model has a constraint the circuit lacks | **Dangerous.** The theorem assumes something the prover need not satisfy. | Defence 2 (negative parity) — not yet built |
| Model omits a constraint the circuit has | Safe. `TransactSat` is weaker, so `TransactSat → TxWellFormed` is a *stronger* theorem than needed. | — |
| Model misreads *which* signal a constraint relates | **Dangerous** in both directions. | Defence 1 (table) + Defence 3 (layout parity) |

A fourth failure mode is worse than any of these and has its own check: if the model were
**unsatisfiable**, `transact_sound` would be vacuously true and every table below would be
irrelevant. `Lelantos.transactSat_satisfiable` (`Completeness.lean`) rules that out by
constructing a satisfying assignment at a small shape that exercises a full Merkle chain,
both value commitments, every balance candidate and the Horner evaluation.
`Lelantos.transact4x6Sat_satisfiable` does the same at the shipped `Transact(11, 4, 6)`, and
`Lelantos.batchSat_satisfiable` (`BatchCompleteness.lean`) covers `TreeUpdateBatch`.

### The direction the table does not have a column for

The table above classifies a *constraint* as present or absent. It has nothing to say about
how many signals are left **unconstrained**, and that is a distinct failure mode with its
own consequences.

`Lelantos.polyEval_forge` is the statement of it: `PolyEval` is affine in each coefficient
with slope `z ^ k`, and `z` is an input the prover reads before choosing a witness, so a
single coefficient the rest of the system leaves free is one linear equation in one unknown.
Solve it and `y` is whatever the contract asks for, for an unrelated transaction. No
collision, no low-probability event.

The circuit used to compress 69 coefficients at `Transact(11, 4, 6)`, of which 23 —
`recipient_address`, `chain_id`, `payer_address`, `relayer_address`, `out_aux_digest` and
the eighteen FMD clue fields — were declared, wired into `TransactCompressN`, and read
nowhere else. The model transcribed that faithfully. **By the table, faithful is safe.** It
was not.

An exact transcription cannot be caught by a transcription check. What catches this is
counting degrees of freedom. The layout now carries 46 coefficients, one per slot that some
constraint pins, and the pinning table in `Lelantos/Circuit/Transact.lean` names the
constraint behind each. The 23 are bound through the Fiat-Shamir challenge instead:
`PubInputs.sol` hashes 70 words and evaluates 46, so altering any of them moves `z`, hence
`y`, and needs no constraint at all.

**Adding a public input is therefore a fidelity question with a second half:** transcribe
the constraint, then say which constraint outside `PolyEval` pins it — a range check, a
commitment, an equality. If the answer is "none", it is a challenge word, not a coefficient.

Two further consequences are modelled rather than assumed:

* `TransactSat.not_all_dummy` — `MerkleProofOrDummy` skips the root comparison on a dummy
  slot, so an all-dummy witness leaves `merkleRoot` read by nothing. It was the last free
  coefficient after the 23 were removed. `TxWellFormed.someRealInput` is what the circuit's
  `IsEqual` on the dummy count buys.
* `ContractObligations.challenge_binds_witness` used to be `True`, under an earlier name.
  A `True` field states no
  property, so no fidelity check can fail on it, and the prose around it read as though the
  contract discharged it. It is now
  `challenge_binds_witness : chal (txCoeffs w) w.z` — a relation between the challenge and
  the *witness*. The remaining three stubs are still `True` and should be read as claims
  made outside Lean.

What is still not closed: `publicAssetId`, `publicIn` and `publicOut` are pinned only to
64 bits each, and two of those directions are genuinely free (see `README.md`). That is
about `2⁻¹²⁶`, bounded by the range checks rather than eliminated.

Known deliberate omissions, all in the safe directionKnown deliberate omissions, all in the safe direction of the table above — but see the
section immediately above for why "safe by that table" is not the same as harmless:

* `PerAssetPointBalance` **is** modelled (`TransactSat.point_balance`) but nothing is
  derived from it, because `pointBalance_not_sound` proves nothing can be. It is stated
  over the published coordinate pairs, folded with `babyAdd` the way `PointSum` builds
  them. That is a change: it used to be stated over group elements, which required six
  further fields tying each `cv` / `rH` pair and each bucket point to a subgroup element.
  Those six had no circom counterpart — `4x6.circom` imposes no subgroup or curve check on
  them — so by the table at the top of this file they were the model's only constraints in
  the **dangerous** direction. Restating `PointSum` over `Pt` removed all six, and the
  counterexample now travels group-to-coordinates through
  `perAssetPointBalance_of_group` rather than the other way.
* The FMD clue fields are not signals of `Transact` at all, so the model has no fields for
  them. They were `PolyEval`-bound only, which is the same as unbound; they are challenge
  words now (`src/README.md § 2a`).
* `out_aux_digest` is likewise not a signal. Being full-field it could never have been
  pinned by a range check, which is why the split is the only fix. That the digest is the
  true hash of the aux calldata is still checked on-chain and recorded in
  `ContractObligations.aux_digest_recomputed`.
* `Num2Bits`' `<--` witness hints are not modelled, only the `===` constraints beneath
  them. The hints carry no soundness weight.

## Defence 1 — constraint-by-constraint table

Every `===` / `<==` written in `src/lib/*.circom` — the transitive closure of `src/4x6.circom`
and `src/tree_update_batch.circom`, minus `node_modules/circomlib` — appears
in the tables below, with **two** stated exceptions, both of them repo-owned code that is
collapsed rather than transcribed:

1. `src/lib/fixed_base_mul.circom` — `FixedBaseMulBits` / `FixedBaseMul`, ~270 lines and 748
   constraints — is collapsed into the `escalarMul` / `escalarMul_spec` axiom pair
   (`Lelantos/Model/Jubjub.lean`). Note this is **not** covered by the circomlib carve-out
   below: `MulH` deliberately does not use circomlib's `EscalarMulFix`
   (`src/lib/value_commit.circom`), so this is the repo's own gadget behind an axiom.
2. `EmptySubtreeHashes` / `EMPTY_SUBTREE` (`src/lib/common.circom`) has no rows. In Lean
   `zeros : ℕ → F` is a free parameter, never tied to the eleven hard-coded constants, and
   the constraint systems accept any fill, which is the safe direction. The batch results,
   however, assume `ZerosCoherent` (`Gadgets/Common.lean`) — that the fills are the
   empty-subtree chain — for the reason the header of `src/lib/batch_append.circom` gives.
   Lean cannot evaluate Poseidon, so the chain is a hypothesis, not a transcription;
   `test/merkle.test.ts` pins the constants to it numerically, and
   `ZerosCoherent.eq_emptyChain` shows the hypothesis determines the table.

See "What is not proved" in [README.md](README.md). `src/4x6.circom` is the only transact
top-level the repository ships, instantiating `Transact(11, 4, 6)`; the smaller shapes that
appear in `Proofs/Completeness.lean` are witness constructions, not circuits. The shared
wiring lives in `src/lib/transact.circom`, which the tables cite as `transact:`.

The correspondence is one row to one Lean field, with three documented exceptions:

* **circomlib gadgets are collapsed, not transcribed.** `Poseidon`, `BabyAdd`, `EscalarMulAny`
  / `EscalarMulFix` and `Pedersen` become opaque Lean functions with axiomatised semantics
  (`Lelantos.Meta.Assumptions`). Their internal constraints have no Lean counterpart. The two
  circomlib templates the model *does* transcribe are `Num2Bits` (`Bits.lean`) and `IsZero` /
  `IsEqual` (`Comparators.lean`), because their soundness is load-bearing.
* **`ValueTimesGen` is split** across two model fields — see its row below.
* **`HashToAssetGen`'s Pedersen is collapsed** into `assetGen` — see its own section below.

Line citations in the Lean sources are the same correspondence at finer grain: every `…Sat`
field's doc comment names the circom lines it mirrors. `lean/scripts/check-citations.py` (run by
`check-all.sh`) resolves each one, so a citation into a deleted file or past the end of a
surviving one is a build failure. A bare `:lo-hi` resolves against the last path named in
the same file — with a line number, or in a markdown heading, which is how the tables here
are anchored. Anchoring on headings matters: without it the rows under a heading resolve
against whatever file some earlier prose happened to name, or, before any full citation
appears in the file, against nothing at all, and are silently skipped. Both happened.

The checker also **anchors**: where the doc comment quotes something in backticks that is
also vocabulary of the cited file — `` `acc[0] <== 0` ``, `` `HashToAssetGen` ``,
`` `is_deposit` `` — that word has to appear inside the cited span. A drift that stays
inside the file's length used to pass even when every number was wrong, which is how this
rotted twice: `src/tree_update_batch.circom` had drifted by 15 to 23 lines, was corrected,
and had drifted again by 25 lines in the chain half and 72 in the insert half, while
`src/lib/transact.circom` had gone 18 out and `src/lib/poly_eval.circom` 13 to 19. Every
one of those now fails the check, which also prints where the anchors have moved to.

Two things it still cannot check. A citation that quotes nothing from its file gets
existence and range only. And a citation into `contracts/` or `sdk/` — sibling
repositories rather than directories of this one — is verifiable only in a workspace that
has checked both out; CI checks out this repository alone, so it counts those as skipped
and says how many rather than failing on how the tree was cloned. The four that exist
today are checked locally, which is where a `PubInputs.sol` citation aimed at `src/lib/`
rather than `src/libs/` was caught. (Naming the wrong path in full here would itself be a
citation, and this check would fail on the sentence describing it.)

The companion check is `lean/scripts/check-names.py`, which resolves the `Lelantos` names
the prose claims exist. Comments hold no identifiers the compiler resolves, so a renamed
theorem — or one described in a module note and never written — is invisible to `lake
build`. Both existed: a theorem named transact_y_not_binding was cited three times as the
result showing `y` does not determine the transaction, and one named activeIdx_eq was cited
as the lemma consuming the chained circuit's per-slot index decomposition. (Neither name is
written in backticks here, because backticks are what the checker reads as a claim.) Neither
had been written, and in the second case the constraint it was supposed to justify was
consumed by nothing at all. The lemma that closed it was later removed along with the chain
it described; `batch_capacity` consumes the one range check that replaced it.

### `src/lib/balance.circom`

| circom | Lean |
|---|---|
| `:11` `RangeCheck64` → `Num2Bits(64)` | `RangeCheck64Sat` / `Num2BitsSat` (`Bits.lean`) |
| `:24-41` `ValueTimesGen` = `RangeCheck64` + `ValueScalarMul` | no single definition: the two halves are modelled separately as `TransactSat.pub_in_range` / `pub_in_mul` and `pub_out_range` / `pub_out_mul`. The template has no state of its own, so splitting it is an exact transcription, not a weakening. |
| `:48` `dummy*(dummy-1) === 0` | `DummyZeroValueSat` (first conjunct) |
| `:49` `dummy*value === 0` | `DummyZeroValueSat` (second conjunct) |
| `:108-110` `pub_eq[c] = IsEqual(pa, cand[c])` | `PerAssetValueBalanceSat.pubEq_sat` |
| `:113` `lhs[c][0] <== public_in * pub_eq[c]` | `lhs_chain` initial value |
| `:114` `rhs[c][0] <== public_out * pub_eq[c]` | `rhs_chain` initial value |
| `:117-119` `in_eq[c][i] = IsEqual(in_asset[i], cand[c])` | `inEq_sat` |
| `:120` `in_term[c][i] <== in_value[i] * in_eq[c][i]` | `inTerm_def` |
| `:121` `lhs[c][i+1] <== lhs[c][i] + in_term[c][i]` | `lhs_chain` step |
| `:124-126` `out_eq[c][j] = IsEqual(out_asset[j], cand[c])` | `outEq_sat` |
| `:127` `out_term[c][j] <== out_value[j] * out_eq[c][j]` | `outTerm_def` |
| `:128` `rhs[c][j+1] <== rhs[c][j] + out_term[c][j]` | `rhs_chain` step |
| `:131` `lhs[c][N_IN] === rhs[c][N_OUT]` | `balanced` |
| `:90-97` `cand[]` fill | `candAt` |
| `:185-186` point equality | `PerAssetPointBalanceSat` (`PointBalance.lean`) |

### `src/lib/asset_gen.circom`

`HashToAssetGen` is the one template whose body is **not** transcribed constraint-for-constraint.
Its `Num2Bits` is; its Pedersen is collapsed into an opaque function plus an axiom.

| circom | Lean |
|---|---|
| `:18-19` `Num2Bits(64)(asset_id)` | `Num2BitsSat 64` — `SpentNoteSat.asset_bits`, `OutputNoteSat.asset_bits`, `TransactSat.pub_asset_range`. This is where every `asset_id < 2^64` in the development comes from. |
| `:23-29` `Pedersen(72)` over `TAG_ASSET ‖ asset_id_LE` | **collapsed**, not transcribed: `Lelantos.assetGen : F → G` (`Jubjub.lean`), an opaque function of the asset id. The 8 constant tag bits and the 64 wired input bits have no Lean counterpart. |
| `:31-32` `gen[0..1] <== p.out[0..1]` | `gen_def : gen = coords (assetGen asset_id)` — `SpentNoteSat`, `OutputNoteSat`, `TransactSat.pub_gen` |

The collapse is safe in the direction that matters. Modelling `assetGen` as opaque means the
proofs may assume **nothing** about it beyond being a subgroup element — strictly weaker than
what the circuit computes, so it is the safe direction of the table above.

The one property the development *does* assume is the axiom `assetMul` (`Jubjub.lean`): every
`assetGen a` is a known multiple of `BASE0`. That is a **weakness** of the circuit, deliberately
imported so `pointBalance_not_sound` can exhibit it, and `assetMul_arith` (`assetMul 1 +
assetMul 3 = 2 · assetMul 2`) is checked against the real gadget at runtime by
`test/transact/multi_asset.test.ts` ("FAILS on cross-asset cancellation V^1 + V^3 ==
2·V^2"). No positive result depends on either.

### `src/lib/common.circom` / `src/lib/merkle.circom`

| circom | Lean |
|---|---|
| `common:16-17` `Num2Bits(2)(path_index)` | `PathIndexSelectorsSat` first conjunct |
| `common:21-26` `bb`, `s[0..3]` | `PathIndexSelectorsSat` remaining conjuncts |
| `merkle:35-64` four slot equations | `MerkleLevel4Sat` `c 0 … c 3` |
| `merkle:66-74` `out = Poseidon(TAG_MERKLE, c0..c3)` | `MerkleLevel4Sat` last conjunct / `merkleNode` |
| `merkle:84-96` level chain | `MerkleRootSat` |
| `merkle:109` `is_dummy*(is_dummy-1) === 0` | `MerkleProofOrDummySat.dummy_bit` |
| `merkle:121` `diff <== root' - root` | `MerkleProofOrDummySat.diff_def` |
| `merkle:122` `(1-is_dummy)*diff === 0` | `MerkleProofOrDummySat.matches_root` |

### `src/lib/batch_append.circom`

The construction is explained in that file's header; the rows are its constraints. Every
`BatchAppend` signal lives in `BatchAppendSignals`, and the numeric side conditions of an
instance in `BatchShape`.

| circom | Lean |
|---|---|
| `:57-70` `BATCH_WINDOW` | `batchWindow`; `batchWindow_eq_circom` against the literal clamp |
| `:75-84` `BATCH_SRC`, `p = 4 * j + k - r` | `batchSrc`; `batchSrc_eq_circom` against the signed `ℤ` computation |
| `:88-104` `BATCH_NPROD` | none needed — it only sizes `prod`, and `assert(pi == NPROD)` fails compilation on a mismatch |
| `:115` `assert(EMPTY_SUBTREE(0) == 0)` | `ZerosCoherent`, first conjunct — a hypothesis, see exception 2 |
| `:129` `assert((1 << COUNT_BITS) == MAX_L)` | `BatchShape.pow_count` |
| `:130-131` `Num2Bits(COUNT_BITS)(actual_count - 1)` | `BatchAppendSat.count_bits` |
| `:133-139` `LessThan(COUNT_BITS+1)(k, actual_count)` | `BatchAppendSat.active_def` |
| `:144-145` `Num2Bits(BITS)(start_index)` | `BatchAppendSat.index_bits` |
| `:146-147` `last_idx_bits.in <== start_index + actual_count - 1` | `BatchAppendSat.last_idx_bits` |
| `:153` `bb[d] <== idx_bits.out[2 * d] * idx_bits.out[2 * d + 1]` | `BatchAppendSat.bb_def` / `bitPairs` |
| `:154-157` `s[d][0..3]` over the bits and `bb` | `batchSel`, `appendSel` |
| `:161-169` `(1 - read) * frontier_in[d][k] === 0` | `BatchAppendSat.frontier_pin` / `batchRead` |
| `:175` `old_node[0] <== 0` | `BatchAppendSat.old_base` |
| `:178` `old_h[d].inputs[0] <== tag` | `BatchAppendSat.old_def` via `merkleNode` |
| `:179-187` `old_prod[d][k] <== s[d][k] * old_node[d]` with the frontier and empty-subtree terms | `BatchAppendSat.old_def` via `oldChild` |
| `:190` `old_node[d + 1] <== old_h[d].out` | `BatchAppendSat.old_def` |
| `:192` `old_root <== old_node[DEPTH]` | `BatchAppendSat.old_root_def` |
| `:203` `assert(W[DEPTH] == 1)` | `batchWindow_top` |
| `:207` `node[OFF[0] + t] <== active[t] * leaves[t]` | `BatchAppendSat.leaf_def` |
| `:222` `h[hi].inputs[0] <== tag` | `BatchAppendSat.node_def` via `merkleNode` |
| `:225-240` `prod[pi] <== s[d][r] * node[OFF[d] + src]` with the frontier and empty-subtree terms | `BatchAppendSat.node_def` via `batchChild` |
| `:242` `node[OFF[d + 1] + j] <== h[hi].out` | `BatchAppendSat.node_def` |
| `:247` `new_root <== node[OFF[DEPTH]]` | `BatchAppendSat.new_root_def` |

`oldChild` and `batchChild` state the children exactly as the circuit sums them: the frontier
slot as a linear term, then one term per digit — a selector product with a window node or the
running node, or the selector times the empty subtree. `oldChild` collects the empty-subtree
digits into one coefficient, as the circuit's `below` does, and `batchChild` visits the digits
in the circuit's own order, so every assignment satisfying the constraints satisfies
`old_def` and `node_def`. The linear frontier term is the circuit's own, not a model
simplification — what makes it the frontier slot the digit selects is the pin, and
`batchAppend_frontier_zero` is where that is proved.

`node d t` is two-dimensional in Lean and the flat `node[OFF[d] + t]` in the circuit, with
`OFF[d] = Σ_{e<d} W[e]` (`batchWindow_deployed` evaluates the widths). `signal-map.json` can
only check that `main.append.node[0..28]` exist; the `OFF` correspondence is this paragraph,
and it is injective because every read and write stays below its level's width (`batchSrc`
names a node only below `w`, `leaf_def` has `t < maxL`, `node_def` has `j < W[d+1]`).

Note the shape of the `last_idx_bits` row. The circuit range-checks one index, the last
inserted one, so the model must too: a bound over `start_index + k` for every slot would put a
constraint in the model that the circuit does not impose — the dangerous direction of the
table at the top of this file — and would be false of an honest batch ending on the final
index of the tree. `batchAppend_witness` shows the whole system is satisfiable at every start,
count and canonical frontier, so `frontier_pin` is not over-strict either.

### `src/tree_update_batch.circom`

Split across two Lean structures — `BatchChainSat` and `BatchDepositSat` — so that the
append results reach no curve axiom. `EMPTY_SUBTREE` is a parameter of the constraint system,
not a signal, so it is an argument of `BatchChainSat` rather than a field of `BatchSignals`.

| circom | Lean |
|---|---|
| `:128-135` `leaf = Poseidon(TAG_LEAF, cm, cv_dep.x, cv_dep.y)` | `BatchChainSat.leaf_def` |
| `:141-151` `BatchAppend(DEPTH, MAX_L)` over `start_index`, `actual_count`, `leaves`, `frontier_in` | `BatchChainSat.append` |
| `:152` `old_root === append.old_root` | `BatchChainSat.old_root_def` |
| `:153` `new_root === append.new_root` | `BatchChainSat.new_root_def` |
| `:158` `(1-append.active)*cms === 0` | `BatchChainSat.pad_cm` |
| `:159-160` `(1-append.active)*cv_dep[0..1] === 0` | `BatchChainSat.pad_cv_x` / `pad_cv_y` |
| `:161-164` `(1-append.active)*{leaf_asset, leaf_public_in, is_deposit, rcv} === 0` | `BatchChainSat.pad_asset` … `pad_rcv` |
| `:171` `is_deposit*(1-is_deposit) === 0` | `BatchChainSat.deposit_bit` |
| `:172-173` `(1-is_deposit)*{leaf_asset, leaf_public_in} === 0` | `BatchChainSat.spend_zero_asset` / `spend_zero_public_in` |
| `:180-185` `BabyCheck(cv_dep.x, cv_dep.y + (1-append.active))` | **absent** — no curve equation in the model |
| `:198` `active_dep <== append.active * is_deposit` | `BatchDepositSat.active_dep_def` |
| `:200-201` `IsZero(leaf_asset)` | `BatchDepositSat.asset_isZero` |
| `:225-226` `IsZero(leaf_public_in)` | `BatchDepositSat.public_in_isZero` |
| `:257` step 6a `active_dep * (leaf_asset_nz.out - pub_in_nz.out) === 0` | `BatchDepositSat.asset_matches_value` |
| `:203-204` `HashToAssetGen(leaf_asset)` | `BatchDepositSat.gen_def` |
| `:207-210` `ValueTimesGen(leaf_public_in, gen)` | `BatchDepositSat.public_in_range` + `expected_def` (`ValueCommitSat.value_term`) |
| `:213-214` `MulH(rcv)` | `BatchDepositSat.expected_def` (`ValueCommitSat.blind_term`) |
| `:216-220` `expected = BabyAdd(pub_in_mul, rH)` | `BatchDepositSat.expected_def` (`ValueCommitSat.sum_def`) |
| `:222-223` `active_dep*(cv_dep - expected) === 0` | `BatchDepositSat.deposit_x` / `deposit_y` |
| `:261-274` `BatchCompress(MAX_L)` | `batchPiSlot` / `batchSlotValue`, dumped to `expected/layout-batch-8.txt` by `dump-layout.sh`. The Horner chain itself is `polyEval_sound`, proved generically |

One row is deliberately empty: `BabyCheck` is a genuine gap, listed in the README. The old
root used to be a second — `FrontierRoot` was not modelled — and is now `batch_old_root`.

`BatchCompress` used to be a gap too. The Horner chain was always covered generically by
`polyEval_sound` / `polyEval_binding`, but the *order* of the 52 coefficients was not, and
`test/formal/batch_layout_parity.test.ts` anchored it on the published vector — the file the
SDK and the contracts fixture also read, so a drift the generator agreed with was invisible
in all three. `batchPiSlot` is now that anchor.

### `src/lib/note.circom`

| circom | Lean |
|---|---|
| `:13-22` `ivk = Poseidon(TAG_IVK, nsk)` | `deriveIvk` |
| `:25-33` `nk = Poseidon(TAG_NK, nsk)` | `deriveNk` |
| `:36-44` `pk = Poseidon(TAG_PK, ivk)` | `derivePk` |
| `:61` `packed_av <== asset*2^64 + value` | `packAV` |
| `:63-68` `cm = Poseidon(packed_av, pk, rho, rcm)` | `noteCommitment` |
| `:76-86` `rho = Poseidon(TAG_RHO, nf0, index)` | `deriveRho` |
| `:97-109` `nf = Poseidon(TAG_NF, nk, rho, cm)` | `nullifierOf` |

### `src/lib/value_commit.circom`

| circom | Lean |
|---|---|
| `:32-46` `ValueScalarMul` | `ValueScalarMulSat` |
| `:51-64` `MulH` (`Num2Bits(252)` + `FixedBaseMul`) | `MulHSat` |
| `:78-123` `ValueCommitPair` — one shared `value·gen`, two blinders | two independent `ValueCommitSat` instances per note slot (same constraint set; see the `Gadgets/ValueCommit.lean` module note) |
| `:144-151` `cv = BabyAdd(vT, rH)` | `ValueCommitSat` third conjunct; opened by `valueCommit_opens` |
| `:157-183` `PointSum` chain | `pointSum` |

### `src/lib/spent.circom` / `src/lib/output.circom`

`SpentNoteSat` and `OutputNoteSat` are named-field structures: one field per circom
constraint, in circom source order, each field's doc comment citing the source line it
mirrors. They can be read side by side with the originals and checked a row at a time.

### `src/lib/poly_eval.circom` / `src/lib/transact.circom`

| circom | Lean |
|---|---|
| `poly_eval:32` `acc[0] <== 0` | `PolyEvalSat` first conjunct |
| `poly_eval:33-35` Horner step | `PolyEvalSat` second conjunct |
| `poly_eval:36` `y <== acc[N]` | `PolyEvalSat` third conjunct |
| `poly_eval:81-108` coefficient layout | `piSlot` + `slotValue` |
| — `out_aux_digest` is no longer a coefficient | **absent by design** — no `PISlot` constructor; it is a challenge word, see § "The direction the table does not have a column for" |
| `transact:151-154` `out_rho[j] === DeriveRho(nf0, j)` | `TransactSat.rho_derived` |
| `transact:168-169` `out_cv_dep === OutputNote.cv_dep` | `TransactSat.cv_dep_bound` |
| `transact:106` `spent[i].root <== merkle_root` | `TransactSat.spent_root` |
| `transact:175-189` public bucket | `pub_gen`, `pub_in_range`, `pub_out_range`, `pub_in_mul`, `pub_out_mul` |

## Defence 2 — witness parity harness

**Not built.** It would be a `modelcheck` executable loading a real circom witness plus
`build/4x6.sym`, checking `TransactSat` evaluates to `true` on it and comparing every
modelled intermediate signal against the circom-computed value at the matching label, plus a
negative pass replaying the rejecting cases from [test/transact/](../test/transact/) and
asserting the model rejects them too.

This is the defence that would catch a model *stronger* than the circuit — the dangerous
direction in the table above. It is the only one that would. Treat the transcription as
unverified in that direction.

Two things about building it are worth recording, because they are the parts that are not
obvious. The first is that **`TransactSat` is not executable**: `poseidon`, `babyAdd`,
`escalarMul`, `coords` and `assetGen` are opaque or axiomatised, so there is nothing to run.
The resolution is not to make them computable but to split every field in two — the
arithmetic ones (`dummy_zero`, `count_bits`, the balance chains, the muxes, `Num2BitsSat`,
`PolyEvalSat`) evaluate directly, and the gadget ones do not evaluate at all. For those,
what the model claims is a *wiring* fact: that `cm_def`'s arguments are the values on
`main.spent[0].cm.h.inputs[0..3]` and its result is the value on `.out`. That is checkable,
and it is the whole transcription content of an equation over an opaque function.

The second is that an executable mirror nobody proved equivalent is a third copy of the
model, free to drift from the one the theorems are about. `transactSatB : TxWitness → Bool`
needs `transactSatB w = true → TransactSat w` alongside it, or the harness checks something
other than what is proved.

Its prerequisite now exists: Defence 5 is the signal map such a harness needs in order to
read a witness vector into a `TxWitness` at all.

## Defence 3 — public-input layout parity

Built and running, for both circuits. The transact 69-slot ordering exists in four
implementations:

1. `src/lib/poly_eval.circom :: TransactCompressN`
2. `contracts/src/libs/PubInputs.sol :: compress(Transact, aux)`
3. `test/ref/compress.ts :: coeffs`
4. `lean/Lelantos/Circuit/Witness.lean :: piSlot`

Checks, each mechanical:

| Link | Check |
|---|---|
| Lean → `expected/layout-4x6.txt` | `lean/scripts/dump-layout.sh` |
| `expected/layout-4x6.txt` → SDK | `test/formal/layout_parity.test.ts`, sentinel-per-field so any transposition fails |
| SDK → circuit | existing PolyEval binding cases, `test/transact/binding.test.ts` |

The sentinel-per-field table in the second row is hand-written and is what catches a
transposition between two slots of the same type. `PubInputs.sol` has no 69-slot `compress`
overload, so the chain currently ends at the published vector rather than at the contract.

The batch has the same chain, and it is newer. `Lelantos.batchPiSlot` →
`lean/expected/layout-batch-8.txt` (`dump-layout.sh`) → `vectors/tree-update-batch-8.json`
(`test/formal/batch_layout_parity.test.ts`) → the SDK and the contracts fixture, which read
that vector. Before the Lean definition existed the batch test anchored on the vector's own
`circuit.layout`, which is what the generator wrote — so a drift agreed on by the generator,
the SDK and the fixture was consistent everywhere and visible nowhere. All 52 batch words
are coefficients, unlike transact's 46-of-69, because every one of them is a signal of
`tree_update_batch.circom` and hashing a signal into `z` binds nothing against a prover that
reads `z` first.

The layout is defined once in Lean (`piSlot`) and the value lookup (`slotValue`) is
separate, so the dumped names are derived from the same definition the proofs use rather
than being a second copy of it.

## Defence 4 — constraint coverage

Built and running: `lean/scripts/check-coverage.py`, in `check-all.sh` and in CI.

Defence 1 claims every `===` and `<==` in the closure appears in its tables. Defence 4 is
that claim, mechanised from the other end: it extracts every constraint-emitting line from
the circom and every cited span from `lean/`, and asks which lines no citation reaches.

The result is graded, because two different things were being conflated. A line inside a
citation of at most twenty lines is **transcribed** — that width is where the data
separates, a narrow citation naming one constraint or one contiguous wiring block a single
model field abstracts, a wider one naming a whole template. A line reached only by a
template-wide citation is **pointer-only**: evidence about the template, not about that
line. A line nothing reaches is **uncited**.

329 of 431 constraints are transcribed. The residue is pinned in `expected/coverage.txt` and
diffed the way `check-axioms.sh` pins the trusted base, so a new uncited constraint appears
in review rather than in nobody's eye. The uncited part of it is *exactly* the two exceptions
Defence 1 states — `fixed_base_mul.circom` and `EmptySubtreeHashes`. It was three while the
old root lived in an unmodelled `frontier_root.circom`, whose 29 uncited lines went when
`BatchAppend` absorbed it.

Writing it found two things beyond drifted line numbers. `merkle.circom`'s
`root <== cur[depth]` was cited three lines off, and — the more interesting one — the
citation form `` `:70-77, 118-119` `` was being read as a single span, silently discarding
everything after the comma. Several fields that looked cited had no working citation over
half of what they mirrored. The scanner now parses span lists, and anchors them together.

## Defence 5 — signal parity

Built and running: `lean/expected/signal-map.json`, checked from both ends.

Every field of `TxWitness`, `SpentSlot`, `OutputSlot` and `BatchSignals` claims to *be* a
signal of the compiled circuit. Nothing checked the claim — `lake build` sees Lean, the
circuit suites see circom, and the sentence joining them lived in a doc comment. The map
writes that sentence down: `test/formal/signal_parity.test.ts` checks each named signal
exists in `build/*.sym`, and `check-names.py` checks each key is a real Lean field. Neither
side can drift without one of them failing.

Three things come with it that were not the point but are worth having:

* **Arity is read off the circuit.** Each template is checked at every index below its bound
  *and* at the bound, where the signal must be absent. `Transact(11, 4, 6)` is therefore
  verified against the compiled artifact rather than asserted in `constants.ts`.
* **The optimizer becomes a witness.** circom deletes a signal that a constraint pins to a
  constant, and the `absent` section asserts those deletions *persist*, with the reason.
  `main.all_dummy.out` is gone because `all_dummy.out === 0` holds it at zero — the
  constraint `TransactSat.not_all_dummy` models and `TxWellFormed.someRealInput` rests on.
  If that constraint is ever dropped, the signal reappears and the check fires. The same
  goes for `out_note[].asset_nz.out` (`asset_nz.out === 0`, what keeps `packed_av ≥ 2^64`)
  and for the top of the `rhs` accumulator, which exists only because
  `lhs[c][N_IN] === rhs[c][N_OUT]` merges it away.
* **It is the input Defence 2 needs.** A witness harness has to turn a flat witness vector
  into a `TxWitness`; this is the map that does it.

What Defence 5 does **not** check is that a field mirrors the *right* signal. A field
pointed at a real but wrong signal passes. That is Defence 2's job.

