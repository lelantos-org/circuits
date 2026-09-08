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
`PubInputs.sol` hashes 69 words and evaluates 46, so altering any of them moves `z`, hence
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
in the tables below, with **three** stated exceptions, all of them repo-owned code that is
collapsed rather than transcribed:

1. `src/lib/frontier_root.circom` is not modelled at all, so its 29 constraint lines have no
   rows here. `README.md` calls this the largest remaining gap in the batch proof.
2. `src/lib/fixed_base_mul.circom` — `FixedBaseMulBits` / `FixedBaseMul`, ~270 lines and 748
   constraints — is collapsed into the `escalarMul` / `escalarMul_spec` axiom pair
   (`Lelantos/Model/Jubjub.lean`). Note this is **not** covered by the circomlib carve-out
   below: `MulH` deliberately does not use circomlib's `EscalarMulFix`
   (`src/lib/value_commit.circom`), so this is the repo's own gadget behind an axiom.
3. `EmptySubtreeHashes` / `EMPTY_SUBTREE` (`src/lib/common.circom`) has no rows. In Lean
   `zeros : ℕ → F` is a free parameter (`Gadgets/Insert.lean`,
   `Circuit/TreeUpdateBatch.lean`), never tied to the eleven hard-coded constants. This is
   the safe direction — `InsertsTo` says "whatever fill the witness supplied" rather than
   "the empty subtree" — but it is a gap, not a transcription.

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
one of those now fails the check; `--suggest` prints where the anchors have moved to.

What still cannot be checked is a citation that quotes nothing from its file. Those get
existence and range only, and `--list` marks them.

The companion check is `lean/scripts/check-names.py`, which resolves the `Lelantos` names
the prose claims exist. Comments hold no identifiers the compiler resolves, so a renamed
theorem — or one described in a module note and never written — is invisible to `lake
build`. Both existed: a theorem named transact_y_not_binding was cited three times as the
result showing `y` does not determine the transaction, and one named activeIdx_eq was cited
as the lemma consuming `BatchChainSat.idx_bits`. (Neither name is written in backticks here,
because backticks are what the checker reads as a claim.) Neither had been written, and in the second case the constraint it
was supposed to justify was consumed by nothing at all — see `batch_active_index`, which is
that lemma.

### `src/lib/balance.circom`

| circom | Lean |
|---|---|
| `:11` `RangeCheck64` → `Num2Bits(64)` | `RangeCheck64Sat` / `Num2BitsSat` (`Bits.lean`) |
| `:24-41` `ValueTimesGen` = `RangeCheck64` + `ValueScalarMul` | no single definition: the two halves are modelled separately as `TransactSat.pub_in_range` / `pub_in_mul` and `pub_out_range` / `pub_out_mul`. The template has no state of its own, so splitting it is an exact transcription, not a weakening. |
| `:48` `dummy*(dummy-1) === 0` | `DummyZeroValueSat` (first conjunct) |
| `:49` `dummy*value === 0` | `DummyZeroValueSat` (second conjunct) |
| `:110-112` `pub_eq[c] = IsEqual(pa, cand[c])` | `PerAssetValueBalanceSat.pubEq_sat` |
| `:115` `lhs[c][0] <== public_in * pub_eq[c]` | `lhs_chain` initial value |
| `:116` `rhs[c][0] <== public_out * pub_eq[c]` | `rhs_chain` initial value |
| `:119-121` `in_eq[c][i] = IsEqual(in_asset[i], cand[c])` | `inEq_sat` |
| `:122` `in_term[c][i] <== in_value[i] * in_eq[c][i]` | `inTerm_def` |
| `:123` `lhs[c][i+1] <== lhs[c][i] + in_term[c][i]` | `lhs_chain` step |
| `:126-128` `out_eq[c][j] = IsEqual(out_asset[j], cand[c])` | `outEq_sat` |
| `:129` `out_term[c][j] <== out_value[j] * out_eq[c][j]` | `outTerm_def` |
| `:130` `rhs[c][j+1] <== rhs[c][j] + out_term[c][j]` | `rhs_chain` step |
| `:133` `lhs[c][N_IN] === rhs[c][N_OUT]` | `balanced` |
| `:92-99` `cand[]` fill | `candAt` |
| `:187-188` point equality | `PerAssetPointBalanceSat` (`PointBalance.lean`) |

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

### `src/lib/insert.circom`

| circom | Lean |
|---|---|
| `:34-35` `PathIndexSelectors(idx_digit)` | `QuaternaryInsertLevelSat.selectors` |
| `:41-43` `c0 = s0·cur + (1-s0)·f[0]` | `QuaternaryInsertLevelSat.c0_def` |
| `:50-53` `c1 = s0·z + s1·cur + (s2+s3)·f[1]` | `QuaternaryInsertLevelSat.c1_def` |
| `:60-63` `c2 = (s0+s1)·z + s2·cur + s3·f[2]` | `QuaternaryInsertLevelSat.c2_def` |
| `:69-71` `c3 = (s0+s1+s2)·z + s3·cur` | `QuaternaryInsertLevelSat.c3_def` |
| `:73-78` `cur_next = Poseidon(TAG_MERKLE, c0..c3)` | `QuaternaryInsertLevelSat.out_def` |
| `:94-96` `frontier_out[0..2]` | `QuaternaryInsertLevelSat.fout0_def` … `fout2_def` |
| `:112` `cur[0] <== leaf` | `QuaternaryInsertSat.base` |
| `:114-126` level chain | `QuaternaryInsertSat.level` |
| `:128` `root <== cur[DEPTH]` | `QuaternaryInsertSat.top` |

The child mux and the frontier mux are transcribed as separate fields on purpose: they differ
at slots 1 and 2 (`(s2+s3)·f[1]` versus `(1-s1)·f[1]`), which the circom comment at `:81-87`
flags. Collapsing them in the model would make a real edit invisible.

### `src/tree_update_batch.circom`

Split across two Lean structures — `BatchChainSat` and `BatchDepositSat` — so that the
append results reach no curve axiom.

| circom | Lean |
|---|---|
| `:138-139` `Num2Bits(COUNT_BITS)(actual_count - 1)` | `BatchChainSat.count_bits` |
| `:145-148` `LessThan(COUNT_BITS+1)(k, actual_count)` | `BatchChainSat.active_def` |
| `:154` `(1-active)*cms === 0` | `BatchChainSat.pad_cm` |
| `:155-156` `(1-active)*cv_dep[0..1] === 0` | `BatchChainSat.pad_cv_x` / `pad_cv_y` |
| `:157-160` `(1-active)*{leaf_asset, leaf_public_in, is_deposit, rcv} === 0` | `BatchChainSat.pad_asset` … `pad_rcv` |
| `:167` `is_deposit*(1-is_deposit) === 0` | `BatchChainSat.deposit_bit` |
| `:168-169` `(1-is_deposit)*{leaf_asset, leaf_public_in} === 0` | `BatchChainSat.spend_zero_asset` / `spend_zero_public_in` |
| `:176-183` `leaf = Poseidon(TAG_LEAF, cm, cv_dep.x, cv_dep.y)` | `BatchChainSat.leaf_def` |
| `:192-194` `BabyCheck(cv_dep.x, cv_dep.y + (1-active))` | **absent** — no curve equation in the model |
| `:208` `active_dep <== active * is_deposit` | `BatchDepositSat.active_dep_def` |
| `IsZero(leaf_asset)` | `BatchDepositSat.asset_isZero` |
| `IsZero(leaf_public_in)` | `BatchDepositSat.public_in_isZero` |
| step 7a `active_dep * (IsZero(leaf_asset).out - IsZero(leaf_public_in).out) === 0` | `BatchDepositSat.asset_matches_value` |
| `:213-214` `HashToAssetGen(leaf_asset)` | `BatchDepositSat.gen_def` |
| `:217-220` `ValueTimesGen(leaf_public_in, gen)` | `BatchDepositSat.public_in_range` + `expected_def` (`ValueCommitSat.value_term`) |
| `:223-224` `MulH(rcv)` | `BatchDepositSat.expected_def` (`ValueCommitSat.blind_term`) |
| `:226-231` `expected = BabyAdd(pub_in_mul, rH)` | `BatchDepositSat.expected_def` (`ValueCommitSat.sum_def`) |
| `:232-233` `active_dep*(cv_dep - expected) === 0` | `BatchDepositSat.deposit_x` / `deposit_y` |
| `:287-288` `Num2Bits(2·DEPTH)(start_index)` | `BatchChainSat.start_index_bits` — the one line of step 8 that is modelled, because `batch_active_index` needs `start_index < 4^DEPTH` |
| `:290-299` `FrontierRoot` and `old_root === frontier_root.root` | **absent** — see README |
| `:331` `idx_in <== active * (start_index + k)` | `BatchChainSat.idx_in_def` |
| `:332-333` `Num2Bits(2·DEPTH)(idx_in)` | `BatchChainSat.idx_bits` |
| `:335-337` `idx_dig` from the bit pairs | `BatchChainSat.idx_dig` |
| `:340-347` `QuaternaryInsert(DEPTH)` per leaf | `BatchChainSat.insert` |
| `:313-315` `fr[0] <== frontier_in` | `BatchChainSat.fr_base` |
| `:318` `running_root[0] <== old_root` | `BatchChainSat.root_base` |
| `:352-354` frontier mux | `BatchChainSat.fr_mux` |
| `:358-360` root mux | `BatchChainSat.root_mux` |
| `:364` `new_root === running_root[MAX_L]` | `BatchChainSat.new_root_def` |
| `:367-380` `BatchCompress(MAX_L)` | `batchPiSlot` / `batchSlotValue`, dumped to `expected/layout-batch-8.txt` by `dump-layout.sh`. The Horner chain itself is `polyEval_sound`, proved generically |

Two rows are deliberately empty. `BabyCheck` and `FrontierRoot` are genuine gaps, not
simplifications, and both are listed in the README — though `FrontierRoot`'s own
`Num2Bits(2·DEPTH)` on `start_index` is modelled, since the position result depends on it.

`BatchCompress` used to be the third. The Horner chain was always covered generically by
`polyEval_sound` / `polyEval_binding`, but the *order* of the 52 coefficients was not, and
`test/formal/batch_layout_parity.test.ts` anchored it on the published vector — the file the
SDK and the contracts fixture also read, so a drift the generator agreed with was invisible
in all three. `batchPiSlot` is now that anchor.

Note the shape of the `idx_bits` row. The circuit range-checks `active[k] · (start_index + k)`,
so the model must too: stating it over `start_index + k` for every slot would put a
constraint in the model that the circuit does not impose — the dangerous direction of the
table at the top of this file — and would additionally be false of a batch whose last active
leaf sits at the final index of the tree, which the circuit accepts.

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
arithmetic ones (`dummy_zero`, `idx_dig`, the balance chains, the muxes, `Num2BitsSat`,
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

358 of 493 constraints are transcribed. The residue is pinned in `expected/coverage.txt` and
diffed the way `check-axioms.sh` pins the trusted base, so a new uncited constraint appears
in review rather than in nobody's eye. The uncited part of it is currently *exactly* the
three exceptions Defence 1 states — `frontier_root.circom`, `fixed_base_mul.circom` and
`EmptySubtreeHashes` — which is the first time that claim has been checked rather than
asserted.

Writing it found two things beyond drifted line numbers. `merkle.circom`'s
`root <== cur[depth]` was cited three lines off, and — the more interesting one — the
citation form `` `:71-78, 119-120` `` was being read as a single span, silently discarding
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

