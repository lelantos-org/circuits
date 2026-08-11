# Fidelity: does the Lean model match the circuit?

The proofs in `lean/` are about `Lelantos.TransactSat`, a hand-written Lean model. They
are only worth something if that model faithfully mirrors the circuit — `Transact` and its
transitive closure, instantiated by `src/2x2.circom`, `src/2x3.circom` and `src/3x3.circom`.
This file is the argument that it does, and — just as importantly — the honest list of where
the argument is still thin.

## Which direction of error is dangerous

| Discrepancy | Effect on `transact_sound` | Caught by |
|---|---|---|
| Model has a constraint the circuit lacks | **Dangerous.** The theorem assumes something the prover need not satisfy. | Defence 2 (negative parity) — not yet built |
| Model omits a constraint the circuit has | Safe. `TransactSat` is weaker, so `TransactSat → TxWellFormed` is a *stronger* theorem than needed. | — |
| Model misreads *which* signal a constraint relates | **Dangerous** in both directions. | Defence 1 (table) + Defence 3 (layout parity) |

A fourth failure mode is worse than any of these and has its own check: if the model were
**unsatisfiable**, `transact_sound` would be vacuously true and every table below would be
irrelevant. `Lelantos.transactSat_satisfiable` (`Completeness.lean`) rules that out by
constructing a satisfying assignment for `Transact(10, 2, 2)` that exercises the full
10-level Merkle chain, both value commitments, all five balance candidates and the
30-coefficient Horner evaluation.

That construction is at the `2x2` shape only. `transact2x3_sound` and `transact3x3_sound`
have no exhibited witness, so for those two shapes this fourth failure mode is **not** ruled
out — see `lean/README.md § What is not proved`.

Known deliberate omissions, all in the safe direction:

* `PerAssetPointBalance` **is** modelled (`TransactSat.point_balance`) but nothing is
  derived from it, because `pointBalance_not_sound` proves nothing can be. `point_pub_in`
  and `point_pub_out` tie the group-level `pubInG` / `pubOutG` to the `pub_in_mul` /
  `pub_out_mul` signals; without them those two are free variables and the point equation
  is satisfiable for any assignment by solving for `pubOutG`.
* The FMD clue fields carry no constraint beyond `PolyEval` inclusion — that is the
  circuit's actual behaviour (`src/README.md § 1 "FMD clue binding"`), not a modelling shortcut.
* `out_aux_digest` likewise carries no constraint beyond `PolyEval` inclusion, again
  matching the circuit. Whether the digest is the true hash of the aux calldata is checked
  on-chain and recorded in `ContractObligations.aux_digest_recomputed`.
* `Num2Bits`' `<--` witness hints are not modelled, only the `===` constraints beneath
  them. That is exactly right: the hints carry no soundness weight.

## Defence 1 — constraint-by-constraint table

Every `===` / `<==` written in `src/lib/*.circom` — the transitive closure of `src/2x2.circom`
and `src/tree_update_batch.circom`, minus `node_modules/circomlib` — appears in the tables
below, with one stated exception: `src/lib/frontier_root.circom` is **not** modelled, so its
constraints have no rows here. See "What is not proved" in [README.md](README.md). The three top-level files do
nothing but instantiate `Transact(10, 2, 2)`, `Transact(10, 2, 3)` and `Transact(10, 3, 3)`;
the wiring they used to hold now lives in `src/lib/transact.circom`, and the tables cite that
file as `transact:`.

The correspondence is one row to one Lean field, with three documented exceptions:

* **circomlib gadgets are collapsed, not transcribed.** `Poseidon`, `BabyAdd`, `EscalarMulAny`
  / `EscalarMulFix` and `Pedersen` become opaque Lean functions with axiomatised semantics
  (`Lelantos.Meta.Assumptions`). Their internal constraints have no Lean counterpart. The two
  circomlib templates the model *does* transcribe are `Num2Bits` (`Bits.lean`) and `IsZero` /
  `IsEqual` (`Comparators.lean`), because their soundness is load-bearing.
* **`ValueTimesGen` is split** across two model fields — see its row below.
* **`HashToAssetGen`'s Pedersen is collapsed** into `assetGen` — see its own section below.

Line citations in the Lean sources are the same correspondence at finer grain: every `…Sat`
field's doc comment names the circom lines it mirrors. They are maintained by hand and are
**not** checked by CI, so a source-line drift shows up here as a stale citation rather than a
failing build. Verify them when the circom files move.

### `src/lib/balance.circom`

| circom | Lean |
|---|---|
| `:11` `RangeCheck64` → `Num2Bits(64)` | `RangeCheck64Sat` / `Num2BitsSat` (`Bits.lean`) |
| `:24-40` `ValueTimesGen` = `RangeCheck64` + `ValueScalarMul` | no single definition: the two halves are modelled separately as `TransactSat.pub_in_range` / `pub_in_mul` and `pub_out_range` / `pub_out_mul`. The template has no state of its own, so splitting it is an exact transcription, not a weakening. |
| `:48` `dummy*(dummy-1) === 0` | `DummyZeroValueSat` (first conjunct) |
| `:49` `dummy*value === 0` | `DummyZeroValueSat` (second conjunct) |
| `:109-111` `pub_eq[c] = IsEqual(pa, cand[c])` | `PerAssetValueBalanceSat.pubEq_sat` |
| `:114` `lhs[c][0] <== public_in * pub_eq[c]` | `lhs_chain` initial value |
| `:115` `rhs[c][0] <== public_out * pub_eq[c]` | `rhs_chain` initial value |
| `:118-120` `in_eq[c][i] = IsEqual(in_asset[i], cand[c])` | `inEq_sat` |
| `:121` `in_term[c][i] <== in_value[i] * in_eq[c][i]` | `inTerm_def` |
| `:122` `lhs[c][i+1] <== lhs[c][i] + in_term[c][i]` | `lhs_chain` step |
| `:125-127` `out_eq[c][j] = IsEqual(out_asset[j], cand[c])` | `outEq_sat` |
| `:128` `out_term[c][j] <== out_value[j] * out_eq[c][j]` | `outTerm_def` |
| `:129` `rhs[c][j+1] <== rhs[c][j] + out_term[c][j]` | `rhs_chain` step |
| `:132` `lhs[c][N_IN] === rhs[c][N_OUT]` | `balanced` |
| `:92-98` `cand[]` fill | `candAt` |
| `:186-187` point equality | `PerAssetPointBalanceSat` (`PointBalance.lean`) |

### `src/lib/asset_gen.circom`

`HashToAssetGen` is the one template whose body is **not** transcribed constraint-for-constraint.
Its `Num2Bits` is; its Pedersen is collapsed into an opaque function plus an axiom.

| circom | Lean |
|---|---|
| `:15-16` `Num2Bits(64)(asset_id)` | `Num2BitsSat 64` — `SpentNoteSat.asset_bits`, `OutputNoteSat.asset_bits`, `TransactSat.pub_asset_range`. This is where every `asset_id < 2^64` in the development comes from. |
| `:20-27` `Pedersen(72)` over `TAG_ASSET ‖ asset_id_LE` | **collapsed**, not transcribed: `Lelantos.assetGen : F → G` (`Jubjub.lean`), an opaque function of the asset id. The 8 constant tag bits and the 64 wired input bits have no Lean counterpart. |
| `:28-29` `gen[0..1] <== p.out[0..1]` | `gen_def : gen = coords (assetGen asset_id)` — `SpentNoteSat`, `OutputNoteSat`, `TransactSat.pub_gen` |

The collapse is safe in the direction that matters. Modelling `assetGen` as opaque means the
proofs may assume **nothing** about it beyond being a subgroup element — strictly weaker than
what the circuit computes, so it is the safe direction of the table above.

The one property the development *does* assume is the axiom `assetMul` (`Jubjub.lean`): every
`assetGen a` is a known multiple of `BASE0`. That is a **weakness** of the circuit, deliberately
imported so `pointBalance_not_sound` can exhibit it, and `assetMul_arith` (`assetMul 1 +
assetMul 3 = 2 · assetMul 2`) is checked against the real gadget at runtime by
`src/test/transact.test.ts:847`. No positive result depends on either.

### `src/lib/common.circom` / `src/lib/merkle.circom`

| circom | Lean |
|---|---|
| `common:16-17` `Num2Bits(2)(path_index)` | `PathIndexSelectorsSat` first conjunct |
| `common:21-26` `bb`, `s[0..3]` | `PathIndexSelectorsSat` remaining conjuncts |
| `merkle:35-64` four slot equations | `MerkleLevel4Sat` `c 0 … c 3` |
| `merkle:66-72` `out = Poseidon(TAG_MERKLE, c0..c3)` | `MerkleLevel4Sat` last conjunct / `merkleNode` |
| `merkle:84-96` level chain | `MerkleRootSat` |
| `merkle:107` `is_dummy*(is_dummy-1) === 0` | `MerkleProofOrDummySat.dummy_bit` |
| `merkle:119` `diff <== root' - root` | `MerkleProofOrDummySat.diff_def` |
| `merkle:120` `(1-is_dummy)*diff === 0` | `MerkleProofOrDummySat.matches_root` |

### `src/lib/insert.circom`

| circom | Lean |
|---|---|
| `:34-35` `PathIndexSelectors(idx_digit)` | `QuaternaryInsertLevelSat.selectors` |
| `:41-43` `c0 = s0·cur + (1-s0)·f[0]` | `QuaternaryInsertLevelSat.c0_def` |
| `:50-53` `c1 = s0·z + s1·cur + (s2+s3)·f[1]` | `QuaternaryInsertLevelSat.c1_def` |
| `:60-63` `c2 = (s0+s1)·z + s2·cur + s3·f[2]` | `QuaternaryInsertLevelSat.c2_def` |
| `:69-71` `c3 = (s0+s1+s2)·z + s3·cur` | `QuaternaryInsertLevelSat.c3_def` |
| `:73-79` `cur_next = Poseidon(TAG_MERKLE, c0..c3)` | `QuaternaryInsertLevelSat.out_def` |
| `:93-95` `frontier_out[0..2]` | `QuaternaryInsertLevelSat.fout0_def` … `fout2_def` |
| `:111` `cur[0] <== leaf` | `QuaternaryInsertSat.base` |
| `:113-125` level chain | `QuaternaryInsertSat.level` |
| `:127` `root <== cur[DEPTH]` | `QuaternaryInsertSat.top` |

The child mux and the frontier mux are transcribed as separate fields on purpose: they differ
at slots 1 and 2 (`(s2+s3)·f[1]` versus `(1-s1)·f[1]`), which the circom comment at `:81-87`
flags. Collapsing them in the model would make a real edit invisible.

### `src/tree_update_batch.circom`

Split across two Lean structures — `BatchChainSat` and `BatchDepositSat` — so that the
append results reach no curve axiom.

| circom | Lean |
|---|---|
| `:79-80` `Num2Bits(COUNT_BITS)(actual_count - 1)` | `BatchChainSat.count_bits` |
| `:85-90` `LessThan(COUNT_BITS+1)(k, actual_count)` | `BatchChainSat.active_def` |
| `:95` `(1-active)*cms === 0` | `BatchChainSat.pad_cm` |
| `:96-97` `(1-active)*cv_dep[0..1] === 0` | `BatchChainSat.pad_cv_x` / `pad_cv_y` |
| `:98-101` `(1-active)*{leaf_asset, leaf_public_in, is_deposit, rcv} === 0` | `BatchChainSat.pad_asset` … `pad_rcv` |
| `:108` `is_deposit*(1-is_deposit) === 0` | `BatchChainSat.deposit_bit` |
| `:109-110` `(1-is_deposit)*{leaf_asset, leaf_public_in} === 0` | `BatchChainSat.spend_zero_asset` / `spend_zero_public_in` |
| `:117-122` `leaf = Poseidon(TAG_LEAF, cm, cv_dep.x, cv_dep.y)` | `BatchChainSat.leaf_def` |
| `:131-133` `BabyCheck(cv_dep.x, cv_dep.y + (1-active))` | **absent** — no curve equation in the model |
| `:145` `active_dep <== active * is_deposit` | `BatchDepositSat.active_dep_def` |
| `:147-148` `HashToAssetGen(leaf_asset)` | `BatchDepositSat.gen_def` |
| `:151-154` `ValueTimesGen(leaf_public_in, gen)` | `BatchDepositSat.public_in_range` + `expected_def` (`ValueCommitSat.value_term`) |
| `:157-158` `MulH(rcv)` | `BatchDepositSat.expected_def` (`ValueCommitSat.blind_term`) |
| `:160-164` `expected = BabyAdd(pub_in_mul, rH)` | `BatchDepositSat.expected_def` (`ValueCommitSat.sum_def`) |
| `:166-167` `active_dep*(cv_dep - expected) === 0` | `BatchDepositSat.deposit_x` / `deposit_y` |
| `:172-184` `FrontierRoot` and `old_root === frontier_root.root` | **absent** — see README |
| `:211-212` `Num2Bits(2·DEPTH)(start_index + k)` | `BatchChainSat.idx_bits` |
| `:214-216` `idx_dig` from the bit pairs | `BatchChainSat.idx_dig` |
| `:219-226` `QuaternaryInsert(DEPTH)` per leaf | `BatchChainSat.insert` |
| `:197-201` `fr[0] <== frontier_in` | `BatchChainSat.fr_base` |
| `:202` `running_root[0] <== old_root` | `BatchChainSat.root_base` |
| `:231-233` frontier mux | `BatchChainSat.fr_mux` |
| `:237-239` root mux | `BatchChainSat.root_mux` |
| `:243` `new_root === running_root[MAX_L]` | `BatchChainSat.new_root_def` |
| `:246-259` `BatchCompress(MAX_L)` | **absent** — `PolyEval` is proved generically; the slot order is pinned by `src/test/tree_update_batch.test.ts` |

Three rows are deliberately empty. `BabyCheck` and `FrontierRoot` are genuine gaps, not
simplifications, and both are listed in the README. `BatchCompress` is covered generically by
`polyEval_sound` / `polyEval_binding`; what Lean does not pin is the *order* of the 100
coefficients, which the TypeScript suite asserts against the circuit's own `y` output.

### `src/lib/note.circom`

| circom | Lean |
|---|---|
| `:14` `ivk = Poseidon(TAG_IVK, nsk)` | `deriveIvk` |
| `:25` `nk = Poseidon(TAG_NK, nsk)` | `deriveNk` |
| `:36` `pk = Poseidon(TAG_PK, ivk)` | `derivePk` |
| `:60` `packed_av <== asset*2^64 + value` | `packAV` |
| `:62-67` `cm = Poseidon(packed_av, pk, rho, rcm)` | `noteCommitment` |
| `:75` `rho = Poseidon(TAG_RHO, nf0, index)` | `deriveRho` |
| `:96` `nf = Poseidon(TAG_NF, nk, rho, cm)` | `nullifierOf` |

### `src/lib/value_commit.circom`

| circom | Lean |
|---|---|
| `:24-38` `ValueScalarMul` | `ValueScalarMulSat` |
| `:41-58` `MulH` (`Num2Bits(253)` + `EscalarMulFix`) | `MulHSat` |
| `:77-124` `ValueCommitPair` — one shared `value·gen`, two blinders | two independent `ValueCommitSat` instances per note slot (same constraint set; see the `Gadgets/ValueCommit.lean` module note) |
| `:143-150` `cv = BabyAdd(vT, rH)` | `ValueCommitSat` third conjunct; opened by `valueCommit_opens` |
| `:167-181` `PointSum` chain | `pointSum` |

### `src/lib/spent.circom` / `src/lib/output.circom`

`SpentNoteSat` and `OutputNoteSat` are named-field structures: one field per circom
constraint, in circom source order, each field's doc comment citing the source line it
mirrors. They can be read side by side with the originals and checked a row at a time.

### `src/lib/poly_eval.circom` / `src/lib/transact.circom`

| circom | Lean |
|---|---|
| `poly_eval:13` `acc[0] <== 0` | `PolyEvalSat` first conjunct |
| `poly_eval:15` Horner step | `PolyEvalSat` second conjunct |
| `poly_eval:17` `y <== acc[N]` | `PolyEvalSat` third conjunct |
| `poly_eval:66-109` coefficient layout | `piSlot` + `slotValue` |
| `poly_eval:109` `coeffs[last] <== out_aux_digest` | `PISlot.auxDigest` / `slotValue .auxDigest` |
| `transact:136` `out_rho[j] === DeriveRho(nf0, j)` | `TransactSat.rho_derived` |
| `transact:150-151` `out_cv_dep === OutputNote.cv_dep` | `TransactSat.cv_dep_bound` |
| `transact:114` `spent[i].root <== merkle_root` | `TransactSat.spent_root` |
| `transact:157-168` public bucket | `pub_gen`, `pub_in_range`, `pub_out_range`, `pub_in_mul`, `pub_out_mul` |

## Defence 2 — witness parity harness

**Not built.** The plan called for a `modelcheck` executable that loads a real circom
witness plus `build/2x2.sym`, checks `TransactSat` evaluates to `true` on it, and compares
every modelled intermediate signal against the circom-computed value at the matching
label; plus a negative pass replaying the ~65 rejecting cases from
[transact.test.ts](../src/test/transact.test.ts) and asserting the model rejects them too.

This is the defence that would catch a model *stronger* than the circuit — the dangerous
direction in the table above. Until it exists, the table and the layout check are the only
evidence, and they are reviewed by eye rather than by machine. Treat the transcription as
unverified in that direction.

## Defence 3 — public-input layout parity

Built and running. The 31-slot ordering exists in four implementations:

1. `src/lib/poly_eval.circom :: TransactCompressN`
2. `contracts/src/lib/PubInputs.sol :: compress(Transact, aux)`
3. `sdk/src/bundle/snark-compression.ts :: flatten`
4. `lean/Lelantos/Circuit/Witness.lean :: piSlot`

Checks, each mechanical:

| Link | Check |
|---|---|
| Lean → `expected/layout-{2x2,2x3,3x3}.txt` | `lean/scripts/dump-layout.sh`, one dump per deployed shape |
| `expected/layout-2x2.txt` → SDK | `src/test/formal/layout_parity.test.ts`, sentinel-per-field so any transposition fails |
| SDK → circuit | existing PolyEval binding cases, `src/test/transact.test.ts:645-729` |

The second and third links exist for the **2x2 shape only**. For `2x3` and `3x3` the chain
stops at the first row: the layout is pinned against Lean, so an accidental change fails CI,
but nothing cross-checks those two against the SDK or the circuit.

The layout is defined once in Lean (`piSlot`) and the value lookup (`slotValue`) is
separate, so the dumped names are derived from the same definition the proofs use rather
than being a second copy of it.
