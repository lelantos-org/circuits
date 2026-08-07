# Fidelity: does the Lean model match the circuit?

The proofs in `formal/` are about `Lelantos.TransactSat`, a hand-written Lean model. They
are only worth something if that model faithfully mirrors `src/2x2.circom`. This file is
the argument that it does, and — just as importantly — the honest list of where the
argument is still thin.

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

Known deliberate omissions, all in the safe direction:

* `PerAssetPointBalance` **is** modelled (`TransactSat.point_balance`) but nothing is
  derived from it, because `pointBalance_not_sound` proves nothing can be. `point_pub_in`
  and `point_pub_out` tie the group-level `pubInG` / `pubOutG` to the `pub_in_mul` /
  `pub_out_mul` signals; without them those two are free variables and the point equation
  is satisfiable for any assignment by solving for `pubOutG`.
* The FMD clue fields carry no constraint beyond `PolyEval` inclusion — that is the
  circuit's actual behaviour (`src/README.md § 1 "FMD clue binding"`), not a modelling shortcut.
* `Num2Bits`' `<--` witness hints are not modelled, only the `===` constraints beneath
  them. That is exactly right: the hints carry no soundness weight.

## Defence 1 — constraint-by-constraint table

Every `===` / `<==` in the transitive closure of `src/2x2.circom` appears exactly once.
`2x2.circom` itself only instantiates `Transact(10, 2, 2)`; the wiring it used to hold now
lives in `src/lib/transact.circom`, and the tables below cite that file as `transact:`.

### `src/lib/balance.circom`

| circom | Lean |
|---|---|
| `:11` `RangeCheck64` → `Num2Bits(64)` | `RangeCheck64Sat` / `Num2BitsSat` (`Bits.lean`) |
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

### `src/lib/common.circom` / `src/lib/merkle.circom`

| circom | Lean |
|---|---|
| `common:16-17` `Num2Bits(2)(path_index)` | `PathIndexSelectorsSat` first conjunct |
| `common:21-26` `bb`, `s[0..3]` | `PathIndexSelectorsSat` remaining conjuncts |
| `merkle:35-64` four slot equations | `MerkleLevel4Sat` `c 0 … c 3` |
| `merkle:66-72` `out = Poseidon(TAG_MERKLE, c0..c3)` | `MerkleLevel4Sat` last conjunct / `merkleNode` |
| `merkle:87-96` level chain | `MerkleRootSat` |
| `merkle:107` `is_dummy*(is_dummy-1) === 0` | `MerkleProofOrDummySat.1` |
| `merkle:119` `diff <== root' - root` | `MerkleProofOrDummySat.2.2.1` |
| `merkle:120` `(1-is_dummy)*diff === 0` | `MerkleProofOrDummySat.2.2.2` |

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
| `:78-85` `cv = BabyAdd(vT, rH)` | `ValueCommitSat` third conjunct; opened by `valueCommit_opens` |
| `:102-116` `PointSum` chain | `pointSum` |

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
| `poly_eval:57-96` coefficient layout | `piSlot` + `slotValue` |
| `transact:129` `out_rho[j] === DeriveRho(nf0, j)` | `TransactSat.rho_derived` |
| `transact:143-144` `out_cv_dep === OutputNote.cv_dep` | `TransactSat.cv_dep_bound` |
| `transact:107` `spent[i].root <== merkle_root` | `TransactSat.spent_root` |
| `transact:150-161` public bucket | `pub_gen`, `pub_in_range`, `pub_out_range`, `pub_in_mul`, `pub_out_mul` |

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

Built and running. The 30-slot ordering exists in four implementations:

1. `src/lib/poly_eval.circom :: TransactCompressN`
2. `contracts/src/lib/PubInputs.sol :: compress(Transact, aux)`
3. `sdk/src/bundle/snark-compression.ts :: flatten`
4. `formal/Lelantos/Transact.lean :: piSlot`

Checks, each mechanical:

| Link | Check |
|---|---|
| Lean → `layout-2x2.txt` | `formal/scripts/dump-layout.sh` |
| `layout-2x2.txt` → SDK | `src/test/formal/layout_parity.test.ts`, sentinel-per-field so any transposition fails |
| SDK → circuit | existing PolyEval binding cases, `src/test/transact.test.ts:645-729` |

The layout is defined once in Lean (`piSlot`) and the value lookup (`slotValue`) is
separate, so the dumped names are derived from the same definition the proofs use rather
than being a second copy of it.
