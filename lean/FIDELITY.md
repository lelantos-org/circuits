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
the two-step commitment, every balance candidate, the coefficient digest and the Horner
evaluation at a nonzero challenge. `Lelantos.transact4x6Sat_satisfiable` does the same at
the shipped `Transact(11, 4, 6)`, and `Lelantos.batchSat_satisfiable`
(`BatchCompleteness.lean`) covers `TreeUpdateBatch`, with a deposit leaf and spend leaves
in one batch.

### The direction the table does not have a column for

The table above classifies a *constraint* as present or absent. It has nothing to say about
how many signals are left **unconstrained**, and that is a distinct failure mode with its
own consequences.

`Lelantos.polyEval_forge` is the statement of it: `PolyEval` is affine in each coefficient
with slope `z ^ k`, and `z` is an input the prover reads before choosing a witness, so a
single coefficient the rest of the system leaves free is one linear equation in one unknown.
Solve it and `y` is whatever the contract asks for, for an unrelated transaction. No
collision, no low-probability event.

An early revision of the circuit compressed 69 coefficients at `Transact(11, 4, 6)`, of
which 23 — the address and chain words, the payload digest and the eighteen FMD clue
fields — were declared, wired into `TransactCompressN`, and read nowhere else. The model
transcribed that faithfully. **By the table, faithful is safe.** It was not.

An exact transcription cannot be caught by a transcription check. What catches this is
asking what fixes the coefficient vector before the challenge, and the answer changed more
than once.

The first change removed the free coefficients: a word the circuit does not constrain is
not a signal and not a coefficient; it is hashed into `z` instead. That left a layout in
which every coefficient was constrained by something, and a slot-by-slot table saying so.

Constrained slot by slot is not enough. Coefficients a prover can each move
*independently* contribute additively to `y`, and forging it becomes a modular k-sum far
below a search of the field. The table had no column for that either. The value
commitments, which were the largest source of separable coefficients and were read by
nothing but the compression, were removed.

The design this development now models does not rest on counting what a prover can move.
Each circuit outputs a `CoeffDigest` of its whole coefficient vector as a second public
signal (`Lelantos.TransactSat.digest_def`, `Lelantos.BatchSat.digest_def`), so the public
signals are `(y, digest, z)`. The contract takes the digest word from calldata, hashes it
into `z` and passes it to the verifier. The witness's coefficient vector is therefore
committed before the challenge exists, and the evaluation is a comparison of two fixed
polynomials at a random point. The digest is not a coefficient and is not evaluated into
`y`. At the shipped shapes: 13 coefficients evaluated and 38 words hashed for transact, 36
evaluated and 37 hashed for the batch.

**What is proved about that argument and what is not** is stated once, in `README.md` under
"Public-input compression", and it matters for fidelity because the unproved part is easy
to mistake for a transcription fact. The theorems are: the public digest is the
`CoeffDigest` of the coefficient vector (`Lelantos.transact_digest_public`,
`Lelantos.batch_digest_public`, unconditional); a vector with that digest is the witness's
vector (`Lelantos.transact_calldata_binding`, `Lelantos.batch_calldata_binding`, under
collision resistance); and two distinct vectors agree on at most `N − 1` challenges
(`Lelantos.polyEval_binding`, unconditional). The step that joins them, from "the digest
binds the vector" and "distinct vectors agree on few challenges" to "no forged calldata
verifies except with negligible probability", is the standard Fiat-Shamir forking /
random-oracle argument. It treats keccak256 as a random oracle, it is prose, and it is not
formalised.

**Adding a public input is therefore a fidelity question with a second half:** transcribe
the constraint, then wire the coefficient in through `prefix` (transact) or `coeffs`
(batch), the one array that feeds both `CoeffDigest` and `PolyEval`, so the digest absorbs
it. If the word is not a signal of the circuit at all, it is a challenge word, not a
coefficient.

Three further consequences are modelled rather than assumed:

* `TransactSat.not_all_dummy` — `MerkleProofOrDummy` skips the root comparison on a dummy
  slot, so with every slot dummy no spend constraint reads `merkleRoot`.
  `TxWellFormed.someRealInput` is what the circuit's `IsEqual` on the dummy count buys.
* `PolyEvalSat.z_nonzero` — at `z = 0` only the first coefficient reaches `y`. The check is
  in the circuit, so it is in the model; `TxWellFormed.challengeNonzero`,
  `batch_challenge_nonzero` and `zero_challenge_rejected` are what it gives. No binding
  result consumes it.
* `ContractObligations.digest_passed_unmodified` is `w.digest = d` — a relation between the
  witness and the calldata digest word, not `True`.
  `ContractObligations.nullifiers_distinct` is stated the same way, over two slots of the
  same witness. The remaining five transact fields are stubs and should be read as claims
  made outside Lean, as should seven of the eight fields of `BatchContractObligations`, the
  same ledger for `tree_update_batch.circom`.

Known deliberate omissions, all in the safe direction of the table above — but see the
section immediately above for why "safe by that table" is not the same as harmless:

* The address words, the intent hash, the FMD clue fields and `out_aux_digest` are not
  signals of `Transact` at all, so the model has no fields for them. They are challenge
  words (`src/README.md § 2a`). That the payload digest is the true hash of the aux calldata
  is checked on-chain and recorded in `ContractObligations.aux_digest_recomputed`.
* `Num2Bits`' and `IsZero`'s `<--` witness hints are not modelled, only the `===`
  constraints beneath them. The hints carry no soundness weight.
* The `prefix[k]`, `dg.in[k]` and `pe.coeffs[k]` wires of `TransactCompressN` are not
  separate model signals. All three are `txCoeffs w k`, which is what the circuit's
  `<==` chain makes them. The same goes for `BatchCompress`'s `coeffs[k]`, `dg.in[k]` and
  `pe.coeffs[k]`, which are `batchCoeffs w k`.
* The compressor's own outputs `pe.y` and `pe.digest` are not separate model signals
  either. `y <== pe.y` and `digest <== pe.digest` make them the circuit's public outputs,
  which are the fields `y` and `digest`.

## Defence 1 — constraint-by-constraint table

Every `===` / `<==` written in `src/lib/*.circom` — the transitive closure of `src/4x6.circom`
and `src/tree_update_batch.circom`, minus `node_modules/circomlib` — appears
in the tables below, with **one** stated exception, repo-owned code that is not
transcribed:

1. `EmptySubtreeHashes` / `EMPTY_SUBTREE` (`src/lib/common.circom`) has no rows. In Lean
   `zeros : ℕ → F` is a free parameter, never tied to the eleven hard-coded constants, and
   the constraint systems accept any fill, which is the safe direction. The batch results,
   however, assume `ZerosCoherent` (`Spec/QuatTree.lean`) — that the fills are the
   empty-subtree chain — for the reason the header of `src/lib/batch_append.circom` gives.
   Lean cannot evaluate Poseidon, so the chain is a hypothesis, not a transcription;
   `test/gadgets/merkle.test.ts` pins the constants to it numerically, and
   `ZerosCoherent.eq_emptyChain` shows the hypothesis determines the table.

There used to be a second: a fixed-base scalar multiplication collapsed into an axiom pair.
It went with the value commitments, and with it the last gadget whose semantics were
assumed rather than transcribed.

See "What is not proved" in [README.md](README.md). `src/4x6.circom` is the only transact
top-level the repository ships, instantiating `Transact(11, 4, 6)`; the smaller shapes that
appear in `Proofs/Completeness.lean` are witness constructions, not circuits. The shared
wiring lives in `src/lib/transact.circom`, which the tables cite as `transact:`.

The correspondence is one row to one Lean field, with one documented exception:

* **circomlib gadgets are collapsed or re-transcribed, not cited.** `Poseidon` becomes an
  opaque Lean function, with no axiom about it; its internal constraints have no Lean
  counterpart. `Num2Bits` (`Bits.lean`) and `IsZero` / `IsEqual` / `LessThan`
  (`Comparators.lean`) are transcribed from circomlib, because their soundness is
  load-bearing. No other circomlib template is in either circuit.

Line citations in the Lean sources are the same correspondence at finer grain: every `…Sat`
field's doc comment names the circom lines it mirrors. `lean/scripts/check-citations.py` (run by
`check-all.sh`) resolves each one, so a citation into a deleted file or past the end of a
surviving one is a build failure. A bare `:lo-hi` resolves against the last path named in
the same file — with a line number, or in a markdown heading, which is how the tables here
are anchored. Anchoring on headings matters: without it the rows under a heading resolve
against whatever file some earlier prose happened to name, or, before any full citation
appears in the file, against nothing at all, and are silently skipped. Both happened.

The checker also **anchors**: where the doc comment quotes something in backticks that is
also vocabulary of the cited file — `` `acc[0] <== 0` ``, `` `NoteCommitment` ``,
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
and says how many rather than failing on how the tree was cloned. The ones that exist
today — mostly the `MASP.sol` checks the two obligation ledgers name — are checked locally,
against whatever revision of the sibling repository is checked out there, which is where a
`PubInputs.sol` citation aimed at `src/lib/` rather than `src/libs/` was caught. (Naming the
wrong path in full here would itself be a citation, and this check would fail on the
sentence describing it.) They are the citations most likely to be stale: the contract moves
on its own schedule, and it has not yet been moved to the layouts modelled here.

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
| `:11-15` `RangeCheck64` → `Num2Bits(64)` | `RangeCheck64Sat` / `Num2BitsSat` (`Bits.lean`). The template has no `bits` output; the model's bit array is the internal `n2b.out` |
| `:22` `dummy*(dummy-1) === 0` | `DummyZeroValueSat` (first conjunct) |
| `:23` `dummy*value === 0` | `DummyZeroValueSat` (second conjunct) |
| `:57-65` `cand[]` fill | `candAt` |
| `:76-78` `pub_eq[c] = IsEqual(pa, cand[c])` | `PerAssetValueBalanceSat.pubEq_sat` |
| `:81` `lhs[c][0] <== 0` | `lhs_chain` initial value. There is no public-input term |
| `:82` `rhs[c][0] <== public_out * pub_eq[c]` | `rhs_chain` initial value |
| `:85-87` `in_eq[c][i] = IsEqual(in_asset[i], cand[c])` | `inEq_sat` |
| `:88` `in_term[c][i] <== in_value[i] * in_eq[c][i]` | `inTerm_def` |
| `:89` `lhs[c][i+1] <== lhs[c][i] + in_term[c][i]` | `lhs_chain` step |
| `:92-94` `out_eq[c][j] = IsEqual(out_asset[j], cand[c])` | `outEq_sat` |
| `:95` `out_term[c][j] <== out_value[j] * out_eq[c][j]` | `outTerm_def` |
| `:96` `rhs[c][j+1] <== rhs[c][j] + out_term[c][j]` | `rhs_chain` step |
| `:99` `lhs[c][N_IN] === rhs[c][N_OUT]` | `balanced` |

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
| `:115` `assert(EMPTY_SUBTREE(0) == 0)` | `ZerosCoherent`, first conjunct — a hypothesis, see exception 1 |
| `:119` `assert(MAX_L <= 4 ** DEPTH)` | none needed — a compile-time guard on the shape. No result uses it: `batchAppend_capacity` bounds the run by the tree from the `last_idx_bits` range check at any `MAX_L` |
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

One Lean structure, `BatchSat`, in source order. `EMPTY_SUBTREE` is a parameter of the
constraint system, not a signal, so it is an argument of `BatchSat` rather than a field of
`BatchSignals`.

| circom | Lean |
|---|---|
| `:126` `is_deposit*(1-is_deposit) === 0` | `BatchSat.deposit_bit` |
| `:127` `(1-is_deposit)*leaf_asset === 0` | `BatchSat.spend_zero_asset` |
| `:128` `(1-is_deposit)*leaf_public_in === 0` | `BatchSat.spend_zero_public_in` |
| `:143-144` `rng_asset = RangeCheck64(leaf_asset)` | `BatchSat.asset_range` |
| `:146-147` `rng_public_in = RangeCheck64(leaf_public_in)` | `BatchSat.public_in_range` |
| `:149-152` `dep_cm = NoteCommitment(leaf_asset, leaf_public_in, cms)` | `BatchSat.dep_cm_def`, with `cms[k]` in the `inner` position |
| `:154` `dep_delta <== is_deposit * (dep_cm.cm - cms)` | `BatchSat.dep_delta_def` |
| `:155` `leaves <== cms + dep_delta` | `BatchSat.leaf_def` |
| `:161-171` `BatchAppend(DEPTH, MAX_L)` over `start_index`, `actual_count`, `leaves`, `frontier_in` | `BatchSat.append` |
| `:172` `old_root === append.old_root` | `BatchSat.old_root_def` |
| `:173` `new_root === append.new_root` | `BatchSat.new_root_def` |
| `:178` `(1-append.active)*cms === 0` | `BatchSat.pad_cm` |
| `:179-181` `(1-append.active)*{leaf_asset, leaf_public_in, is_deposit} === 0` | `BatchSat.pad_asset` … `pad_is_deposit` |
| `:193-194` `leaf_asset_z = IsZero(leaf_asset)` | `BatchSat.asset_isZero` |
| `:195` step 5 `leaf_asset_z.out * leaf_public_in === 0` | `BatchSat.no_value_under_zero` |
| `:199-211` `pe = BatchCompress(MAX_L)`, its wiring, and `y <== pe.y` | `BatchSat.compress`, a `PolyEvalSat` over `batchCoeffs`. The coefficient order is `batchPiSlot` / `batchSlotValue`, dumped to `expected/layout-batch-8.txt` by `dump-layout.sh` |
| `:212` `digest <== pe.digest` | `BatchSat.digest_def`, a `CoeffDigestSat` over the same `batchCoeffs` |

Two things the previous revision's table had and this one does not: a row marked **absent**
for a curve-membership check the model could not express, and a split into two structures.
Both existed because of the deposit value commitment. The deposit binding is a hash now,
transcribed in full by `dep_cm_def`, `dep_delta_def` and `leaf_def`.

The guard at `:195` is ungated. It reads `IsZero(leaf_asset).out * leaf_public_in === 0` on
every slot, active or not, deposit or not; `spend_zero_public_in` and `pad_public_in` are
what make it vacuous off the deposit slots. The model states it ungated too. Gating it in
the model would add a hypothesis the circuit does not have.

`BatchCompress` used to be outside the constraint system: its Horner chain was covered
generically and its order by `batchPiSlot`, but `BatchSat` had no field for it and
`BatchSignals` carried neither `z` nor `y`. It is `BatchSat.compress` now, so the batch's
`z != 0` and `y` are modelled like the transact circuit's, and `BatchSat.digest_def` is the
digest public output over the same 36 words. The slot *order* is anchored on Lean:
`batchPiSlot` → `expected/layout-batch-8.txt` →
`test/formal/batch_layout_parity.test.ts` → the published vector. All 36 words are
coefficients. The digest is not one of them and has no line in the dump.

### `src/lib/note.circom`

| circom | Lean |
|---|---|
| `:19-29` `ivk = Poseidon(TAG_IVK, nsk)` | `deriveIvk` |
| `:31-40` `nk = Poseidon(TAG_NK, nsk)` | `deriveNk` |
| `:42-51` `pk = Poseidon(TAG_PK, ivk)` | `derivePk` |
| `:62-75` `inner = Poseidon(TAG_INNER, owner_pk, rho, rcm)` | `noteInner` |
| `:93` `packed_av <== asset*2^64 + value` | `packAV` |
| `:95-100` `cm = Poseidon(TAG_CM, packed_av, inner)` | `noteCommitment` |
| `:108-119` `rho = Poseidon(TAG_RHO, nf0, index)` | `deriveRho` |
| `:133-146` `nf = Poseidon(TAG_NF, nk, rho, cm)` | `nullifierOf` |

`noteCommitment` takes an `inner`, not `(pk, rho, rcm)`, because that is the template's
interface and `tree_update_batch.circom` instantiates it with a word that is not computed
in-circuit. `noteCm` is the composition the two slot templates wire.

### `src/lib/spent.circom`

`SpentNoteSat` is a named-field structure: one field per circom constraint, in circom source
order, each field's doc comment citing the source line it mirrors.

| circom | Lean |
|---|---|
| `:38-39` `ivk_d = DeriveIvk(nsk)` | `SpentNoteSat.ivk_def` |
| `:41-42` `pk_check = DerivePk(ivk)` | `SpentNoteSat.pk_derived` |
| `:43` `(1 - is_dummy) * (pk_check.pk - pk) === 0` | `SpentNoteSat.owns` |
| `:47-48` `rng_value = RangeCheck64(value)` | `SpentNoteSat.value_range` |
| `:50-51` `rng_asset = RangeCheck64(asset_id)` | `SpentNoteSat.asset_range` |
| `:54-57` `inner = NoteInner(pk, rho, rcm)` | `SpentNoteSat.inner_def` |
| `:59-62` `cm = NoteCommitment(asset_id, value, inner)` | `SpentNoteSat.cm_def` |
| `:65-74` `mp = MerkleProofOrDummy(DEPTH)`, with the commitment as its `leaf` | `SpentNoteSat.membership` |
| `:78-79` `nk_d = DeriveNk(nsk)` | `SpentNoteSat.nk_def` |
| `:81-85` `nf_h.nf === nullifier` | `SpentNoteSat.nf_def` |
| `:89-90` `asset_nz = IsZero(asset_id)` | `SpentNoteSat.asset_isZero` |
| `:91` `(1 - is_dummy) * asset_nz.out === 0` | `SpentNoteSat.asset_nonzero_real` |

### `src/lib/output.circom`

| circom | Lean |
|---|---|
| `:24-25` `rng_value = RangeCheck64(value)` | `OutputNoteSat.value_range` |
| `:27-28` `rng_asset = RangeCheck64(asset_id)` | `OutputNoteSat.asset_range` |
| `:31-32` `asset_nz = IsZero(asset_id)` | `OutputNoteSat.asset_isZero` |
| `:33` `asset_nz.out === 0` | `OutputNoteSat.asset_nonzero` |
| `:36-39` `inner = NoteInner(pk, rho, rcm)` | `OutputNoteSat.inner_def` |
| `:41-45` `cm_h.cm === cm` | `OutputNoteSat.cm_def` |

### `src/lib/poly_eval.circom`

| circom | Lean |
|---|---|
| `:35-36` `z_nz = IsZero(z)` | `PolyEvalSat.z_isZero` |
| `:37` `z_nz.out === 0` | `PolyEvalSat.z_nonzero` |
| `:40` `acc[0] <== 0` | `PolyEvalSat.base` |
| `:41-43` Horner step | `PolyEvalSat.step` |
| `:44` `y <== acc[N]` | `PolyEvalSat.result` |
| `:68-84` `h[b] = Poseidon(5)`, tag or previous output, four words zero-padded | `CoeffDigestSat.block_zero` / `block_succ`, over `padded` |
| `:85` `out <== h[BLOCKS - 1].out` | `CoeffDigestSat.out_def` |
| `:151-163` `prefix[]` fill | `piSlot` + `slotValue` |
| `:165-169` `dg = CoeffDigest(N)` over `prefix`, `digest <== dg.out` | `TransactSat.digest_def` |
| `:171-176` `pe = PolyEval(N)` over `prefix`, `y <== pe.y` | `TransactSat.compress`, over `txCoeffs` |
| `:216-219` `coeffs[0..3]`, the four scalar words | `batchPiSlot` + `batchSlotValue`, indices `0..3` |
| `:221-236` `cms`, `leaf_asset`, `leaf_public_in`, `is_deposit` blocks | `batchPiSlot` + `batchSlotValue`, the four per-slot arrays |
| `:238-242` `dg = CoeffDigest(N)` over `coeffs`, `digest <== dg.out` | `BatchSat.digest_def` |
| `:244-249` `pe = PolyEval(N)` over `coeffs`, `y <== pe.y` | `BatchSat.compress` |
| — the digest is a public output, not a coefficient | **absent by design** — no `PISlot` or `BatchPISlot` constructor; it is the field `digest` of the witness, constrained by `digest_def` |
| — the address words, clue fields and payload digest are not coefficients | **absent by design** — no `PISlot` constructor; they are challenge words, see § "The direction the table does not have a column for" |

### `src/lib/transact.circom`

| circom | Lean |
|---|---|
| `:76-91` `spent[i] = SpentNote(DEPTH)` and its wiring | `TransactSat.spent_sat` |
| `:90` `spent[i].root <== merkle_root` | `TransactSat.spent_root` |
| `:94-95` `in_dz` wiring | `TransactSat.dummy_zero` |
| `:111` `dummy_acc[0] <== 0` | `TransactSat.dummy_acc_base` |
| `:112-114` `dummy_acc[i + 1] <== dummy_acc[i] + in_is_dummy[i]` | `TransactSat.dummy_acc_step` |
| `:115-117` `all_dummy = IsEqual(dummy_acc[N_IN], N_IN)` | `TransactSat.dummy_all_eq` |
| `:118` `all_dummy.out === 0` | `TransactSat.not_all_dummy` |
| `:127-130` `out_rho[j] === DeriveRho(nullifier[0], j)` | `TransactSat.rho_derived` |
| `:132-138` `out_note[j] = OutputNote()` and its wiring | `TransactSat.out_sat` |
| `:144-145` `rng_pub_asset = RangeCheck64(public_asset_id)` | `TransactSat.pub_asset_range` |
| `:147-148` `rng_pub_out = RangeCheck64(public_out)` | `TransactSat.pub_out_range` |
| `:158-159` `pub_out_z = IsZero(public_out)` | `TransactSat.pub_out_isZero` |
| `:160` `pub_out_z.out * public_asset_id === 0` | `TransactSat.transfer_names_no_asset` |
| `:163-173` `vbal = PerAssetValueBalance(N_IN, N_OUT)` and its wiring | `TransactSat.value_balance` |
| `:176-187` `pe = TransactCompressN(N_IN, N_OUT)`, its wiring, and `y <== pe.y` | `TransactSat.compress` |
| `:188` `digest <== pe.digest` | `TransactSat.digest_def` |

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
obvious. The first is that **`TransactSat` is not executable**: `poseidon` is opaque, so
there is nothing to run. The resolution is not to make it computable but to split every
field in two — the arithmetic ones (`dummy_zero`, `count_bits`, the balance chains, the
muxes, `Num2BitsSat`, `PolyEvalSat`) evaluate directly, and the hash ones do not evaluate at
all. For those, what the model claims is a *wiring* fact: that `cm_def`'s arguments are the
values on `main.spent[0].cm.h.inputs[0..2]` and its result is the value on `.out`. That is
checkable, and it is the whole transcription content of an equation over an opaque
function. With the curve gadgets gone, Poseidon is the only opaque function left.

The second is that an executable mirror nobody proved equivalent is a third copy of the
model, free to drift from the one the theorems are about. `transactSatB : TxWitness → Bool`
needs `transactSatB w = true → TransactSat w` alongside it, or the harness checks something
other than what is proved.

Its prerequisite now exists: Defence 5 is the signal map such a harness needs in order to
read a witness vector into a `TxWitness` at all.

## Defence 3 — public-input layout parity

Built and running, for both circuits. The transact 13-slot ordering exists in four
implementations:

1. `src/lib/poly_eval.circom :: TransactCompressN`
2. `contracts/src/libs/PubInputs.sol :: compress(Transact, aux)`
3. `test/ref/compress.ts :: coeffs`
4. `lean/Lelantos/Circuit/Layout.lean :: piSlot`

Checks, each mechanical:

| Link | Check |
|---|---|
| Lean → `expected/layout-4x6.txt` | `lean/scripts/dump-layout.sh` |
| `expected/layout-4x6.txt` → SDK | `test/formal/layout_parity.test.ts`, sentinel-per-field so any transposition fails |
| SDK → circuit | existing PolyEval binding cases, `test/transact/binding.test.ts` |

The sentinel-per-field table in the second row is hand-written and is what catches a
transposition between two slots of the same type. `PubInputs.sol` has not been moved to the
13-coefficient layout, so the chain currently ends at the published vector rather than at
the contract.

The digest is not in the dump: the dump lists coefficients, and the digest is a public
output computed over them. That it is the fold of these thirteen, in this order, is
`TransactSat.digest_def`, and its agreement with the SDK's fold is the business of the
circuit suites, not of this file. The order of the three public signals, `(y, digest, z)`,
is checked against the compiled circuits by `test/formal/pubsignal_order.test.ts`; the
model has no notion of signal order.

The batch has the same chain. `Lelantos.batchPiSlot` →
`lean/expected/layout-batch-8.txt` (`dump-layout.sh`) → `vectors/tree-update-batch-8.json`
(`test/formal/batch_layout_parity.test.ts`) → the SDK and the contracts fixture, which read
that vector. All 36 batch words are coefficients, unlike transact's 13-of-38, because every
one of them is a signal of `tree_update_batch.circom`: a signal that was hashed into `z`
but neither evaluated nor digested would not be tied to the calldata it was hashed from.
The batch's 37th hashed word is its digest.

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

261 of 262 constraints are transcribed. The residue is pinned in `expected/coverage.txt` and
diffed the way `check-axioms.sh` pins the trusted base, so a new uncited constraint appears
in review rather than in nobody's eye. It is *exactly* the one exception Defence 1 states,
`EmptySubtreeHashes`, and nothing is pointer-only. Two lines of `MerkleRoot`'s level loop
were pinned as pointer-only for a while; they were a citation three lines out, not wiring
the model lacks. There were three exceptions while the old root lived in an
unmodelled template and a fixed-base multiplication sat behind an axiom; both are gone.

The count is smaller than it was (431) because the circuit is: the value commitments, the
point balance and the fixed-base multiplication accounted for the difference. The fraction
is higher partly for the same reason and partly because `BatchCompress` and the transact
wiring blocks are now cited at the width of the block a model field abstracts rather than
at the width of the template.

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
  goes for `out_note[].asset_nz.out` (`asset_nz.out === 0`), for `pe.pe.z_nz.out`
  (`z_nz.out === 0`, the nonzero challenge), for the last `CoeffDigest` block's output in
  both circuits, which is gone because it is the public `digest`, for the top of the `rhs`
  accumulator, which
  is gone only because `lhs[c][N_IN] === rhs[c][N_OUT]` merges it away, and for the base
  of the `lhs` accumulator, which is gone because `lhs[c][0] <== 0`: if a public input term
  were ever added back to the input side, it would reappear.
* **It is the input Defence 2 needs.** A witness harness has to turn a flat witness vector
  into a `TxWitness`; this is the map that does it.

What Defence 5 does **not** check is that a field mirrors the *right* signal. A field
pointed at a real but wrong signal passes. That is Defence 2's job.

