# `formal/` — Lean 4 soundness proof for `src/2x2.circom`

A machine-checked development for `Transact(10, 2, 2)`, the 2-in/2-out multi-asset
transact circuit. The top-level theorem holds for **any** assignment satisfying the modeled
constraint system, not only those an honest prover produces.

That distinction is the point. The test suite
([transact.test.ts](../src/test/transact.test.ts), [fuzz/](../src/test/fuzz/)) exercises
the honest witness-generation path only; `circom_tester` cannot detect an under-constrained
signal, so that bug class is untested by construction. These proofs quantify over
satisfying assignments instead.

```
cd formal
lake build Lelantos            # the proofs
./scripts/check-axioms.sh      # trusted base matches expected-axioms.txt
./scripts/dump-layout.sh       # public-input layout matches layout-2x2.txt
python3 scripts/check-prime.py # discharge the two arithmetic axioms
```

CI runs all four ([.github/workflows/formal.yml](../.github/workflows/formal.yml)).

## What is proved

| Theorem | Where | Statement |
|---|---|---|
| `transact_sound` | `Transact.lean` | `TransactSat w → TxWellFormed w` — the top-level result |
| `transact2x2_sound` | `Transact.lean` | the same for the deployed `Transact(10,2,2)` instance |
| `perAssetValueBalance_all_assets` | `Gadgets/Balance.lean` | the 5 candidate checks imply conservation for **every** asset id in the field |
| `perAssetValueBalance_nat` | `Gadgets/Balance.lean` | …and as an exact **integer** equation, not a modular one |
| `pointBalance_not_sound` | `Gadgets/PointBalance.lean` | the Edwards point balance is **not** a conservation check at the deployed `(2,2)` shape |
| `polyEval_sound` | `Gadgets/PolyEval.lean` | the Horner chain computes `Σ cₖ zᵏ` |
| `polyEval_binding` | `Gadgets/PolyEval.lean` | distinct coefficient vectors agree on `≤ 29` challenges |
| `spentNote_sound` | `Spent.lean` | a non-dummy slot proves ownership + Merkle membership |
| `merkleProofOrDummy_sound` | `Gadgets/Merkle.lean` | a non-dummy slot's leaf sits under the root |
| `nullifier_binds_cm` † | `Note.lean` | faerie-gold resistance: `cm` is in the nullifier preimage |
| `packAV_inj` | `Note.lean` | `(asset, value)` packing is injective given the range checks |
| `num2Bits_sound` | `Bits.lean` | `2ⁿ ≤ p` makes the decomposition alias-free |
| `pathIndexSelectors_sound` | `Gadgets/Common.lean` | the selector is one-hot at `path_index` |
| `outputNote_cvDep_same_value` | `Output.lean` | `cv` and `cv_dep` open to the note's **own** `value` under its own `V^asset`, differing only in blinding |
| `valueCommit_opens` | `Gadgets/ValueCommit.lean` | `cv = value · V^asset + rcv · H`, where the scalar is the range-checked `value` signal, not an opaque bit array |
| `transactSat_satisfiable` | `Completeness.lean` | the constraint system **is satisfiable** — `transact_sound` is not vacuous |
| `transactSat_spend_satisfiable` | `Completeness.lean` | …and satisfiable by a transaction that actually **moves value** through a non-dummy slot |
| `spentReal_witness` | `Completeness.lean` | `SpentReal` is inhabited, so `spentNote_sound`'s `is_dummy = 0` case is reachable |
| `transactSat_twoAsset_satisfiable` | `Completeness.lean` | …and by one moving **two distinct assets** with a non-zero public input |
| `merkleMember_inj` † | `Gadgets/Merkle.lean` | the root **binds** the leaf at a position |
| `noteCommitment_inj` † | `Note.lean` | `cm` binds all five note fields, given the range checks |
| `noteCommitment_ne_leafHash` † | `Note.lean` | a leaf hash can never be passed off as a note commitment |
| `no_asset_creation` | `Transact.lean` | an asset on no input and not in the public bucket cannot appear on any output |
| `transact_pi_binding` | `Transact.lean` | two transactions with different public inputs share `(z, y)` for at most 29 challenges |
| `transact_pi_binding_slot` | `Transact.lean` | …stated per **named** public input, via `piSlot_slotIndex` |
| `piSlot_slotIndex` | `Witness.lean` | `slotIndex` inverts the coefficient layout, so a named-field difference yields a coefficient index |
| `cross_asset_cancellation_rejected` | `Rejection.lean` | the `V¹ + V³ = 2·V²` attack that the **point** balance accepts is **rejected** by the full system |
| `inflation_rejected` / `mint_from_nothing_rejected` | `Rejection.lean` | no satisfying assignment inflates or mints an asset |
| `slots_inj` | `Gadgets/Merkle.lean` | inserting at a fixed position is injective |
| `merkleNode_inj` / `leafHash_inj` † | `Note.lean` | the supporting injectivity layer |
| `transact_binding` † | `Transact.lean` | `TransactSat w → TxBinding w`: distinct `rho`s, binding membership, binding `cm` |
| `poseidon_not_injective` | `Poseidon.lean` | literal injectivity of Poseidon is **false** — guards against reintroducing it as an axiom |
| `poseidon_collision` | `Poseidon.lean` | …and therefore the † hypothesis below is unsatisfiable |

**† conditional on `¬ PoseidonCollision`, which is unsatisfiable** — see
[What is not proved](#what-is-not-proved). Everything unmarked is unconditional; in
particular `transact_sound` assumes nothing about Poseidon.

### Is the theorem vacuous?

Two questions hide under that word.

**Is the hypothesis satisfiable?** Yes, twice over. `transactSat_satisfiable` constructs the
degenerate-but-legal padding transaction (both inputs dummy, both outputs asset `1` value
`0`). `transactSat_spend_satisfiable` constructs one that actually spends: a non-dummy input
carrying one unit of asset `1`, a real Merkle path, a non-zero scalar multiplication in
`ValueCommit`, and a balance whose sums are not all zero. `transact_wellFormed_witness` and
`transact_wellFormed_spend` run `transact_sound` on them.

Both matter. `A → B` is trivially true when `A` is unsatisfiable, so a modelling slip that
over-constrains the system would fail silently. The spending witness additionally makes
`spentNote_sound` non-vacuous: its hypothesis is `is_dummy = 0`, and until a non-dummy slot
was exhibited (`spentReal_witness`) nothing showed that case was reachable at all.

**Is the axiom set consistent?** Yes, and this is independent of the first question. An
axiom such as `Function.Injective poseidon` is refutable (`List F` infinite, `F` finite), so
it proves `False`, and `False` proves `TxWellFormed w` for every `w` — satisfying or not.
Satisfiability of `TransactSat` is no defence. `poseidon_not_injective` stands as a
machine-checked guard against reintroducing such an axiom; the hash assumption survives only
as the explicit `†` hypothesis.

### The two results worth reading first

**Per-asset conservation** mechanizes the candidate-set argument from
[src/README.md § 6 "Value conservation (binding check)"](../src/README.md).
`PerAssetValueBalance` checks only the five asset ids present in the transaction;
`perAssetValueBalance_all_assets` shows that covers every asset id, and
`perAssetValueBalance_nat` lifts the field equality to `ℕ` via the 64-bit range checks —
the "three summands under `2^66 ≪ p`" argument at
[balance.circom:75-80](../src/lib/balance.circom). Drop a `RangeCheck64` upstream and the
theorem loses its hypothesis, which is exactly the failure that comment warns about.

Both depend on **`p_prime` alone** — no cryptographic assumption. That is what
`PerAssetValueBalance` was written to achieve.

**Both directions of the point-balance warning are now proved.**
`pointBalance_not_sound` exhibits an assignment the Edwards point equation accepts and that
mints value; `cross_asset_cancellation_rejected` shows the *same* asset/value pattern has no
satisfying assignment of the full system. Together they are exactly the claim
`src/lib/balance.circom:34-41` makes in prose.

**Point balance is not sound** turns the prose warning at
[balance.circom:56-62](../src/lib/balance.circom) into a machine-checked fact.
`HashToAssetGen` is a single-segment Pedersen hash, so every asset generator is a known
multiple of one shared base; asset ids 1, 2, 3 land on consecutive multipliers, giving
`V¹ + V³ = 2·V²`. `pointBalance_not_sound` constructs an assignment satisfying the point
equation while minting value. Nothing in the development may derive conservation from that
equation, and now nothing can.

## What is *not* proved

* **Groth16 knowledge soundness.** The theorems concern R1CS satisfaction, not the on-chain
  verifier. Bridging that gap is a separate, much larger development.
* **`tree_update_batch.circom`.** The deposit-binding defences C-1′ and C-1″ live there;
  only the 2x2 half of deposit binding (`outputNote_cvDep_binds`) is covered.
* **Under-constrainedness of the compiled R1CS.** The proofs concern the *modeled* system
  and cannot show the 70k-constraint R1CS has no extra degrees of freedom. Running
  **Picus** or **Ecne** on a fresh `build/2x2.r1cs` answers that question — hours of work,
  not weeks. Recommended.
* **Contract obligations.** Nullifier freshness, `z` being a genuine Fiat-Shamir challenge,
  and the `chain_id` / `recipient_address` checks are recorded in
  `Lelantos.ContractObligations` and assumed by nothing.
* **Anything requiring Poseidon collision resistance** — the `†` rows, i.e. all of
  `TxBinding`: pairwise-distinct output `rho`s, Merkle membership being binding rather than
  merely existential, and `cm` pinning its whole note. These follow from
  `¬ PoseidonCollision`, which `poseidon_collision` shows is unsatisfiable, so read
  literally they are vacuous. The assumption sits in the statement rather than in an axiom
  because the axiom version is refutable and would contaminate every other result; a
  non-vacuous treatment needs a concrete-security formulation with an explicit adversary and
  advantage bound, which is a separate and much larger development. The containment is the
  point: `transact_sound`, conservation, the range checks and `PolyEval` are unaffected.
* **The dangerous direction of transcription error** — see [FIDELITY.md](FIDELITY.md).

## Trusted base

`lake env lean Lelantos/Assumptions.lean` prints it; `scripts/check-axioms.sh` diffs it
against [expected-axioms.txt](expected-axioms.txt), so an axiom cannot appear without
surfacing in review. That check names the headline theorems;
[Lelantos/AxiomGuard.lean](Lelantos/AxiomGuard.lean) covers the other ~75 by walking every
declaration in the namespace at build time, so `lake build` itself fails on an unexpected
axiom or an admitted proof. Per-axiom rationale is in
[Lelantos/Assumptions.lean](Lelantos/Assumptions.lean).

**There is no hash axiom.** [Lelantos/Poseidon.lean](Lelantos/Poseidon.lean) records why
each tempting formulation fails: literal injectivity is refutable and makes the development
prove everything, and a `P ∨ PoseidonCollision` conclusion is discharged by `Or.inr` because
`PoseidonCollision` is itself provable. Collision resistance appears only as an explicit
hypothesis on the `†` theorems.

The two primality axioms (`p_prime`, `ell_prime`) exist only because Mathlib's `norm_num`
extension is trial-division based and cannot certify 254- and 251-bit numbers.
`scripts/check-prime.py` discharges them externally: for `p` it verifies the full
factorization of `p - 1` and exhibits a base of order exactly `p - 1` (a Lucas certificate,
hence a real primality proof), and checks `babyjub_order = 8 · ell` plus every size bound
the proofs consume. For `ell` it runs 64-round Miller-Rabin only — stated plainly in the
script's output rather than dressed up as a certificate.