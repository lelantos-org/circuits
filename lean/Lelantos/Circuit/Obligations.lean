import Lelantos.Circuit.Layout
import Lelantos.Circuit.BatchLayout

/-!
# What the contracts must check

The checks both circuits leave to their verifier: one structure per circuit, one field per
check. Nothing in the development assumes any field of either.

A field is either stated — a relation between objects this development has, which the
contract is claimed to establish — or a stub, `True`, naming a check whose subject (a
nullifier set, an EVM `block.chainid`, a keccak preimage, the live accumulator, an escrow
digest) has no counterpart here. A stub states no property; it is a claim made outside
Lean. A stated field is an assumption, not a result.

## The three conditions the compression needs

Both circuits output `(y, digest, z)`, and both ledgers carry the same three conditions on
the consumer (`src/lib/poly_eval.circom:92-95`). `d` is the digest word in calldata:

1. `d` is passed to the verifier unmodified, as the `digest` public signal;
2. `d` is in the keccak preimage of `z`;
3. every coefficient is in the keccak preimage of `z`.

`d` is not a coefficient: the contract does not evaluate it into `y`, and it never
recomputes it.

The first is stated, as `w.digest = d` for the witness the accepted proof attests. The
other two are stubs. With them, with Poseidon collision resistance and with keccak256 as a
random oracle, the Fiat-Shamir argument concludes that the calldata coefficients are the
witness's coefficients except with probability at most `(N − 1)/r`. That conclusion is not
a field of either ledger and is not a theorem (`Lelantos.Circuit.Transact`, "Why the
compression binds").
-/

namespace Lelantos

variable {depth nIn nOut : ℕ}

/-! ## `src/4x6.circom` -/

/-- What `Transact(depth, nIn, nOut)` leaves to `MASP.sol`. `d` is the digest word the
contract read from calldata; `w` is the witness the accepted proof attests.

`nullifiers_distinct` and `digest_passed_unmodified` are stated; the other five are
stubs. -/
structure ContractObligations (d : F) (w : TxWitness depth nIn nOut) : Prop where
  /-- `nullifier[i]` is unspent. A stub: it concerns the nullifiers every earlier
  transaction published. Distinctness within this transaction is `nullifiers_distinct`.
  This also makes `rho` derivation collision-free across transactions, since `DeriveRho`
  anchors on `nullifier[0]`. -/
  nullifiers_fresh : True
  /-- No two input slots carry the same nullifier.

  Each slot is opened against the shared root on its own, so nothing in `Transact` stops
  one note filling two of them: the duplicate satisfies every constraint, and
  `PerAssetValueBalance` counts its value once per slot, so the spender draws twice what
  the note holds. `src/4x6.circom:47-49` names the check as the consumer's;
  `contracts/src/MASP.sol:1076-1080` is it: a pairwise scan, `DuplicateNullifier` on a hit.

  The contract compares the calldata copies. The nullifier slots are coefficients
  (`PISlot.nullifier`), so the binding argument in the module note covers them.

  The range is every slot, dummies included. `is_dummy` is private, so the contract cannot
  tell the slots apart, and `MASP._consumeNullifier` at `contracts/src/MASP.sol:1053-1055`
  runs over all of them. A dummy slot's nullifier is over a note the prover chose freely,
  so distinctness is a constraint on the prover. -/
  nullifiers_distinct : ∀ a b, a < nIn → b < nIn → a ≠ b →
    (w.spent a).nullifier ≠ (w.spent b).nullifier
  /-- Condition 1: the calldata digest word is the `digest` public signal. The contract
  takes `d` from calldata and passes it to the verifier unmodified, in the public signals
  `(y, d, z)`, so for the witness an accepted proof attests the public output `digest` is
  `d`. With `transact_digest_public` it gives
  `d = coeffDigest (txCoeffs w) (piCount nIn nOut)`. -/
  digest_passed_unmodified : w.digest = d
  /-- Condition 2: the digest word is in the keccak preimage of `z`. The contract hashes
  `d` into the challenge, after the coefficients and before the challenge-only words
  (`src/4x6.circom:14-27`). Left out, the prover can choose the witness, and so `d`, after
  seeing `z`, and the count in `polyEval_binding` bounds nothing. A stub: the keccak
  preimage has no counterpart here. -/
  digest_in_challenge : True
  /-- Condition 3: every coefficient is in the keccak preimage of `z`: the 13 calldata
  coefficients at the deployed shape, in layout order. The preimage is 38 words: these 13,
  the digest word, and the 24 challenge-only words (addresses, chain id, intent hash, FMD
  clues, payload digest), which are hashed but are not signals of the circuit. A stub. -/
  coefficients_in_challenge : True
  /-- `chain_id = block.chainid` and `recipient_address < 2^160`.

  Neither word is a signal of the circuit; both reach the proof only through the
  challenge. -/
  address_and_chain_checked : True
  /-- `out_aux_digest` is recomputed from the `aux` calldata, not taken from it. The
  challenge binds whatever value the prover supplied; only this check ties that value to
  the encrypted-note payload the recipient receives. Without it a relayer could keep the
  challenge-bound clue intact while corrupting `ephPub` and the ciphertext, leaving a note
  that cannot be opened after its inputs are spent. -/
  aux_digest_recomputed : True

/-! ## `src/tree_update_batch.circom`

`old_root`, `start_index` and `actual_count` are inputs of the batch, so every result in
`Lelantos.Circuit.TreeUpdateBatch` is conditional on them: a proof over a stale root or a
wrong start position is as valid as one over the live tree. Likewise `batch_deposit_leaf`
says a deposit slot's leaf is the commitment of its declared `(leaf_asset, leaf_public_in)`
and the published `inner`, not that those are the asset and amount anybody escrowed, nor
that the slot should have been a deposit slot.
-/

/-- What `TreeUpdateBatch(depth, maxL)` leaves to `MASP.sol`
(`src/tree_update_batch.circom:55-75`). `d` is the digest word the contract read from
calldata; `w` is the witness the accepted proof attests.

`digest_passed_unmodified` is stated; the other seven are stubs. Unlike the transact
layout, all `4 + 4·MAX_L` words are coefficients: there are no challenge-only words, and
the challenge preimage is the 36 coefficients and the digest word, 37 words at
`MAX_L = 8`. -/
structure BatchContractObligations {depth maxL : ℕ} (d : F)
    (w : BatchSignals depth maxL) : Prop where
  /-- Condition 1: the calldata digest word is the `digest` public signal, the transact
  obligation of the same name. The verification at `contracts/src/MASP.sol:733-735` is
  against values the contract takes from its own calldata. With `batch_digest_public` this
  field gives `d = coeffDigest (batchCoeffs w) (batchPiCount maxL)`.

  `new_root` cannot serve instead: it is not injective in the coefficients, since a zero
  leaf is the empty leaf. -/
  digest_passed_unmodified : w.digest = d
  /-- Condition 2: the digest word is in the keccak preimage of `z`, hashed after the
  coefficients (`src/tree_update_batch.circom:47-50`). It is not evaluated into `y`. A
  stub. -/
  digest_in_challenge : True
  /-- Condition 3: every coefficient is in the keccak preimage of `z`. All 36 words at
  `MAX_L = 8`. A stub. -/
  coefficients_in_challenge : True
  /-- `old_root` is the tree's live root, not some root it once had —
  `MASP._requireTreePosition` at `contracts/src/MASP.sol:754-755`, and on the spend path
  `currentRoot()` fed into the proof image at `contracts/src/MASP.sol:1051-1052` instead.
  Without it `batch_advances_by_count` advances a tree nobody is keeping. -/
  old_root_is_live : True
  /-- `start_index` is the number of leaves already committed, so the batch appends at the
  frontier rather than overwriting (`contracts/src/MASP.sol:757`, reverting with
  `BatchMisaligned`). `batch_capacity` bounds `start_index + actual_count` by the tree's
  size; it says nothing about where the tree currently ends. -/
  start_index_is_committed_count : True
  /-- `actual_count` is the number of leaves the payload actually carries — two per deposit
  on the flush path (`contracts/src/MASP.sol:743-747`, `MASP._validateBatchHeader`), the
  fixed output count on the spend path. `batch_active_spec` makes the active run a prefix of
  that length, so an unchecked `actual_count` would commit padding as leaves or silently
  drop a deposit. -/
  count_matches_payload : True
  /-- `is_deposit[k]` is pinned per active slot, not taken from the relayer: 1 on every
  leaf of a deposit batch, 0 on every leaf of a spend batch
  (`src/tree_update_batch.circom:67-73`). The circuit constrains it only to be boolean, and
  it selects how `cms[k]` becomes a leaf (`batch_deposit_leaf`, `batch_spend_leaf`). Both
  mistakes verify:

  * cleared on a deposit leaf, the depositor's word is inserted as it stands, so a
    depositor who escrowed a commitment of its choosing in place of `inner` holds a note of
    any value for a one-unit deposit;
  * set on a spend leaf, the leaf is the hash of `out_cm` under
    `(leaf_asset, leaf_public_in)`. It has no opening as a note, so the spend's outputs are
    burned. -/
  is_deposit_pinned : True
  /-- Each active deposit leaf is the one its escrow record describes: `cms` (the
  depositor's `inner`), `leaf_asset` and `leaf_public_in` are checked against the digest
  stored at submit, and the record is deleted, so one escrow funds one leaf —
  `DepositNotPending` … `BadDepositMode` at `contracts/src/MASP.sol:779-790`, then the
  `escrowed` entry dropped at `contracts/src/MASP.sol:850`. On the spend path `cms` is
  forwarded from the paired transact proof's `out_cm`. -/
  leaves_match_escrow : True
end Lelantos
