import Lelantos.Circuit.Layout
import Lelantos.Circuit.BatchLayout
import Lelantos.Gadgets.PolyEval

/-!
# What the contracts must check

Both circuits leave work to their verifier, and this module is the ledger of it: one
structure per circuit, one field per check, listed so that no theorem elsewhere is read as
covering them. Nothing in the development assumes any field of either.

A field is either **stated** — a relation between objects this development has, which the
contract is claimed to establish — or a **stub**, `True`, naming a check whose subject (a
nullifier set, an EVM `block.chainid`, a keccak preimage, the live accumulator, an escrow
digest) has no counterpart here. A stub states no property, so no check in `lean/` can fail
on it; it is a claim made outside Lean. A stated field is an assumption, not a result.

`Challenge` is in `Lelantos.Gadgets.PolyEval`, next to `polyEval_forge`, which is why both
ledgers need it: the prover reads `z` before choosing a witness, so the compression binds
only if the challenge covers the vector actually evaluated.
-/

namespace Lelantos

variable {depth nIn nOut : ℕ}

/-! ## `src/4x6.circom` -/

/-- What `Transact(depth, nIn, nOut)` leaves to `MASP.sol`.

`challenge_binds_witness` and `nullifiers_distinct` are stated; both range over this
witness. The other three are stubs. -/
structure ContractObligations (chal : Challenge) (w : TxWitness depth nIn nOut) : Prop where
  /-- `nullifier[i]` is unspent — a statement about the set of nullifiers every *earlier*
  transaction published, which is why it is a stub. Distinctness *within* this transaction
  is the separate `nullifiers_distinct` below. This also makes `rho` derivation
  collision-free across transactions, since `DeriveRho` anchors on `nullifier[0]`. -/
  nullifiers_fresh : True
  /-- **No two input slots carry the same nullifier.**

  Each slot is opened against the shared root on its own, so nothing in `Transact` stops
  one note filling two of them: the duplicate satisfies every constraint, and
  `PerAssetValueBalance` counts its value once per slot, so the spender draws twice what
  the note holds. `src/4x6.circom:56-58` names the check as the consumer's;
  `contracts/src/MASP.sol:1082-1086` is it: a pairwise scan, `DuplicateNullifier` on a hit.

  Stated rather than stubbed, because the nullifiers are fields of this witness. What the
  contract compares are the calldata copies, which are these values only under
  `challenge_binds_witness`; the nullifier slots are coefficients (`PISlot.nullifier`), so
  that field covers them.

  The range is every slot, dummies included. `is_dummy` is private, so the contract cannot
  tell the slots apart, and `MASP._consumeNullifier` at `contracts/src/MASP.sol:1062-1064`
  runs over all of them. A dummy slot's nullifier is still
  `Poseidon(TAG_NF, nk, rho, cm)` over a note the prover chose freely, so distinctness is a
  constraint on the prover, not a property of honest padding. -/
  nullifiers_distinct : ∀ a b, a < nIn → b < nIn → a ≠ b →
    (w.spent a).nullifier ≠ (w.spent b).nullifier
  /-- **The challenge covers this witness's coefficient vector.**

  The vector fed to the hash must agree with `txCoeffs w`, the one the accepted proof
  evaluated. The contract hashes the vector it reconstructs from calldata and never sees
  `txCoeffs w`, so nothing on-chain establishes this directly. It follows from the pinning
  argument below: every coefficient is fixed by a constraint the prover cannot solve
  around, so the only vector it can evaluate is the one describing its transaction.

  The property is a relation between the challenge and the witness, not a check performed,
  so it is stated rather than stubbed. `chal` ranges over more than `txCoeffs w`: the
  contract's preimage is 70 words at the deployed shape against 46 coefficients, since the
  addresses, the FMD clues and the payload digest are hashed but not evaluated, which binds
  them without a constraint. This field states only the part that must agree. -/
  challenge_binds_witness : chal (txCoeffs w) w.z
  /-- `chain_id = block.chainid` and `recipient_address < 2^160`.

  Checked against the calldata copy of those fields, which is a different quantity from
  `w.chainId` / `w.recipient` unless `challenge_binds_witness` holds. -/
  address_and_chain_checked : True
  /-- `out_aux_digest` is recomputed from the `aux` calldata, not taken from it. The
  coefficient binds whatever value the prover supplied; only this check ties that value to
  the encrypted-note payload the recipient receives. Without it a relayer could keep the
  `PolyEval`-bound clue intact (so the recipient still flags the note) while corrupting
  `ephPub` and the ciphertext, leaving a note that cannot be opened after its inputs are
  spent. -/
  aux_digest_recomputed : True

/-! ## `src/tree_update_batch.circom`

`BatchChainSat` says where the tree *goes*; it says nothing about where it *is*. `old_root`,
`start_index` and `actual_count` are inputs of the batch, so every result in
`Lelantos.Circuit.TreeUpdateBatch` is conditional on them, and a proof over a stale root or
a wrong start position is as valid as one over the live tree. The leaves are the same
story: `batch_deposit_opens` says leaf `k` opens at its declared
`(leaf_asset, leaf_public_in)`, not that those are the asset and amount anybody escrowed.
-/

/-- What `TreeUpdateBatch(depth, maxL)` leaves to `MASP.sol`.

`challenge_binds_witness` is stated; the other four are stubs. Unlike the transact layout,
all `4 + 6·MAX_L` words are coefficients, so that one field covers every public field of
the batch: there are no challenge-only words here to bind separately. -/
structure BatchContractObligations {depth maxL : ℕ} (chal : Challenge) (z : F)
    (w : BatchSignals depth maxL) : Prop where
  /-- **The challenge covers this witness's coefficient vector**, the transact obligation of
  the same name read over `batchCoeffs`. `polyEval_forge` is why it is load-bearing: the
  prover reads `z` before choosing a witness, so a coefficient no constraint pins sends `y`
  wherever it likes. The verification at `contracts/src/MASP.sol:737-738`
  (`TreeUpdateRejected` on a reject) is against the vector the contract rebuilds from its
  own calldata, never against `batchCoeffs w`. -/
  challenge_binds_witness : chal (batchCoeffs w) z
  /-- `old_root` is the tree's live root, not some root it once had —
  `MASP._requireTreePosition` at `contracts/src/MASP.sol:760-761`, and on the spend path
  `currentRoot()` fed into the proof image at `contracts/src/MASP.sol:1060-1061` instead.
  Without it `batch_advances_by_count` advances a tree nobody is keeping. -/
  old_root_is_live : True
  /-- `start_index` is the number of leaves already committed, so the batch appends at the
  frontier rather than overwriting (`contracts/src/MASP.sol:763`, reverting with
  `BatchMisaligned`). `batch_capacity` bounds `start_index + actual_count` by the tree's
  size; it says nothing about where the tree currently ends. -/
  start_index_is_committed_count : True
  /-- `actual_count` is the number of leaves the payload actually carries — two per deposit
  on the flush path (`contracts/src/MASP.sol:749-752`, `MASP._validateBatchHeader`), the
  fixed output count on the spend path. `batch_active_spec` makes the active run a prefix of
  that length, so an unchecked `actual_count` would commit padding as leaves or silently
  drop a deposit. -/
  count_matches_payload : True
  /-- Each active leaf is the one its escrow record describes: `cms`, `cv_dep`,
  `leaf_asset`, `leaf_public_in` and `is_deposit` are checked against the digest stored at
  submit, and the record is deleted, so one escrow funds one leaf —
  `DepositNotPending` … `BadDepositMode` at `contracts/src/MASP.sol:785-792`, then the
  `escrowed` entry dropped at `contracts/src/MASP.sol:861`. `batch_deposit_opens`
  gives the opening of a leaf against its *own* declared fields; this is what ties those
  fields to tokens someone actually paid in. -/
  leaves_match_escrow : True
end Lelantos
