# circuits

MASP (Multi-Asset Shielded Pool) circuits in Circom.

- `2x2.circom` — 2-in / 2-out shielded transact: ownership, no double-spend, per-asset balance, without revealing sender / receiver / asset / amount.
- `tree_update.circom` — relayer-side proof that the on-chain commitment tree advances `oldRoot → newRoot` by inserting two leaves (`cm0`, `cm1`) at `[startIndex, startIndex+1]` over a relayer-supplied frontier. Lazy-root model.

Both circuits use SnarkCompression: 22 logical PIs (transact) / 5 logical PIs (tree_update) are folded into `(z, y)` via `PolyEval`, so the Solidity verifier sees only two field elements per proof.

See [src/README.md](src/README.md) for full design notes.

## Layout

```
src/
  2x2.circom            # transact circuit (2-in / 2-out)
  tree_update.circom    # relayer tree-advance circuit (lazy root)
  lib/                  # primitives — notes, merkle, asset gen, value commit,
                        #   balance, spent, output, insert (QuaternaryInsert),
                        #   poly_eval, tags
  test/
    *.test.ts           # transact / merkle / tree_update suites
    helpers.ts          # witness builders + JS-side hashes
    fixtures/           # frozen witness vectors used by tests
justfile                # compile / setup / prove / rebuild / test recipes
ptau/                   # phase-1 powers-of-tau (downloaded on demand)
build/                  # compiled artifacts (gitignored)
```

## Requirements

- [circom](https://docs.circom.io/) 2.x
- [snarkjs](https://github.com/iden3/snarkjs)
- node + npm (for `circomlib` in `node_modules` and tests)
- [just](https://github.com/casey/just)
- `curl`, `openssl`

## Usage

Per-circuit recipes:

```bash
# 2x2 transact
just compile              # r1cs / wasm / sym for 2x2.circom
just setup                # phase-2 trusted setup (downloads ptau if missing)
just prove path/to/input.json
just rebuild              # compile + setup + sync Verifier.sol → ../contracts/src/
just all                  # compile + setup + prove

# tree_update
just compile-tree
just setup-tree
just prove-tree path/to/input.json
just rebuild-tree         # compile-tree + setup-tree + sync TreeUpdateVerifier.sol
just all-tree             # compile + compile-tree + setup + setup-tree

just clean
```

`rebuild` / `rebuild-tree` re-run the prototype single-contributor ceremony — existing proofs become invalid afterwards.

### Tests

```bash
npm install
just test           # mocha + circom_tester; runs all *.test.ts suites
```

Tests use `circom_tester` (witness + constraint check only) — no ptau or trusted setup required. CI runs `just test`.

## Verifier-visible public signals

Both circuits expose only `[z, y]`. The logical PIs below are private witnesses bound through `PolyEval` (Schwartz–Zippel binding over the BN254 scalar field).

- **2x2 transact** — 22 logical PIs: `merkle_root`, `nullifier[2]`, `out_cm[2]`, `public_asset_id`, `pub_asset_gen_x`, `pub_asset_gen_y`, `public_in`, `public_out`, `in_cv[2]`, `out_cv[2]`, `recipient_address`, `chain_id`, `payer_address`, `relayer_address`. Slot order MUST match `contracts/src/MASP.sol::_flatten()`.
- **tree_update** — 5 logical PIs: `old_root`, `new_root`, `cm0`, `cm1`, `start_index`. Slot order MUST match `_compressTreeUpdatePI` in the contract.

Full design in [src/README.md](src/README.md).

## Circuit constraints

R1CS totals (BN254, `snarkjs r1cs info`):

| Circuit | Constraints | Wires | Private inputs | Labels |
|---|---:|---:|---:|---:|
| `2x2.circom` (DEPTH=10, N_IN=2, N_OUT=2, GAMMA=5) | 102,970 | 103,037 | 154 | 247,289 |
| `tree_update.circom` (DEPTH=10) | 34,068 | 34,082 | 35 | 54,982 |

Verifier-visible: 1 public input (`z`) + 1 output (`y`) per circuit.

What each circuit enforces in-zk. Anything not listed is contract's job (see `Properties NOT enforced in-circuit` in [src/2x2.circom](src/2x2.circom)).

### `2x2.circom` — Transact (DEPTH=10, N_IN=2, N_OUT=2, GAMMA=5)

Per spent slot `i` (`SpentNote`, [src/lib/spent.circom](src/lib/spent.circom)):
- `is_dummy ∈ {0,1}`; if `is_dummy = 1` then `value = 0` (`DummyZeroValue`).
- Note commitment `cm_i = NoteCommit(asset_id, value, pk, rho, rcm)`.
- Quaternary Merkle path: `cm_i` opens to `merkle_root` along `path_elements[DEPTH][3]` / `path_indices[DEPTH]` (skipped for dummies).
- Nullifier `nullifier[i] = PRF_nsk(rho, cm_i)` — binds note to spending key.
- Value commitment `in_cv[i] = value · V^t(asset_id) + rcv · H` on Baby-Jubjub; `rH_i = rcv · H` exported for balance.

Per output slot `j` (`OutputNote`, [src/lib/output.circom](src/lib/output.circom)):
- `out_cm[j] = NoteCommit(asset_id, value, pk, rho, rcm)`.
- `out_cv[j] = value · V^t(asset_id) + rcv · H`; `rH_j = rcv · H` exported.
- FMD clue (`ClueCheck`, [src/lib/clue.circom](src/lib/clue.circom)): `R = r · G_8`; for each of `GAMMA=5` flag-keys, `clue_bits[j]` low bits = `1 - lsb1(Poseidon(...))`. `out_clue_Rx`, `out_clue_Ry` exposed for PolyEval binding.

Public-bucket / balance:
- `SafePoint(pub_asset_gen)`: on Baby-Jubjub curve and `x ≠ 0` (rules out identity + 2-torsion). Cofactor-8 subgroup membership is contract-side.
- `RangeCheck64` on `public_in`, `public_out` (belt-and-suspenders to contract `< 2^64`).
- `pub_in_pt = public_in · V^pub`, `pub_out_pt = public_out · V^pub` via `ValueScalarMul` over the 64 range bits.
- `PerAssetPointBalance`: Edwards-point equality
  `Σ in_cv + pub_in_pt + Σ out_rH  ==  Σ out_cv + pub_out_pt + Σ in_rH`.
  `rcv·H` cancels ⇒ per-asset value conservation; distinct assets sit in distinct `V^t` subgroups so cross-asset cancel needs Pedersen DL break.

PI compression:
- `PolyEval(22 + 3·N_OUT)` Horner-evals `[merkle_root, nullifier[2], out_cm[2], public_asset_id, pub_asset_gen_x/y, public_in/out, in_cv[2][2], out_cv[2][2], recipient_address, chain_id, payer_address, relayer_address, (out_clue_Rx, out_clue_Ry, out_clue_bits)·N_OUT]` at `z`. Output `y` is the only verifier-visible signal beside `z`. Slot order MUST match `MASP.sol::_flatten()`.

### `tree_update.circom` — TreeUpdate (DEPTH=10)

- `Num2Bits(2·DEPTH)` on `start_index` and on `start_index + 1` ⇒ both fit in 20 bits ⇒ `start_index ≤ 4^DEPTH − 2` (room for 2nd insert).
- Per level `d`, 2-bit digits `idx0_digits[d] = b0 + 2·b1`, same for `idx1` from `start_index+1`.
- `ins0 = QuaternaryInsert(DEPTH)` ([src/lib/insert.circom](src/lib/insert.circom)): inserts `cm0` at `start_index` over `frontier_in`, emits `frontier_out`.
- `ins1 = QuaternaryInsert(DEPTH)`: inserts `cm1` at `start_index+1` over `ins0.frontier_out`.
- `new_root === ins1.root` — binds public `new_root` to the chained inserts.
- `old_root` is NOT recomputed; contract anchors it via `oldRoot == currentRoot()`. Inconsistent `(frontier_in, old_root)` only harms the relayer (useless ring entry, no soundness break).
- `PolyEval(5)` over `[old_root, new_root, cm0, cm1, start_index]` at `z`, output `y`. Slot order MUST match contract `_compressTreeUpdatePI`.

## Status

Prototype. Trusted setup uses a single contributor — **not production-safe**. Do a real MPC ceremony before mainnet use.
