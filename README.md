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

## Status

Prototype. Trusted setup uses a single contributor — **not production-safe**. Do a real MPC ceremony before mainnet use.
