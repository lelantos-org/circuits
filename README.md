# circuits

MASP (Multi-Asset Shielded Pool) circuits in Circom. Provides `2x2`: a 2-input / 2-output shielded transaction proving ownership, no double-spend, and per-asset balance — without revealing sender, receiver, asset, or amount.

See [src/CIRCUITS.md](src/CIRCUITS.md) for full design notes.

## Layout

```
src/
  2x2.circom            # top-level circuit (2-in / 2-out)
  lib/                  # primitives (notes, merkle, asset gen, value commit, balance, spent, output)
  test/                 # circom_tester + ts test suite
justfile                # compile / setup / prove / test recipes
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

```bash
just compile              # build r1cs / wasm / sym
just setup                # phase-2 trusted setup (downloads ptau if missing)
just prove path/to/input.json
just all                  # compile + setup + prove
just clean
```

### Tests

```bash
npm install
just test           # or: npm test
```

Tests use `circom_tester` (witness + constraint check only) — no ptau or trusted setup required. CI runs `just test`.

## Public inputs

20 fields: `merkle_root`, `nullifier[2]`, `out_cm[2]`, `public_in`, `public_out`, `asset_id`, `recipient_address`, `chain_id`, `in_cv[2]`, `out_cv[2]`. Details in [src/CIRCUITS.md](src/CIRCUITS.md).

## Status

Prototype. Trusted setup uses a single contributor — **not production-safe**. Do a real MPC ceremony before mainnet use.
