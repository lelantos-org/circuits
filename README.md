# `@lelantos-org/circuits`

Companion artifact package for [`@lelantos-org/sdk`](../sdk). Ships
the Groth16 prover artifacts for the 2x2 transact circuit
(`2x2.wasm` + `2x2_final.zkey` + `verification_key.json`); the SDK's
`Wallet.connect()` auto-resolves these via subpath `exports`.

The `tree_update_batch` artifacts (built locally via
`just rebuild-batch`) are NOT shipped in the npm package — they live
in the contracts repo's deployment pipeline.

This README doubles as the development guide for circuit authors —
see "Layout" through "Status" below. Design details:
[src/README.md](src/README.md). Audit notes: [SECURITY.md](./SECURITY.md).

## Consuming the published package

### Node

```bash
npm install @lelantos-org/circuits
```

The SDK auto-resolves the artifacts via `import.meta.resolve`. No
further wiring needed:

```ts
import { Wallet } from "@lelantos-org/sdk";

const wallet = await Wallet.fromPrivateKey(pk, {
    network: "anvil",
    rpcUrl: "http://localhost:8545",
});
// SDK reads:
//   node_modules/@lelantos-org/circuits/build/2x2.wasm
//   node_modules/@lelantos-org/circuits/build/2x2_final.zkey
```

Override the location via `proverArtifacts` on `Wallet.connect()` or
the `LELANTOS_PROVER_ARTIFACTS_DIR` env var.

### Browser

GitHub Packages does not expose a public CDN, so there is no zero-
config browser path. Pick one:

1. **Bundle the assets.** Vite/Webpack/Next.js can inline static
   assets from `node_modules`. Resolve the artifact URLs through
   your bundler's asset pipeline and pass them to `Wallet.connect`:
   ```ts
   import wasmUrl from "@lelantos-org/circuits/2x2/2x2.wasm?url";
   import zkeyUrl from "@lelantos-org/circuits/2x2/2x2_final.zkey?url";
   const wallet = await Wallet.connect({
       ...,
       proverArtifacts: { circuit: wasmUrl, zkey: zkeyUrl },
   });
   ```
2. **Self-host.** Copy
   `node_modules/@lelantos-org/circuits/build/{2x2.wasm,2x2_final.zkey}`
   to your CDN and pass the public URLs as `proverArtifacts`.

### Subpath exports

| Specifier                                              | Resolves to                       |
|--------------------------------------------------------|-----------------------------------|
| `@lelantos-org/circuits/2x2/2x2.wasm`                  | `build/2x2.wasm` (4.8 MB)         |
| `@lelantos-org/circuits/2x2/2x2_final.zkey`            | `build/2x2_final.zkey` (52.7 MB)  |
| `@lelantos-org/circuits/2x2/verification_key.json`     | `build/verification_key.json`     |

### Artifact provenance

The single-contributor ceremony (`snarkjs zkey contribute`) is non-
deterministic — snarkjs mixes fresh `crypto.randomBytes(64)` into the
entropy source on every run, so the `2x2_final.zkey` SHA-256 differs
across rebuilds. Per-release hashes are recorded in the matching
[GitHub Release notes](https://github.com/lelantos-org/circuits/releases),
not pre-pinned. Verify a downloaded tarball against the release body:

```bash
shasum -a 256 \
    node_modules/@lelantos-org/circuits/build/2x2.wasm \
    node_modules/@lelantos-org/circuits/build/2x2_final.zkey \
    node_modules/@lelantos-org/circuits/build/verification_key.json
```

The pre-publish gate ([`scripts/check-artifacts.mjs`](./scripts/check-artifacts.mjs))
asserts presence, generous size bands, and vkey JSON shape — enough to
catch a broken build, not the artifact itself. Strict SHA-pinning will
return once the package switches to the post-MPC ceremony output
committed to git.

---

## For circuit authors

MASP (Multi-Asset Shielded Pool) circuits in Circom 2.2.3.

- [`src/2x2.circom`](src/2x2.circom) — 2-in / 2-out shielded transact:
  ownership, no double-spend, per-asset balance, no leakage of sender /
  receiver / asset / amount. Instantiated as `Transact(10, 2, 2, 5)`.
- [`src/tree_update_batch.circom`](src/tree_update_batch.circom) —
  relayer-side proof that the canonical commitment tree advances
  `old_root → new_root` by inserting up to `MAX_N=8` pairs of leaves
  (16 leaves max per batch) over a relayer-supplied frontier.
  Instantiated as `TreeUpdateBatch(10, 8)`. Includes per-pair Pedersen
  aggregate binding that closes the C-1 deposit-substitution attack on
  the deposit path.

Both circuits use SnarkCompression: the logical PIs are folded into
`(z, y)` via [`PolyEval`](src/lib/poly_eval.circom), so the Solidity
verifier sees only two field elements per proof. Coefficient layouts
are defined inside [`src/lib/poly_eval.circom`](src/lib/poly_eval.circom)
(`TransactCompress` / `BatchCompress`) and MUST match
[`contracts/src/lib/PubInputs.sol`](../contracts/src/lib/PubInputs.sol).

See [src/README.md](src/README.md) for the full design write-up.

## Layout

```
src/
  2x2.circom                # transact circuit (2-in / 2-out)
  tree_update_batch.circom  # relayer batch tree-advance circuit
  lib/
    tags.circom             # domain-separation tag constants + 2^64
    common.circom           # PathIndexSelectors + EmptySubtreeHashes
    note.circom             # NoteCommitment, key derivation, Nullifier
    merkle.circom           # quaternary Merkle level + dummy-aware proof
    insert.circom           # QuaternaryInsert (single-leaf, frontier IO)
    frontier_root.circom    # frontier → old_root rebuild (SOUNDNESS-CRITICAL)
    asset_gen.circom        # HashToAssetGen — Pedersen hash-to-curve
    value_commit.circom     # ValueCommit, MulH, ValueScalarMul, PointSum
    balance.circom          # RangeCheck64, DummyZeroValue, PerAssetPointBalance
    spent.circom            # SpentNote — per-input slot constraints
    output.circom           # OutputNote — per-output slot constraints
    clue.circom             # ClueCheck — FMD2 in-circuit clue derivation
    hash_to_bit.circom      # 4-constraint Legendre-symbol bit extractor
    poly_eval.circom        # PolyEval, TransactCompress, BatchCompress
  test/
    *.test.ts               # mocha + circom_tester suites (144 tests)
    helpers.ts              # witness builders + JS-side hashes
    fixtures/               # frozen witness vectors used by tests
SECURITY.md                 # audit checklist + circomspect baseline
justfile                    # compile / setup / prove / rebuild / test recipes
ptau/                       # phase-1 powers-of-tau (downloaded on demand)
build/                      # compiled artifacts (gitignored)
```

## Requirements

- [circom](https://docs.circom.io/) 2.2.3
- [snarkjs](https://github.com/iden3/snarkjs)
- node + npm (for `circomlib` in `node_modules` and tests)
- [just](https://github.com/casey/just)
- `curl`, `openssl`
- [circomspect](https://github.com/trail-of-bits/circomspect) for `just lint`

## Usage

```bash
# 2x2 transact (depends on ptau_17, ~64 MB)
just compile              # r1cs / wasm / sym for 2x2.circom
just setup                # phase-2 trusted setup (downloads ptau if missing)
just prove path/to/input.json
just rebuild              # compile + setup + sync Verifier.sol → ../contracts/src/
just all                  # compile + setup + prove

# tree_update_batch (depends on ptau_20, ~3 GB)
just compile-batch
just setup-batch
just prove-batch path/to/input.json
just rebuild-batch        # compile-batch + setup-batch + sync TreeUpdateBatchVerifier.sol
just all-tree             # compile + compile-batch + setup + setup-batch
```

```bash
just clean
```

`rebuild` / `rebuild-batch` re-run the prototype single-contributor
ceremony — existing proofs become invalid afterwards.

### Tests

```bash
npm install
just test     # mocha + circom_tester; runs all src/test/**/*.test.ts (144 tests)
```

Tests use `circom_tester` (witness + constraint check only) — no ptau
or trusted setup required. CI runs `just test`.

### Lint

```bash
just lint     # circomspect static analysis
```

12 warnings are known and documented in
[SECURITY.md](./SECURITY.md#static-analysis-baseline-circomspect).
New warnings outside that baseline MUST be triaged before merge.

## Verifier-visible public signals

Both circuits expose only `[z, y]`. Logical PIs are private witnesses
bound through `PolyEval` (Schwartz–Zippel over BN254 scalar field).

- **2x2 transact** — 30 logical PIs at `N_OUT=2`: `merkle_root`,
  `nullifier[2]`, `out_cm[2]`, `public_asset_id`, `public_in`,
  `public_out`, `in_cv[2][2]`, `out_cv[2][2]`, `recipient_address`,
  `chain_id`, `payer_address`, `relayer_address`, `out_cv_dep[2][2]`,
  `(out_clue_Rx, out_clue_Ry, out_clue_bits) · N_OUT`. Slot order MUST
  match `contracts/src/lib/PubInputs.sol :: compress(Transact, aux)`.
- **tree_update_batch** — `4 + 9·MAX_N = 76` logical PIs at `MAX_N=8`:
  `old_root`, `new_root`, `start_index`, `actual_count`,
  `cms[2·MAX_N]`, `cv_dep[2·MAX_N][2]`, `pair_asset[MAX_N]`,
  `pair_public_in[MAX_N]`, `is_deposit[MAX_N]`. Slot order MUST match
  `contracts/src/lib/PubInputs.sol :: compress(TreeUpdateBatch)`.

Full design in [src/README.md](src/README.md).

## Circuit constraints

R1CS totals (BN254, `snarkjs r1cs info`):

| Circuit                                                          | Constraints | Wires    | Private inputs | Labels   |
|------------------------------------------------------------------|------------:|---------:|---------------:|---------:|
| `2x2.circom` (DEPTH=10, N_IN=2, N_OUT=2, GAMMA=5)                |     111,728 |  111,805 |            180 |  273,709 |
| `tree_update_batch.circom` (DEPTH=10, MAX_N=8)                   |     348,269 |  348,069 |            114 |  606,405 |

Verifier-visible: 1 public input (`z`) + 1 public output (`y`) per
circuit.

What each circuit enforces in-zk. Anything not listed is the
contract's job — see SECURITY.md "Properties NOT enforced in the
circuit" and the `Properties NOT enforced in-circuit` block at the top
of [src/2x2.circom](src/2x2.circom).

### `2x2.circom` — Transact(DEPTH=10, N_IN=2, N_OUT=2, GAMMA=5)

Per spent slot `i` ([`SpentNote`](src/lib/spent.circom)):
- `is_dummy ∈ {0,1}`; if `is_dummy = 1` then `value = 0` (via
  `DummyZeroValue` in the parent).
- Key hierarchy: `pk_check` from `nsk → ivk → pk` (bypassed for dummies).
- Note commitment `cm_i = NoteCommit(asset_id, value, pk, rho, rcm)`.
- Quaternary Merkle path opens to `merkle_root` over `DEPTH=10` levels
  (skipped for dummies).
- Nullifier `nullifier[i] = Poseidon(TAG_NF, nk, rho)` with
  `nk = Poseidon(TAG_NK, nsk)` — always real, including dummies.
- Value commitment `in_cv[i] = value · V^t(asset_id) + rcv · H` on
  Baby-Jubjub; `rH_i = rcv · H` exposed for the balance check.
- `asset_id != 0` for real notes (ghost-note defense).
- `cv_dep_i = value · V^t + rcv_dep · H` recomputed and pinned into the
  Merkle leaf `Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y)` so the
  spend reproduces the deposit-anchored commitment.

Per output slot `j` ([`OutputNote`](src/lib/output.circom)):
- `out_cm[j] = NoteCommit(asset_id, value, pk, rho, rcm)`.
- `out_cv[j] = value · V^t + rcv · H`; `rH_j` exposed for balance.
- `cv_dep[j] = value · V^t + rcv_dep · H` bound to public
  `out_cv_dep[j]` so the contract forwards the same point to
  `tree_update_batch`.
- `asset_id != 0` (no dummy bypass on the output side).
- FMD clue ([`ClueCheck`](src/lib/clue.circom)): `R = r · G_8` plus γ=5
  Legendre-bit checks `clue_bits[j] === 1 - legendre_bit(...)` per slot.

Public-bucket / balance:
- `V^pub = HashToAssetGen(public_asset_id)` derived in-circuit (no
  externally witnessed point).
- `RangeCheck64` on `public_in`, `public_out` (defense-in-depth on the
  contract `< 2^64` check).
- `PerAssetPointBalance`:
  `Σ in_cv + pub_in·V^pub + Σ out_rH  ==  Σ out_cv + pub_out·V^pub + Σ in_rH`.

PI compression:
- `TransactCompress(N_OUT)` (lib/poly_eval.circom) emits `y = Σ coeffs[k]·z^k`.
  Slots [0..23] = base PIs; slots [24..24+3·N_OUT) = clue triples per
  output. Total = 24 + 3·N_OUT = 30 for N_OUT=2.

### `tree_update_batch.circom` — TreeUpdateBatch(DEPTH=10, MAX_N=8)

- Range-check `actual_count ∈ [1, MAX_N]` via `Num2Bits(COUNT_BITS=3)`.
- Per-pair active selector `active[i] = (i < actual_count)`. Inactive
  pairs MUST have all per-pair fields zero (cms, cv_dep, pair_asset,
  pair_public_in, is_deposit, rcv_total) — enforced by padding
  constraints (load-bearing for PolyEval binding).
- `is_deposit[i] ∈ {0, 1}` (booleanized).
- Per-cm Merkle leaf `leaves[k] = Poseidon(TAG_LEAF, cms[k], cv_dep[k][0], cv_dep[k][1])`.
- Per-pair deposit binding when `active[i] · is_deposit[i] == 1`:
  `cv_dep[2i] + cv_dep[2i+1] == pair_public_in[i] · V^pair_asset[i] + rcv_total[i] · H`.
  Closes the C-1 deposit-substitution attack: forces both leaves in a
  deposit pair to share the public `(asset, value)` total.
- Frontier binding ([`FrontierRoot`](src/lib/frontier_root.circom)):
  rebuild `old_root` from `frontier_in + start_index_bits` and assert
  equality — without this, a relayer could forge an `old_root` matching
  `currentRoot()` and DoS the pool.
- Sequential pair-insert via two `QuaternaryInsert(DEPTH)` per pair;
  inactive pairs carry the previous frontier / root through a mux.
- `new_root === running_root[MAX_N]`.
- `BatchCompress(MAX_N)` (lib/poly_eval.circom) folds 4 + 9·MAX_N
  coefficients into `(z, y)`.

## Status

Prototype. Trusted setup uses a single contributor — **not
production-safe**. Do a real MPC ceremony before mainnet use; this
package will bump to `1.0.0` once that ceremony completes. See
[SECURITY.md](./SECURITY.md) for the full mainnet checklist.
