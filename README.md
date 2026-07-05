# Lelantos Circuits

Groth16 prover artifacts for the Lelantos 2x2 transact circuit, consumed by
[`@lelantos-org/sdk`](../sdk) (`2x2.wasm`, `2x2_final.zkey`,
`verification_key.json`). The SDK resolves them automatically via subpath
`exports`.

The `tree_update_batch` artifacts are **not** shipped in the npm package —
they are built locally (`just rebuild-batch`) and deployed through the
contracts repo's pipeline.

Circuit design: [src/README.md](src/README.md).

## Installation

```bash
npm install @lelantos-org/circuits
```

The SDK locates the artifacts via `import.meta.resolve` — no wiring needed:

```ts
import { Wallet } from "@lelantos-org/sdk";

const wallet = await Wallet.fromPrivateKey(pk, {
    network: "anvil",
    rpcUrl: "http://localhost:8545",
});
```

Override the artifact location with `proverArtifacts` on `Wallet.connect()`
or the `LELANTOS_PROVER_ARTIFACTS_DIR` env var.

### Browser

GitHub Packages has no public CDN, so pick one:

1. **Bundle the assets** — resolve the artifact URLs through your bundler
   and pass them to `Wallet.connect`:
   ```ts
   import wasmUrl from "@lelantos-org/circuits/2x2/2x2.wasm?url";
   import zkeyUrl from "@lelantos-org/circuits/2x2/2x2_final.zkey?url";
   const wallet = await Wallet.connect({
       ...,
       proverArtifacts: { circuit: wasmUrl, zkey: zkeyUrl },
   });
   ```
2. **Self-host** — copy the artifacts from
   `node_modules/@lelantos-org/circuits/build/` to your CDN and pass the
   public URLs as `proverArtifacts`.

### Subpath exports

| Specifier                                          | Resolves to                    |
|----------------------------------------------------|--------------------------------|
| `@lelantos-org/circuits/2x2/2x2.wasm`              | `build/2x2.wasm` (~4.8 MB)     |
| `@lelantos-org/circuits/2x2/2x2_final.zkey`        | `build/2x2_final.zkey` (~36 MB)|
| `@lelantos-org/circuits/2x2/verification_key.json` | `build/verification_key.json`  |

### Artifact provenance

The single-contributor ceremony (`snarkjs zkey contribute`) is
non-deterministic — snarkjs mixes fresh `crypto.randomBytes(64)` into the
entropy on every run, so the zkey SHA-256 differs across rebuilds.
Per-release hashes are recorded in the matching
[GitHub Release notes](https://github.com/lelantos-org/circuits/releases).
Verify a downloaded tarball against the release body:

```bash
shasum -a 256 \
    node_modules/@lelantos-org/circuits/build/2x2.wasm \
    node_modules/@lelantos-org/circuits/build/2x2_final.zkey \
    node_modules/@lelantos-org/circuits/build/verification_key.json
```

The pre-publish gate ([`scripts/check-artifacts.mjs`](./scripts/check-artifacts.mjs))
asserts file presence, size bands, and vkey JSON shape — enough to catch a
broken build, not to authenticate the artifact. Strict SHA-pinning returns
once the package ships the post-MPC ceremony output committed to git.

---

## Development

MASP (Multi-Asset Shielded Pool) circuits in Circom 2.2.3 over BN254, with
Baby-Jubjub for value commitments.

- [`src/2x2.circom`](src/2x2.circom) — `Transact(10, 2, 2)`, the shielded
  transact circuit: note ownership, no double-spend, per-asset balance, no
  leakage of sender / receiver / asset / amount. FMD clues are computed
  off-circuit by the client and bound via PolyEval.
- [`src/2x3.circom`](src/2x3.circom), [`src/3x3.circom`](src/3x3.circom) —
  the same wiring at 2-in/3-out and 3-in/3-out. No artifacts shipped yet.
- [`src/tree_update_batch.circom`](src/tree_update_batch.circom) —
  `TreeUpdateBatch(10, 8)`, the relayer-side proof that the commitment tree
  advances `old_root → new_root` by inserting up to 8 pairs of leaves over a
  relayer-supplied frontier. Includes the per-pair Pedersen aggregate
  binding that closes the C-1 deposit-substitution attack.

All circuits compress their public inputs: the logical PIs are folded into
`(z, y)` via [`PolyEval`](src/lib/poly_eval.circom), so the Solidity
verifier sees only two field elements per proof. Coefficient layouts
(`TransactCompressN` / `BatchCompress`) MUST match
[`contracts/src/lib/PubInputs.sol`](../contracts/src/lib/PubInputs.sol).

Full design write-up: [src/README.md](src/README.md).

### Requirements

- [circom](https://docs.circom.io/) 2.2.3
- [snarkjs](https://github.com/iden3/snarkjs)
- node + npm (for `circomlib` and tests)
- [just](https://github.com/casey/just)
- `curl`, `openssl`
- [circomspect](https://github.com/trail-of-bits/circomspect) for `just lint`

### Build

```bash
# 2x2 transact (downloads ptau_17, ~64 MB, on first setup)
just compile              # r1cs / wasm / sym
just setup                # phase-2 trusted setup
just prove path/to/input.json
just rebuild              # compile + setup + sync Verifier.sol → ../contracts/src/verifiers/

# tree_update_batch (downloads ptau_20, ~3 GB, on first setup)
just compile-batch
just setup-batch
just prove-batch path/to/input.json
just rebuild-batch        # + sync TreeUpdateBatchVerifier.sol

just clean
```

`rebuild` / `rebuild-batch` re-run the prototype single-contributor
ceremony — existing proofs become invalid afterwards.

### Test

```bash
npm install
just test        # full suite (unit + fuzz at FUZZ=medium)
just test-unit   # unit suites only
just test-fuzz   # heavy fuzz suite (FUZZ=heavy)
```

Tests use `circom_tester` (witness + constraint checks) — no ptau or
trusted setup required. CI runs `just test`.

### Lint

```bash
just lint        # circomspect static analysis
```

Suppressed analysis passes are reviewed and documented inline in the
[`justfile`](./justfile) `lint` recipe. New warnings MUST be triaged
before merge.

### Constraint counts

R1CS totals on BN254 (`snarkjs r1cs info`):

| Circuit                                    | Constraints | Wires   | Private inputs |
|--------------------------------------------|------------:|--------:|---------------:|
| `2x2.circom` — `Transact(10, 2, 2)`        |      70,096 |  70,171 |            142 |
| `tree_update_batch.circom` — `TreeUpdateBatch(10, 8)` | 348,269 | 348,069 |     114 |

## Status

Prototype. The trusted setup uses a single contributor — **not
production-safe**. A real MPC ceremony is required before mainnet use; the
package bumps to `1.0.0` once that ceremony completes.
