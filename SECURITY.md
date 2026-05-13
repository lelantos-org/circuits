# Circuits — Security & Audit Checklist

Scope: Lelantos MASP zk-circuits in `src/`. This file lists invariants the
**contract** (or other off-circuit caller) must enforce, plus the
prototype-only caveats that block mainnet use as-is.

## Circuit ↔ contract contract

The circuits compress logical public inputs into a single `(z, y)` pair via
`PolyEval` (see [src/lib/poly_eval.circom](src/lib/poly_eval.circom)). The
contract MUST mirror the coefficient layout byte-for-byte. Any drift is a
soundness break.

| Circuit                    | Layout source                                                    | Contract counterpart                          |
|----------------------------|------------------------------------------------------------------|-----------------------------------------------|
| `2x2.circom`               | [src/2x2.circom](src/2x2.circom) header (slots `[0..23]` + `3·N_OUT` clue) | `contracts/src/MASP.sol :: _flatten()`        |
| `tree_update_batch.circom` | [src/tree_update_batch.circom](src/tree_update_batch.circom) header (`4 + 9·MAX_N`) | `contracts/src/MASP.sol :: PubInputs.TreeUpdateBatch::compress` |

A CI lint (`scripts/lint-polyeval-layout.mjs`, invoked via `just lint`)
parses both sides and asserts agreement. Do not bypass it.

## Properties NOT enforced in the circuit — contract MUST check

### `2x2.circom`
- `chain_id == block.chainid`
- `public_in  < 2^64`
- `public_out < 2^64`
- `public_asset_id < 2^64` (or whatever registry key range applies)
- `recipient_address < 2^160` (typed as `address`)
- `payer_address < 2^160`
- `relayer_address < 2^160`
- Each `nullifier[i]` inserted unconditionally; revert on already-spent (no
  sentinel for dummies)
- Each `out_cm[j]` inserted unconditionally into the cm tree (no sentinel)

### `tree_update_batch.circom`
- `start_index + 2*MAX_N - 1 < 4^DEPTH` (caller must not overflow capacity)
- `old_root` MUST equal the canonical on-chain root at submission time
- After verification, the contract MUST advance the canonical root to
  `new_root` atomically; replays past `old_root` would otherwise reapply the
  batch

### Both
- Verifier inputs `(z, y)` taken from a Fiat–Shamir transcript bound to the
  full logical public-input vector. A constant or attacker-chosen `z`
  destroys the Schwartz–Zippel argument.

## Field-size assumptions (BN254 scalar field, ~2^253.6)

- `Num2Bits_strict()` callers rely on the strict variant to reject
  representatives above the field modulus. Plain `Num2Bits(n)` for `n < 254`
  is sufficient when the high bits are independently constrained.
- All asset-id range checks use `Num2Bits(64)` inside
  [src/lib/asset_gen.circom](src/lib/asset_gen.circom) (`HashToAssetGen`),
  so `in_asset[i]`, `out_asset[j]`, `public_asset_id`, `pair_asset[i]` are
  in `[0, 2^64)` in-circuit. Contract checks are defense-in-depth.

## Trusted setup — PROTOTYPE ONLY

The `setup` and `setup-batch` recipes in [justfile](justfile) run a
**single-contributor** Groth16 phase-2 ceremony with random entropy from
`openssl rand`. Toxic waste is not destroyed; the contributor’s machine
must be assumed compromised. Do not deploy the resulting `*_final.zkey` or
`Verifier.sol` on any production network.

For mainnet:
1. Run a multi-party phase-2 ceremony (e.g. `snarkjs zkey contribute` chain
   across ≥ N independent contributors).
2. Publish the contribution transcript.
3. Recompute `release-manifest.json` SHA-256 hashes from the multi-party
   final zkey and refresh `scripts/check-artifacts.mjs`.

## Frontier-binding soundness (`tree_update_batch.circom`)

The relayer supplies `frontier_in[DEPTH][3]`. Without binding,
`old_root` could be forged. `FrontierRoot` (see
[src/lib/frontier_root.circom](src/lib/frontier_root.circom)) reconstructs
`old_root` from `frontier_in` + `start_index`, and the circuit asserts
equality with the public `old_root`. Inactive trailing pairs must zero all
per-pair fields (lines `114-125`) — otherwise the aggregate Pedersen check
could leak randomness through padding slots. Audit any change to that loop
with extra care.

## Pre-merge checklist for circuit edits

1. `just compile && just compile-batch` — both succeed
2. `just test` — full mocha suite passes
3. `just lint` — `circomspect` clean **and** PolyEval-layout lint passes
4. If r1cs constraint count changed: rebuild ceremony + regenerate
   `release-manifest.json`, update `scripts/check-artifacts.mjs` digests,
   and refresh `contracts/src/Verifier.sol`.
5. If you touched `tree_update_batch.circom`: confirm `MAX_N` headroom
   against ptau_20 (`~547k` constraints at `MAX_N=16`,
   ~half at `MAX_N=8`).
6. Update this file if a new contract-side invariant is introduced.

## Static-analysis baseline (`circomspect`)

`just lint` runs Trail-of-Bits circomspect over `src/`. The following
warnings are known and accepted (do **not** suppress without re-review):

1. `lib/hash_to_bit.circom:43` — `inv <-- 1 / hash; inv * hash === 1`.
   Standard non-zero check: if `hash == 0`, no `inv` satisfies the equality
   and the witness is rejected. Divisor cannot be zero in any sound proof.
2. `lib/clue.circom:71` — `Num2Bits(GAMMA)` with `GAMMA = 5`. No aliasing
   risk: `5 ≪ 254`, all 5-bit values are unique field elements.
3. `lib/output.circom:85`, `lib/spent.circom:84` — `vc_dep.rH` unused.
   `ValueCommit` exposes `rH` for the primary `vc` (consumed by the balance
   check). `vc_dep` only needs `cv`. The `rH` computation is shared
   internal Pedersen state (`MulH` for `rcv·H`) that the constraint system
   needs anyway for the `cv` output, so removing it would save zero
   constraints. Two linear stub constraints (`rH[k] <== rHmul.out[k]`) are
   the only overhead; the circom optimizer elides them.

New circomspect warnings outside this list MUST be triaged before merge.

## Reporting

Suspected vulnerabilities: do **not** open a public issue. Email the
maintainers with a reproducer.
