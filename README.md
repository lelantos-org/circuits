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
