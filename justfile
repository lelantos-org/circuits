set shell := ["bash", "-ceuo", "pipefail"]

# === paths ===
ROOT := justfile_directory()
BUILD := ROOT / "build"
PTAU_DIR := ROOT / "ptau"
PTAU_URL_BASE := "https://storage.googleapis.com/zkevm/ptau"
PTAU17 := "powersOfTau28_hez_final_17.ptau"
PTAU20 := "powersOfTau28_hez_final_20.ptau"

# Sync targets in sibling contracts/ checkout. Updated for new src/ layout
# (verifiers grouped under src/verifiers/).
CONTRACTS_VERIFIER := ROOT / ".." / "contracts" / "src" / "verifiers" / "Verifier.sol"
CONTRACTS_TREE_BATCH_VERIFIER := ROOT / ".." / "contracts" / "src" / "verifiers" / "TreeUpdateBatchVerifier.sol"

default:
    @just --list

# === 2x2 circuit ===

# Compile 2x2.circom -> r1cs + wasm + sym, print constraint count.
compile:
    mkdir -p "{{BUILD}}"
    echo "==> Compiling {{ROOT}}/src/2x2.circom"
    circom "{{ROOT}}/src/2x2.circom" --r1cs --wasm --sym -o "{{BUILD}}" -l "{{ROOT}}/node_modules"
    echo "==> Constraint info"
    npx snarkjs r1cs info "{{BUILD}}/2x2.r1cs"

# Phase-2 trusted setup (single-contributor; INSECURE — prototype only).
setup:
    just _fetch-ptau "{{PTAU17}}"
    echo "==> Phase-2 setup"
    npx snarkjs groth16 setup "{{BUILD}}/2x2.r1cs" "{{PTAU_DIR}}/{{PTAU17}}" "{{BUILD}}/2x2_0.zkey"
    echo "==> Single contribution (PROTOTYPE ONLY)"
    npx snarkjs zkey contribute "{{BUILD}}/2x2_0.zkey" "{{BUILD}}/2x2_final.zkey" --name="prototype-contributor" -e="$(openssl rand -hex 32)"
    echo "==> Export verification key"
    npx snarkjs zkey export verificationkey "{{BUILD}}/2x2_final.zkey" "{{BUILD}}/verification_key.json"
    echo "==> Export Solidity verifier"
    npx snarkjs zkey export solidityverifier "{{BUILD}}/2x2_final.zkey" "{{BUILD}}/Verifier.sol"
    echo "==> Done. Verifier at {{BUILD}}/Verifier.sol"

# Prove + verify a single witness from input.json.
prove input="":
    INPUT="{{ if input == "" { ROOT / "circuits/test/input.json" } else { input } }}"; \
    echo "==> Compute witness from $INPUT"; \
    node "{{BUILD}}/2x2_js/generate_witness.js" "{{BUILD}}/2x2_js/2x2.wasm" "$INPUT" "{{BUILD}}/witness.wtns"; \
    echo "==> Prove (groth16)"; \
    npx snarkjs groth16 prove "{{BUILD}}/2x2_final.zkey" "{{BUILD}}/witness.wtns" "{{BUILD}}/proof.json" "{{BUILD}}/public.json"; \
    echo "==> Verify"; \
    npx snarkjs groth16 verify "{{BUILD}}/verification_key.json" "{{BUILD}}/public.json" "{{BUILD}}/proof.json"

all: compile setup prove

# === tree_update_batch circuit ===

# Compile tree_update_batch.circom -> r1cs + wasm + sym, print constraint count.
compile-batch:
    mkdir -p "{{BUILD}}"
    echo "==> Compiling {{ROOT}}/src/tree_update_batch.circom"
    circom "{{ROOT}}/src/tree_update_batch.circom" --r1cs --wasm --sym -o "{{BUILD}}" -l "{{ROOT}}/node_modules"
    echo "==> Constraint info"
    npx snarkjs r1cs info "{{BUILD}}/tree_update_batch.r1cs"

# Phase-2 trusted setup for tree_update_batch (single-contributor; INSECURE).
# tree_update_batch (MAX_N=8) has ~348k constraints, requires ptau_20 (~3GB).
setup-batch:
    just _fetch-ptau "{{PTAU20}}"
    echo "==> Phase-2 setup (tree_update_batch)"
    npx snarkjs groth16 setup "{{BUILD}}/tree_update_batch.r1cs" "{{PTAU_DIR}}/{{PTAU20}}" "{{BUILD}}/tree_update_batch_0.zkey"
    echo "==> Single contribution (PROTOTYPE ONLY)"
    npx snarkjs zkey contribute "{{BUILD}}/tree_update_batch_0.zkey" "{{BUILD}}/tree_update_batch_final.zkey" --name="prototype-contributor" -e="$(openssl rand -hex 32)"
    echo "==> Export verification key"
    npx snarkjs zkey export verificationkey "{{BUILD}}/tree_update_batch_final.zkey" "{{BUILD}}/tree_update_batch_verification_key.json"
    echo "==> Export Solidity verifier"
    npx snarkjs zkey export solidityverifier "{{BUILD}}/tree_update_batch_final.zkey" "{{BUILD}}/TreeUpdateBatchVerifier.sol"
    echo "==> Done. Verifier at {{BUILD}}/TreeUpdateBatchVerifier.sol"

# Prove + verify a tree_update_batch witness.
prove-batch input="":
    INPUT="{{ if input == "" { ROOT / "circuits/test/tree_update_batch_input.json" } else { input } }}"; \
    echo "==> Compute witness from $INPUT"; \
    node "{{BUILD}}/tree_update_batch_js/generate_witness.js" "{{BUILD}}/tree_update_batch_js/tree_update_batch.wasm" "$INPUT" "{{BUILD}}/tree_update_batch_witness.wtns"; \
    echo "==> Prove (groth16)"; \
    npx snarkjs groth16 prove "{{BUILD}}/tree_update_batch_final.zkey" "{{BUILD}}/tree_update_batch_witness.wtns" "{{BUILD}}/tree_update_batch_proof.json" "{{BUILD}}/tree_update_batch_public.json"; \
    echo "==> Verify"; \
    npx snarkjs groth16 verify "{{BUILD}}/tree_update_batch_verification_key.json" "{{BUILD}}/tree_update_batch_public.json" "{{BUILD}}/tree_update_batch_proof.json"

# Build everything: 2x2 + tree_update_batch.
all-tree: compile compile-batch setup setup-batch

# === rebuild + sync into contracts/ ===

# Build all 2x2 artifacts WITHOUT the contracts/ sync. Used by the
# `package` recipe (publish CI does not have a sibling contracts repo
# checked out). Local circuit authors should prefer `rebuild`, which
# wraps this and also pushes Verifier.sol into ../contracts/src/verifiers/.
#
# WARNING: re-runs the prototype single-contributor ceremony (INSECURE
# — see `setup` recipe). Existing proofs become invalid after.
build-artifacts: compile setup

# Full rebuild after circuit edits: recompile -> trusted setup -> sync
# Verifier.sol into contracts/src/verifiers/. Use after changes to
# 2x2.circom or any lib/*.circom; this regenerates 2x2.r1cs, 2x2.wasm,
# 2x2_final.zkey, verification_key.json, and Verifier.sol, then copies
# the verifier into contracts/.
rebuild: build-artifacts
    @echo "==> Syncing Verifier.sol -> {{CONTRACTS_VERIFIER}}"
    cp "{{BUILD}}/Verifier.sol" "{{CONTRACTS_VERIFIER}}"
    @just _rebuild-report "2x2" "{{BUILD}}/2x2.r1cs" "{{BUILD}}/2x2_js/2x2.wasm" "{{BUILD}}/2x2_final.zkey" "{{BUILD}}/verification_key.json" "{{CONTRACTS_VERIFIER}}"

# Full rebuild for tree_update_batch circuit + sync TreeUpdateBatchVerifier.sol
# into contracts/src/verifiers/.
rebuild-batch: compile-batch setup-batch
    @echo "==> Patching contract name (Groth16Verifier -> TreeUpdateBatchGroth16Verifier)"
    @sed 's/contract Groth16Verifier/contract TreeUpdateBatchGroth16Verifier/' "{{BUILD}}/TreeUpdateBatchVerifier.sol" > "{{BUILD}}/TreeUpdateBatchVerifier.patched.sol"
    @echo "==> Syncing TreeUpdateBatchVerifier.sol -> {{CONTRACTS_TREE_BATCH_VERIFIER}}"
    cp "{{BUILD}}/TreeUpdateBatchVerifier.patched.sol" "{{CONTRACTS_TREE_BATCH_VERIFIER}}"
    @just _rebuild-report "tree_update_batch" "{{BUILD}}/tree_update_batch.r1cs" "{{BUILD}}/tree_update_batch_js/tree_update_batch.wasm" "{{BUILD}}/tree_update_batch_final.zkey" "{{BUILD}}/tree_update_batch_verification_key.json" "{{CONTRACTS_TREE_BATCH_VERIFIER}}"

# === test + lint ===

# Run the TypeScript test suite (mocha + circom_tester).
test:
    npm test

# Run unit tests, excluding fuzz suite (covered by `just test-fuzz`).
test-unit:
    npm run test:unit

# Run heavy fuzz suite.
test-fuzz:
    npm run test:fuzz

# Static analysis via Trail of Bits circomspect. Install: cargo install circomspect
#
# Suppressed analysis passes (each reviewed; rationale below). To audit, run
# without `--allow` flags and confirm every reported site falls under one of
# the documented categories. Re-evaluate whenever the listed sites change.
#
#   CS0005 signal-assignment           HashToBit: `inv <-- 1/hash; inv*hash===1`
#   CS0015 unconstrained-division      is the canonical non-zero-hash check.
#   CS0017 under-constrained-signal    `inv` is fully constrained by the
#                                      product equation (any prover assignment
#                                      satisfying `inv*hash===1` forces
#                                      inv = hash^{-1}; hash=0 is unsatisfiable).
#
#   CS0010 non-strict-binary-conversion
#       Each Num2Bits site uses n < 254 bits, so 2^n < p and no aliasing is
#       possible (the field-element decomposition is unique).
#       Sites: balance.circom / asset_gen.circom (64 bits),
#              value_commit.circom (253 bits), common.circom (2 bits),
#              tree_update_batch.circom (COUNT_BITS=3; 2*DEPTH bits,
#              DEPTH<=32 ⇒ n<=64).
#
#   CS0014 unconstrained-less-than
#       tree_update_batch.circom `LessThan(COUNT_BITS+1)` with inputs `i`
#       (compile-time loop var, becomes a constant in R1CS) and `actual_count`
#       (bounded by `Num2Bits(COUNT_BITS=3)` at line ~93, so <= 2^3).
#
#   CS0018 unused-output-signal
#       Intentional: components are instantiated for their internal constraints,
#       not all outputs are propagated. Sites:
#         - SpentNote/OutputNote: `vc_dep.rH` only the cv branch's rH is
#           threaded out; deposit-branch rH is bound internally by ValueCommit.
#         - QuaternaryInsertLevel/MerkleLevel4: `PathIndexSelectors.bits`
#           selectors output is consumed; `bits` is the redundant view.
#         - TreeUpdateBatch: `insA[i].root` unused (only frontier threaded;
#           insB root feeds the mux). Costs extra constraints but is sound.
lint:
    @command -v circomspect >/dev/null || { echo "circomspect not found. Install: cargo install circomspect"; exit 1; }
    circomspect "{{ROOT}}/src" -L "{{ROOT}}/node_modules" \
        --allow CS0005 --allow CS0010 --allow CS0014 \
        --allow CS0015 --allow CS0017 --allow CS0018

clean:
    rm -rf "{{BUILD}}"

# === lean proofs ===

# Elaborate and kernel-check every proof; also runs the namespace-wide axiom guard.
lean-build:
    cd "{{ROOT}}/lean" && lake build

# Everything CI runs against the Lean development.
lean-check:
    cd "{{ROOT}}/lean" && ./scripts/check-all.sh

# Regenerate the two golden files under lean/expected/ after an intentional change.
lean-update:
    cd "{{ROOT}}/lean" && ./scripts/check-axioms.sh --update && ./scripts/dump-layout.sh --update

# === package ===

# Stage and verify the runtime artifact bundle for npm publish.
# Copies the witness wasm out of `build/2x2_js/` to a flat `build/2x2.wasm`
# so the package `files` whitelist (and `exports` subpath map) resolves
# without shipping the redundant `2x2_js/` glue. Then runs
# `scripts/check-artifacts.mjs` to assert sizes + SHA-256 match
# `release-manifest.json`.
#
# Depends on `build-artifacts` (NOT `rebuild`) so the publish workflow
# does not require a sibling contracts/ checkout for the Verifier.sol
# sync step.
package: build-artifacts
    @echo "==> Staging build/2x2.wasm for publish"
    cp "{{BUILD}}/2x2_js/2x2.wasm" "{{BUILD}}/2x2.wasm"
    @ls -lh "{{BUILD}}/2x2.wasm" "{{BUILD}}/2x2_final.zkey" "{{BUILD}}/verification_key.json"
    @echo "==> Verifying artifacts against release-manifest.json"
    node scripts/check-artifacts.mjs

# === internal helpers (prefixed `_`) ===

_fetch-ptau file:
    mkdir -p "{{PTAU_DIR}}"
    @if [ ! -f "{{PTAU_DIR}}/{{file}}" ]; then \
        echo "==> Downloading {{file}}"; \
        curl -L "{{PTAU_URL_BASE}}/{{file}}" -o "{{PTAU_DIR}}/{{file}}"; \
    fi

_rebuild-report name r1cs wasm zkey vk verifier:
    @echo "==> rebuild ({{name}}) complete"
    @echo "    r1cs:        {{r1cs}}"
    @echo "    wasm:        {{wasm}}"
    @echo "    zkey:        {{zkey}}"
    @echo "    vk:          {{vk}}"
    @echo "    verifier:    {{verifier}}"
