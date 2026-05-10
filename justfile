set shell := ["bash", "-ceuo", "pipefail"]

ROOT := justfile_directory()
BUILD := ROOT / "build"
PTAU_DIR := ROOT / "ptau"
PTAU_FILE := "powersOfTau28_hez_final_17.ptau"
PTAU_URL := "https://storage.googleapis.com/zkevm/ptau/" + PTAU_FILE
CONTRACTS_VERIFIER := ROOT / ".." / "contracts" / "src" / "Verifier.sol"
CONTRACTS_TREE_BATCH_VERIFIER := ROOT / ".." / "contracts" / "src" / "TreeUpdateBatchVerifier.sol"

default:
    @just --list

# Compile 2x2.circom -> r1cs + wasm + sym, print constraint count.
compile:
    mkdir -p "{{BUILD}}"
    echo "==> Compiling {{ROOT}}/src/2x2.circom"
    circom "{{ROOT}}/src/2x2.circom" --r1cs --wasm --sym -o "{{BUILD}}" -l "{{ROOT}}/node_modules"
    echo "==> Constraint info"
    npx snarkjs r1cs info "{{BUILD}}/2x2.r1cs"

# Phase-2 trusted setup (single-contributor; INSECURE — prototype only).
setup:
    mkdir -p "{{PTAU_DIR}}"
    if [ ! -f "{{PTAU_DIR}}/{{PTAU_FILE}}" ]; then \
        echo "==> Downloading {{PTAU_FILE}}"; \
        curl -L "{{PTAU_URL}}" -o "{{PTAU_DIR}}/{{PTAU_FILE}}"; \
    fi
    echo "==> Phase-2 setup"
    npx snarkjs groth16 setup "{{BUILD}}/2x2.r1cs" "{{PTAU_DIR}}/{{PTAU_FILE}}" "{{BUILD}}/2x2_0.zkey"
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

# Compile tree_update_batch.circom -> r1cs + wasm + sym, print constraint count.
compile-batch:
    mkdir -p "{{BUILD}}"
    echo "==> Compiling {{ROOT}}/src/tree_update_batch.circom"
    circom "{{ROOT}}/src/tree_update_batch.circom" --r1cs --wasm --sym -o "{{BUILD}}" -l "{{ROOT}}/node_modules"
    echo "==> Constraint info"
    npx snarkjs r1cs info "{{BUILD}}/tree_update_batch.r1cs"

# Phase-2 trusted setup for tree_update_batch (single-contributor; INSECURE).
# tree_update_batch (MAX_N=16) has ~547k constraints, requires ptau_20 (~3GB).
setup-batch:
    mkdir -p "{{PTAU_DIR}}"
    if [ ! -f "{{PTAU_DIR}}/powersOfTau28_hez_final_20.ptau" ]; then \
        echo "==> Downloading powersOfTau28_hez_final_20.ptau (~3GB)"; \
        curl -L "https://storage.googleapis.com/zkevm/ptau/powersOfTau28_hez_final_20.ptau" -o "{{PTAU_DIR}}/powersOfTau28_hez_final_20.ptau"; \
    fi
    echo "==> Phase-2 setup (tree_update_batch)"
    npx snarkjs groth16 setup "{{BUILD}}/tree_update_batch.r1cs" "{{PTAU_DIR}}/powersOfTau28_hez_final_20.ptau" "{{BUILD}}/tree_update_batch_0.zkey"
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

# Full rebuild for tree_update_batch circuit + sync TreeUpdateBatchVerifier.sol into contracts/src.
rebuild-batch: compile-batch setup-batch
    @echo "==> Patching contract name (Groth16Verifier -> TreeUpdateBatchGroth16Verifier)"
    @sed 's/contract Groth16Verifier/contract TreeUpdateBatchGroth16Verifier/' "{{BUILD}}/TreeUpdateBatchVerifier.sol" > "{{BUILD}}/TreeUpdateBatchVerifier.patched.sol"
    @echo "==> Syncing TreeUpdateBatchVerifier.sol -> {{CONTRACTS_TREE_BATCH_VERIFIER}}"
    cp "{{BUILD}}/TreeUpdateBatchVerifier.patched.sol" "{{CONTRACTS_TREE_BATCH_VERIFIER}}"
    @echo "==> rebuild-batch complete"
    @echo "    r1cs:        {{BUILD}}/tree_update_batch.r1cs"
    @echo "    wasm:        {{BUILD}}/tree_update_batch_js/tree_update_batch.wasm"
    @echo "    zkey:        {{BUILD}}/tree_update_batch_final.zkey"
    @echo "    vk:          {{BUILD}}/tree_update_batch_verification_key.json"
    @echo "    verifier:    {{CONTRACTS_TREE_BATCH_VERIFIER}}"

# Build everything: 2x2 + tree_update_batch.
all-tree: compile compile-batch setup setup-batch

# Full rebuild after circuit edits: recompile -> trusted setup -> sync Verifier.sol
# into contracts/src. Use after changes to 2x2.circom or any lib/*.circom; this
# regenerates 2x2.r1cs, 2x2.wasm, 2x2_final.zkey, verification_key.json, and
# Verifier.sol, then copies the verifier into contracts/.
#
# WARNING: re-runs the prototype single-contributor ceremony (INSECURE — see
# `setup` recipe). Existing proofs become invalid after this command.
rebuild: compile setup
    @echo "==> Syncing Verifier.sol -> {{CONTRACTS_VERIFIER}}"
    cp "{{BUILD}}/Verifier.sol" "{{CONTRACTS_VERIFIER}}"
    @echo "==> rebuild complete"
    @echo "    r1cs:        {{BUILD}}/2x2.r1cs"
    @echo "    wasm:        {{BUILD}}/2x2_js/2x2.wasm"
    @echo "    zkey:        {{BUILD}}/2x2_final.zkey"
    @echo "    vk:          {{BUILD}}/verification_key.json"
    @echo "    verifier:    {{CONTRACTS_VERIFIER}}"

# Run the TypeScript test suite (mocha + circom_tester).
test:
    npm test

# Static analysis via Trail of Bits circomspect. Install: cargo install circomspect
lint:
    @command -v circomspect >/dev/null || { echo "circomspect not found. Install: cargo install circomspect"; exit 1; }
    circomspect "{{ROOT}}/src" -L "{{ROOT}}/node_modules"

clean:
    rm -rf "{{BUILD}}"

# Stage and verify the runtime artifact bundle for npm publish.
# Copies the witness wasm out of `build/2x2_js/` to a flat `build/2x2.wasm`
# so the package `files` whitelist (and `exports` subpath map) resolves
# without shipping the redundant `2x2_js/` glue. Then runs
# `scripts/check-artifacts.mjs` to assert sizes + SHA-256 match
# `release-manifest.json`.
package: rebuild
    @echo "==> Staging build/2x2.wasm for publish"
    cp "{{BUILD}}/2x2_js/2x2.wasm" "{{BUILD}}/2x2.wasm"
    @ls -lh "{{BUILD}}/2x2.wasm" "{{BUILD}}/2x2_final.zkey" "{{BUILD}}/verification_key.json"
    @echo "==> Verifying artifacts against release-manifest.json"
    node scripts/check-artifacts.mjs
