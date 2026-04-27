set shell := ["bash", "-ceuo", "pipefail"]

ROOT := justfile_directory()
BUILD := ROOT / "build"
PTAU_DIR := ROOT / "ptau"
PTAU_FILE := "powersOfTau28_hez_final_17.ptau"
PTAU_URL := "https://storage.googleapis.com/zkevm/ptau/" + PTAU_FILE

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

# Run the TypeScript test suite (mocha + circom_tester).
test:
    npm test

# Generate asset_registry.json (HashToAssetGen for ids 1..3). Override OUT to redirect.
gen-asset-registry OUT=(ROOT / "../contracts/test/fixtures/asset_registry.json"):
    ASSET_REGISTRY_OUT="{{OUT}}" npx ts-node "{{ROOT}}/src/scripts/gen_asset_registry.ts"

# Generate proof_deposit.json fixture (Groth16 deposit proof for MASP.t.sol).
# Requires `compile` + `setup` to have produced build/2x2_js/2x2.wasm and
# build/2x2_final.zkey. Override OUT to redirect.
gen-proof-deposit OUT=(ROOT / "../contracts/test/fixtures/proof_deposit.json"):
    PROOF_DEPOSIT_OUT="{{OUT}}" npx ts-node "{{ROOT}}/src/scripts/gen_proof_deposit.ts"

# Build canonical witness for the LAN benchmark UI (bench/public/input.json).
bench-prepare:
    npx ts-node "{{ROOT}}/bench/prepare.ts"

# Run LAN benchmark webserver on :8787 (override with PORT=).
bench PORT="8787":
    PORT={{PORT}} npx ts-node "{{ROOT}}/bench/server.ts"

clean:
    rm -rf "{{BUILD}}"
