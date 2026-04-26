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
    echo "==> Compiling {{ROOT}}/circuits/2x2.circom"
    circom "{{ROOT}}/circuits/2x2.circom" --r1cs --wasm --sym -o "{{BUILD}}" -l "{{ROOT}}/node_modules"
    echo "==> Constraint info"
    snarkjs r1cs info "{{BUILD}}/2x2.r1cs"

# Phase-2 trusted setup (single-contributor; INSECURE — prototype only).
setup:
    mkdir -p "{{PTAU_DIR}}"
    if [ ! -f "{{PTAU_DIR}}/{{PTAU_FILE}}" ]; then \
        echo "==> Downloading {{PTAU_FILE}}"; \
        curl -L "{{PTAU_URL}}" -o "{{PTAU_DIR}}/{{PTAU_FILE}}"; \
    fi
    echo "==> Phase-2 setup"
    snarkjs groth16 setup "{{BUILD}}/2x2.r1cs" "{{PTAU_DIR}}/{{PTAU_FILE}}" "{{BUILD}}/2x2_0.zkey"
    echo "==> Single contribution (PROTOTYPE ONLY)"
    snarkjs zkey contribute "{{BUILD}}/2x2_0.zkey" "{{BUILD}}/2x2_final.zkey" --name="prototype-contributor" -e="$(openssl rand -hex 32)"
    echo "==> Export verification key"
    snarkjs zkey export verificationkey "{{BUILD}}/2x2_final.zkey" "{{BUILD}}/verification_key.json"
    echo "==> Export Solidity verifier"
    snarkjs zkey export solidityverifier "{{BUILD}}/2x2_final.zkey" "{{BUILD}}/Verifier.sol"
    echo "==> Done. Verifier at {{BUILD}}/Verifier.sol"

# Prove + verify a single witness from input.json.
prove input="":
    INPUT="{{ if input == "" { ROOT / "circuits/test/input.json" } else { input } }}"; \
    echo "==> Compute witness from $INPUT"; \
    node "{{BUILD}}/2x2_js/generate_witness.js" "{{BUILD}}/2x2_js/2x2.wasm" "$INPUT" "{{BUILD}}/witness.wtns"; \
    echo "==> Prove (groth16)"; \
    snarkjs groth16 prove "{{BUILD}}/2x2_final.zkey" "{{BUILD}}/witness.wtns" "{{BUILD}}/proof.json" "{{BUILD}}/public.json"; \
    echo "==> Verify"; \
    snarkjs groth16 verify "{{BUILD}}/verification_key.json" "{{BUILD}}/public.json" "{{BUILD}}/proof.json"

all: compile setup prove

# Run the TypeScript test suite (mocha + circom_tester).
test:
    npm test

clean:
    rm -rf "{{BUILD}}"
