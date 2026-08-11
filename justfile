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

# === 3x3 circuit ===
#
# `Transact(10, 3, 3)` — 3 shielded inputs x 3 shielded outputs (~103k
# constraints, vs ~69k for 2x2; both fit PTAU17). Built and published as a
# package artifact, but NOT wired on-chain: deploying it additionally needs a
# `PubInputs.compress` overload for its 42-slot layout, a Solidity verifier, and
# `TRANSACT_OUT_LEAVES = 3` on the spend path. See src/3x3.circom.

# Compile 3x3.circom -> r1cs + wasm + sym, print constraint count.
compile-3x3:
    mkdir -p "{{BUILD}}"
    echo "==> Compiling {{ROOT}}/src/3x3.circom"
    circom "{{ROOT}}/src/3x3.circom" --r1cs --wasm --sym -o "{{BUILD}}" -l "{{ROOT}}/node_modules"
    echo "==> Constraint info"
    npx snarkjs r1cs info "{{BUILD}}/3x3.r1cs"

# Phase-2 trusted setup for 3x3 (single-contributor; INSECURE — prototype only).
setup-3x3:
    just _fetch-ptau "{{PTAU17}}"
    echo "==> Phase-2 setup (3x3)"
    npx snarkjs groth16 setup "{{BUILD}}/3x3.r1cs" "{{PTAU_DIR}}/{{PTAU17}}" "{{BUILD}}/3x3_0.zkey"
    echo "==> Single contribution (PROTOTYPE ONLY)"
    npx snarkjs zkey contribute "{{BUILD}}/3x3_0.zkey" "{{BUILD}}/3x3_final.zkey" --name="prototype-contributor" -e="$(openssl rand -hex 32)"
    echo "==> Export verification key"
    npx snarkjs zkey export verificationkey "{{BUILD}}/3x3_final.zkey" "{{BUILD}}/3x3_verification_key.json"
    echo "==> Export Solidity verifier"
    npx snarkjs zkey export solidityverifier "{{BUILD}}/3x3_final.zkey" "{{BUILD}}/Verifier3x3.sol"
    echo "==> Done. Verifier at {{BUILD}}/Verifier3x3.sol (not synced to contracts/)"

# Build all 3x3 artifacts. No contracts/ sync — 3x3 is not deployed on-chain.
build-artifacts-3x3: compile-3x3 setup-3x3

# === tree_update_batch circuit ===

# Compile tree_update_batch.circom -> r1cs + wasm + sym, print constraint count.
compile-batch:
    mkdir -p "{{BUILD}}"
    echo "==> Compiling {{ROOT}}/src/tree_update_batch.circom"
    circom "{{ROOT}}/src/tree_update_batch.circom" --r1cs --wasm --sym -o "{{BUILD}}" -l "{{ROOT}}/node_modules"
    echo "==> Constraint info"
    npx snarkjs r1cs info "{{BUILD}}/tree_update_batch.r1cs"

# Phase-2 trusted setup for tree_update_batch (single-contributor; INSECURE).
# tree_update_batch (MAX_L=16) has ~253k constraints, requires ptau_20 (~3GB).
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

# === golden vectors ===

# Regenerate vectors/ — the cross-repo contract consumed by @lelantos-org/sdk.
#
# Every `y` is read out of a witness produced by the compiled circuit and
# compared against the TypeScript Horner evaluation; the generator refuses to
# write if they disagree. That is what makes these a circuit contract rather
# than a TS-to-TS snapshot. Slot names come from lean/expected/layout-2x2.txt,
# so run `just lean-update` first if the layout changed.
vectors:
    NODE_OPTIONS="--import tsx/esm" node "{{ROOT}}/scripts/gen-vectors.ts"

# Regenerate into a temp dir and diff against the committed files.
# Run in CI: a circuit or layout change that was not accompanied by
# `just vectors` fails here.
vectors-check:
    #!/usr/bin/env bash
    set -euo pipefail
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    NODE_OPTIONS="--import tsx/esm" node "{{ROOT}}/scripts/gen-vectors.ts" "$tmp"
    if ! diff -u -r "{{ROOT}}/vectors" "$tmp"; then
        echo
        echo "vectors/ is stale. Regenerate with: just vectors"
        exit 1
    fi
    echo "==> vectors/ up to date"

# Static analysis via Trail of Bits circomspect. Install: cargo install circomspect
#
# Scope is `src/lib/` plus the top-level `src/*.circom` entry points. The tree
# carries no `<--`, so the CS0005 / CS0015 / CS0017 passes (signal-assignment,
# unconstrained-division, under-constrained-signal) run live on every compiled
# circuit instead of being waived tree-wide. Re-check
# `grep -rn '<--' src/lib src/*.circom` before adding any waiver back.
#
# Suppressed analysis passes (each reviewed; rationale below). To audit, run
# without `--allow` flags and confirm every reported site falls under one of
# the documented categories. Re-evaluate whenever the listed sites change.
#
#   CS0010 non-strict-binary-conversion
#       Each Num2Bits site uses n < 254 bits, so 2^n < p and no aliasing is
#       possible (the field-element decomposition is unique).
#       Sites: balance.circom / asset_gen.circom (64 bits),
#              value_commit.circom (253 bits), common.circom (2 bits),
#              tree_update_batch.circom (COUNT_BITS=4; 2*DEPTH bits,
#              DEPTH<=32 ⇒ n<=64).
#
#   CS0014 unconstrained-less-than
#       tree_update_batch.circom `LessThan(COUNT_BITS+1)` with inputs `k`
#       (compile-time loop var, becomes a constant in R1CS) and `actual_count`
#       (bounded by `Num2Bits(COUNT_BITS=4)` in step 1, so <= 2^4).
#
#   CS0018 unused-output-signal
#       Intentional: components are instantiated for their internal constraints,
#       not all outputs are propagated. Sites:
#         - SpentNote/OutputNote: `vc_dep.rH` only the cv branch's rH is
#           threaded out; deposit-branch rH is bound internally by ValueCommit.
#         - QuaternaryInsertLevel/MerkleLevel4: `PathIndexSelectors.bits`
#           selectors output is consumed; `bits` is the redundant view.
#       TreeUpdateBatch no longer appears here: with one insert per leaf,
#       every `ins[k].root` feeds the running-root mux.
lint:
    @command -v circomspect >/dev/null || { echo "circomspect not found. Install: cargo install circomspect"; exit 1; }
    @test -z "$(grep -rl -- '<--' "{{ROOT}}/src/lib" "{{ROOT}}/src"/*.circom || true)" \
        || { echo "a '<--' hint appeared in a linted circuit; review it before waiving CS0005/CS0015/CS0017"; exit 1; }
    circomspect "{{ROOT}}/src/lib" "{{ROOT}}/src"/*.circom -L "{{ROOT}}/node_modules" \
        --allow CS0010 --allow CS0014 --allow CS0018

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

# Answers a question the Lean proofs cannot: they are about the *modeled* constraint
# system, while Picus reads the R1CS circom actually emitted. Not part of `lean-check`
# or CI — it needs Docker and a 4.5 GB image, built once with:
#
#   docker build -t picus:local https://github.com/Veridise/Picus.git
#
# On arm64 that image runs under emulation (upstream publishes amd64 only), so `just
# picus-image` builds a native one instead and `picus` prefers it when present.
#
# Picus recommends --O0 input, so this compiles a separate artifact rather than reusing
# build/2x2.r1cs.

# Build the native arm64 Picus image, avoiding the emulated upstream one.
picus-image:
    docker build --platform linux/arm64 -t picus:arm64 \
        -f "{{ROOT}}/docker/picus-arm64.Dockerfile" "{{ROOT}}/docker"

# Check the compiled R1CS for under-constrainedness (needs Docker). STRONG=1 for strong safety.
picus STRONG="":
    #!/usr/bin/env bash
    set -euo pipefail
    command -v docker >/dev/null || { echo "docker not found"; exit 1; }
    if docker image inspect picus:arm64 >/dev/null 2>&1; then
        image=picus:arm64
    elif docker image inspect picus:local >/dev/null 2>&1; then
        image=picus:local
    else
        echo "no Picus image. Build one: just picus-image (native arm64)"
        echo "  or: docker build -t picus:local https://github.com/Veridise/Picus.git"
        exit 1
    fi
    mkdir -p "{{BUILD}}/picus"
    circom "{{ROOT}}/src/2x2.circom" --r1cs --sym --O0 -o "{{BUILD}}/picus" -l "{{ROOT}}/node_modules"
    docker run --rm -v "{{BUILD}}/picus:/data" "$image" \
        ./run-picus --solver z3 --timeout 10000 {{ if STRONG != "" { "--strong" } else { "" } }} /data/2x2.r1cs

# === package ===

# Full rebuild + verify for npm publish. RE-RUNS BOTH CEREMONIES (2x2, 3x3)
# and so invalidates existing proofs — see `package-check` for the gate alone.
# Copies the witness wasm out of `build/2x2_js/` to a flat `build/2x2.wasm`
# so the package `files` whitelist (and `exports` subpath map) resolves
# without shipping the redundant `2x2_js/` glue. Then runs
# `scripts/check-artifacts.ts` to assert sizes + SHA-256 match
# `release-manifest.json`.
#
# Depends on `build-artifacts` (NOT `rebuild`) so the publish workflow
# does not require a sibling contracts/ checkout for the Verifier.sol
# sync step.
package: build-artifacts build-artifacts-3x3
    @just package-check

# Stage the flat wasms and run the publish gate against whatever is ALREADY in
# build/ — no compile, no ceremony.
#
# Split out of `package` because that recipe runs two trusted-setup ceremonies as
# a side effect (2x2 and 3x3). Each mints a fresh zkey from fresh entropy, which
# invalidates every proof built against the previous one — including the
# committed fixtures in ../contracts (proof_transfer.json,
# proof_deposit_batch_n1.json). Reaching for `just package` to re-check the gate
# therefore breaks those fixtures silently. Use this instead.
#
# Missing artifacts are left to check-artifacts.ts to report, which names each
# one and how to rebuild it.
package-check:
    @echo "==> Staging build/2x2.wasm + build/3x3.wasm (no rebuild)"
    @[ -f "{{BUILD}}/2x2_js/2x2.wasm" ] && cp "{{BUILD}}/2x2_js/2x2.wasm" "{{BUILD}}/2x2.wasm" || echo "    skip: build/2x2_js/2x2.wasm absent"
    @[ -f "{{BUILD}}/3x3_js/3x3.wasm" ] && cp "{{BUILD}}/3x3_js/3x3.wasm" "{{BUILD}}/3x3.wasm" || echo "    skip: build/3x3_js/3x3.wasm absent"
    @echo "==> Verifying artifacts"
    NODE_OPTIONS="--import tsx/esm" node scripts/check-artifacts.ts

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
