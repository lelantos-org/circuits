set shell := ["bash", "-ceuo", "pipefail"]

# === paths ===
ROOT := justfile_directory()
BUILD := ROOT / "build"
PTAU_DIR := ROOT / "ptau"
PTAU_URL_BASE := "https://storage.googleapis.com/zkevm/ptau"
# All three shapes size to `cirPower = 16`, so one ptau serves the whole repo.
# snarkjs picks the domain from `nConstraints + nPubInputs + nOutputs`, which
# caps a 2^16 ceremony at 65,533 constraints — see `budget` below.
PTAU16 := "powersOfTau28_hez_final_16.ptau"

# Sync targets in sibling contracts/ checkout. Updated for new src/ layout
# (verifiers grouped under src/verifiers/).
CONTRACTS_VERIFIER := ROOT / ".." / "contracts" / "src" / "verifiers" / "Verifier.sol"
CONTRACTS_TREE_BATCH_VERIFIER := ROOT / ".." / "contracts" / "src" / "verifiers" / "TreeUpdateBatchVerifier.sol"

default:
    @just --list

# === 2x2 circuit ===

# Compile 2x2.circom -> r1cs + wasm + sym, print constraint count.
compile: (_compile "2x2")

# Phase-2 trusted setup (single-contributor; INSECURE — prototype only).
setup:
    just _fetch-ptau "{{PTAU16}}"
    echo "==> Phase-2 setup"
    npx snarkjs groth16 setup "{{BUILD}}/2x2.r1cs" "{{PTAU_DIR}}/{{PTAU16}}" "{{BUILD}}/2x2_0.zkey"
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

# Compile, run the prototype ceremony, then prove and verify one witness.
all: compile setup prove

# === 3x3 circuit — the deployed transact shape ===
#
# `Transact(10, 3, 3)`: 3 shielded inputs x 3 shielded outputs. Constraint
# counts are in budget.json. Published as a package artifact and wired on-chain:
# `PubInputs.sol` carries the 42-slot compress for this layout,
# `TRANSACT_IN = TRANSACT_OUT = 3`, and the exported verifier is
# contracts/src/verifiers/Verifier.sol. Use `rebuild-3x3` to regenerate and sync
# it. See src/3x3.circom.

# Compile 3x3.circom -> r1cs + wasm + sym, print constraint count.
compile-3x3: (_compile "3x3")

# Phase-2 trusted setup for 3x3 (single-contributor; INSECURE — prototype only).
setup-3x3:
    just _fetch-ptau "{{PTAU16}}"
    echo "==> Phase-2 setup (3x3)"
    npx snarkjs groth16 setup "{{BUILD}}/3x3.r1cs" "{{PTAU_DIR}}/{{PTAU16}}" "{{BUILD}}/3x3_0.zkey"
    echo "==> Single contribution (PROTOTYPE ONLY)"
    npx snarkjs zkey contribute "{{BUILD}}/3x3_0.zkey" "{{BUILD}}/3x3_final.zkey" --name="prototype-contributor" -e="$(openssl rand -hex 32)"
    echo "==> Export verification key"
    npx snarkjs zkey export verificationkey "{{BUILD}}/3x3_final.zkey" "{{BUILD}}/3x3_verification_key.json"
    echo "==> Export Solidity verifier"
    npx snarkjs zkey export solidityverifier "{{BUILD}}/3x3_final.zkey" "{{BUILD}}/Verifier3x3.sol"
    # Single quotes, not backticks: this recipe runs under `bash -ceuo pipefail`,
    # where a backtick inside a double-quoted string is command substitution.
    # Backticking `just rebuild-3x3` here made the echo re-invoke this recipe
    # through its own dependency chain, recursing until the job timed out.
    echo "==> Done. Verifier at {{BUILD}}/Verifier3x3.sol — run 'just rebuild-3x3' to sync it"

# Used by `package`, since publish CI has no sibling contracts checkout. Local
# circuit authors should prefer `rebuild-3x3`, which also pushes the verifier
# into contracts/.

# Build all 3x3 artifacts WITHOUT the contracts/ sync.
build-artifacts-3x3: compile-3x3 setup-3x3

# === tree_update_batch circuit ===

# Compile tree_update_batch.circom -> r1cs + wasm + sym, print constraint count.
compile-batch: (_compile "tree_update_batch")

# tree_update_batch at MAX_L=4 has 57,106 constraints and so uses the 2^16 FFT
# domain, with 8,427 constraints of headroom. A leaf slot costs roughly 12k
# constraints, and `just budget` pins the domain so growth past it fails CI
# rather than doubling proving time.
#
# 2x2 (44,406) and 3x3 (65,523) size to the same domain and share this ptau.
# 3x3 clears it by 10 constraints, so a ceremony is also the second line of
# defence: at 65,534 `groth16 setup` fails outright rather than silently
# building a 2^17 zkey.

# Phase-2 trusted setup for tree_update_batch (single-contributor; INSECURE).
setup-batch:
    just _fetch-ptau "{{PTAU16}}"
    echo "==> Phase-2 setup (tree_update_batch)"
    npx snarkjs groth16 setup "{{BUILD}}/tree_update_batch.r1cs" "{{PTAU_DIR}}/{{PTAU16}}" "{{BUILD}}/tree_update_batch_0.zkey"
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

# Never syncs into contracts/: 2x2 is not the deployed transact shape, so
# `build/Verifier.sol` must not reach contracts/src/verifiers/Verifier.sol.
# That path holds the 3x3 verifier, and overwriting it would swap the deployed
# circuit under an unchanged filename.
#
# WARNING: re-runs the prototype single-contributor ceremony (INSECURE — see the
# `setup` recipe). Existing proofs become invalid.

# Compile + trusted setup for 2x2. Never synced into contracts/.
build-artifacts: compile setup

# No contracts/ sync — see `build-artifacts` above, and use `rebuild-3x3` for
# the deployed shape.

# Full rebuild of the 2x2 shape after circuit edits.
rebuild-2x2: build-artifacts
    @just _rebuild-report "2x2" "{{BUILD}}/2x2.r1cs" "{{BUILD}}/2x2_js/2x2.wasm" "{{BUILD}}/2x2_final.zkey" "{{BUILD}}/verification_key.json" "(not synced — 2x2 is not deployed)"

# Full rebuild of the DEPLOYED transact shape after circuit edits: recompile ->
# trusted setup -> sync Verifier3x3.sol into contracts/src/verifiers/Verifier.sol.
# Use after changes to 3x3.circom or any lib/*.circom.

# Full rebuild of the DEPLOYED transact shape, syncing the verifier to contracts/.
rebuild-3x3: build-artifacts-3x3
    @echo "==> Syncing Verifier3x3.sol -> {{CONTRACTS_VERIFIER}}"
    cp "{{BUILD}}/Verifier3x3.sol" "{{CONTRACTS_VERIFIER}}"
    @just _rebuild-report "3x3" "{{BUILD}}/3x3.r1cs" "{{BUILD}}/3x3_js/3x3.wasm" "{{BUILD}}/3x3_final.zkey" "{{BUILD}}/3x3_verification_key.json" "{{CONTRACTS_VERIFIER}}"

# Syncs TreeUpdateBatchVerifier.sol into contracts/src/verifiers/.

# Full rebuild of the tree_update_batch shape after circuit edits.
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

# === constraint budget ===

# Every shape must fit its FFT domain, and its exact count must match
# budget.json — a change lands as a diff a reviewer approves rather than
# drifting silently. Needs the r1cs, so run after `compile*`.

# Check every shape against its constraint budget.
budget:
    @echo "==> Constraint budget"
    NODE_OPTIONS="--import tsx/esm" node "{{ROOT}}/scripts/check-budget.mjs"

# Accept new constraint counts into budget.json. Review the diff.
budget-update:
    NODE_OPTIONS="--import tsx/esm" node "{{ROOT}}/scripts/check-budget.mjs" --update

# === golden vectors ===

# Every `y` is read out of a witness produced by the compiled circuit and
# compared against the TypeScript Horner evaluation; the generator refuses to
# write on disagreement, so these are a circuit contract rather than a
# TypeScript snapshot. Slot names come from
# lean/expected/layout-<shape>.txt, so run `just lean-update` first if the
# layout changed.

# Regenerate vectors/ — the cross-repo contract consumed by @lelantos-org/sdk.
vectors:
    NODE_OPTIONS="--import tsx/esm" node "{{ROOT}}/scripts/gen-vectors.ts"

# Run in CI: a circuit or layout change that was not accompanied by
# `just vectors` fails here.

# Regenerate into a temp dir and diff against the committed files.
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
# Suppressed analysis passes, with the rationale for each below. To audit, run
# without the `--allow` flags and confirm every reported site falls under one of
# these categories. Re-evaluate whenever the listed sites change.
#
#   CS0010 non-strict-binary-conversion
#       Each Num2Bits site uses n < 254 bits, so 2^n < p and no aliasing is
#       possible (the field-element decomposition is unique).
#       Sites: balance.circom / asset_gen.circom (64 bits),
#              value_commit.circom (RCV_BITS = 252), common.circom (2 bits),
#              tree_update_batch.circom (COUNT_BITS = 2; 2*DEPTH bits,
#              DEPTH <= 32 ⇒ n <= 64).
#
#   CS0014 unconstrained-less-than
#       tree_update_batch.circom `LessThan(COUNT_BITS+1)` with inputs `k`
#       (compile-time loop var, becomes a constant in R1CS) and `actual_count`
#       (bounded by `Num2Bits(COUNT_BITS=2)` in step 1, so <= 2^2).
#
#   CS0018 unused-output-signal
#       Intentional: components are instantiated for their internal constraints,
#       not all outputs are propagated. Sites:
#         - SpentNote/OutputNote: `vc_dep.rH` only the cv branch's rH is
#           threaded out; deposit-branch rH is bound internally by ValueCommit.
#         - QuaternaryInsertLevel/MerkleLevel4: `PathIndexSelectors.bits`
#           selectors output is consumed; `bits` is the redundant view.

# Static analysis over src/lib and the top-level circuits (needs circomspect).
lint:
    @command -v circomspect >/dev/null || { echo "circomspect not found. Install: cargo install circomspect"; exit 1; }
    @test -z "$(grep -rl -- '<--' "{{ROOT}}/src/lib" "{{ROOT}}/src"/*.circom || true)" \
        || { echo "a '<--' hint appeared in a linted circuit; review it before waiving CS0005/CS0015/CS0017"; exit 1; }
    circomspect "{{ROOT}}/src/lib" "{{ROOT}}/src"/*.circom -L "{{ROOT}}/node_modules" \
        --allow CS0010 --allow CS0014 --allow CS0018

# Delete build/ — artifacts, keys and verifiers alike.
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

# Complements the Lean proofs, which are about the modeled constraint system,
# whereas Picus reads the R1CS circom emits. Not part of `lean-check` or CI: it
# needs Docker and a 4.5 GB image, built once with:
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

#   just picus                     # 2x2, weak (default) safety
#   just picus 3x3                 # another circuit under src/
#   just picus tree_update_batch 1 # strong safety
#
# The circuit name comes first, so the old `just picus 1` (strong on 2x2) is now
# `just picus 2x2 1`.

# Check one circuit's R1CS for under-constrainedness (needs Docker). STRONG=1 for strong safety.
picus CIRCUIT="2x2" STRONG="":
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
    src="{{ROOT}}/src/{{CIRCUIT}}.circom"
    [ -f "$src" ] || { echo "no such circuit: $src"; exit 1; }
    mkdir -p "{{BUILD}}/picus"
    circom "$src" --r1cs --sym --O0 -o "{{BUILD}}/picus" -l "{{ROOT}}/node_modules"
    code=0
    docker run --rm -v "{{BUILD}}/picus:/data" "$image" \
        ./run-picus --solver z3 --timeout 10000 {{ if STRONG != "" { "--strong" } else { "" } }} /data/{{CIRCUIT}}.r1cs \
        || code=$?
    # Picus signals its verdict through the exit code (picus/exit.rkt): 8 safe, 9 unsafe,
    # 0 unknown. A passing run therefore exits non-zero and has to be translated, or every
    # green check reads as a failure.
    case "$code" in
        8)  echo "==> {{CIRCUIT}}: properly constrained" ;;
        9)  echo "==> {{CIRCUIT}}: UNDER-CONSTRAINED"; exit 1 ;;
        0)  echo "==> {{CIRCUIT}}: unknown — Picus could not decide (timeout or unsupported)"; exit 1 ;;
        *)  echo "==> {{CIRCUIT}}: Picus error (exit $code)"; exit 1 ;;
    esac

# Keeps going after a failing circuit so one under-constrained result does not hide
# the others, then exits non-zero if any failed.

# Run `picus` over every top-level circuit. STRONG=1 for strong safety.
picus-all STRONG="":
    #!/usr/bin/env bash
    set -euo pipefail
    failed=()
    for circuit in 2x2 3x3 tree_update_batch; do
        echo "==> picus: $circuit"
        just picus "$circuit" "{{STRONG}}" || failed+=("$circuit")
    done
    if [ ${#failed[@]} -gt 0 ]; then
        echo "==> picus failed: ${failed[*]}"
        exit 1
    fi
    echo "==> picus: all circuits properly constrained"

# === package ===

# Full rebuild + verify for npm publish. RE-RUNS BOTH CEREMONIES (2x2, 3x3)
# and so invalidates existing proofs — see `package-check` for the gate alone.
# Copies the witness wasm out of `build/2x2_js/` to a flat `build/2x2.wasm`
# so the package `files` whitelist (and `exports` subpath map) resolves
# without shipping the redundant `2x2_js/` glue. Then runs
# `scripts/check-artifacts.ts` to assert sizes + SHA-256 match
# `release-manifest.json`.
#
# Depends on the `build-artifacts*` recipes (NOT `rebuild-3x3`) so the publish
# workflow does not require a sibling contracts/ checkout for the Verifier.sol
# sync step.

# Full rebuild + publish gate. RE-RUNS BOTH CEREMONIES, invalidating existing proofs.
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

# Run the publish gate against whatever is already in build/. No compile, no ceremony.
package-check:
    @echo "==> Staging build/2x2.wasm + build/3x3.wasm (no rebuild)"
    @[ -f "{{BUILD}}/2x2_js/2x2.wasm" ] && cp "{{BUILD}}/2x2_js/2x2.wasm" "{{BUILD}}/2x2.wasm" || echo "    skip: build/2x2_js/2x2.wasm absent"
    @[ -f "{{BUILD}}/3x3_js/3x3.wasm" ] && cp "{{BUILD}}/3x3_js/3x3.wasm" "{{BUILD}}/3x3.wasm" || echo "    skip: build/3x3_js/3x3.wasm absent"
    @echo "==> Verifying artifacts"
    NODE_OPTIONS="--import tsx/esm" node scripts/check-artifacts.ts

# === internal helpers (prefixed `_`) ===

# Compile one src/<circuit>.circom to r1cs + wasm + sym and print its
# constraint count. The three named `compile*` recipes are thin wrappers so the
# flags cannot drift between the shapes — the constraint budget compares them
# against one another.
_compile circuit:
    mkdir -p "{{BUILD}}"
    echo "==> Compiling {{ROOT}}/src/{{circuit}}.circom"
    circom "{{ROOT}}/src/{{circuit}}.circom" --r1cs --wasm --sym -o "{{BUILD}}" -l "{{ROOT}}/node_modules"
    echo "==> Constraint info"
    npx snarkjs r1cs info "{{BUILD}}/{{circuit}}.r1cs"

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
