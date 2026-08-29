set shell := ["bash", "-ceuo", "pipefail"]

# === paths ===
ROOT := justfile_directory()
BUILD := ROOT / "build"
PTAU_DIR := ROOT / "ptau"
PTAU_URL_BASE := "https://storage.googleapis.com/zkevm/ptau"
# Both circuits are on the 2^17 ceremony: Transact(11,4,6) is 100,320 constraints
# and TreeUpdateBatch(11,8) is 113,502, so neither fits 2^16. snarkjs picks the
# domain from `nConstraints + nPubInputs + nOutputs`, which caps a 2^16 ceremony
# at 65,533 constraints — see `budget` below.
#
# PTAU16 is kept because `_setup` takes the ptau as an argument and a future
# smaller circuit would want it; nothing currently references it.
PTAU16 := "powersOfTau28_hez_final_16.ptau"
PTAU17 := "powersOfTau28_hez_final_17.ptau"

# Pinned revision of iden3/circom-witnesscalc, which supplies the relayer's
# native witness calculator. `build-circuit` is deliberately not on crates.io —
# it lives in that repo's `extensions/` and pulls the circom compiler from git —
# so it is installed from a fixed commit rather than a version range.
#
# The relayer's `circom-witnesscalc` dependency must be pinned to this SAME
# revision: the graph format is versioned, and a mismatched reader rejects the
# file with "Invalid magic".
#
# `--locked` below is load-bearing, not hygiene: build-circuit depends on the
# circom compiler crates by *branch* (`master`), so without the committed
# lockfile the install resolves whatever circom is today. It currently fails
# outright that way — circom master has since added a `StatusInput` variant the
# pinned build-circuit does not match on.
CWC_REV := "d48eb7c97857d46b8a75c94ab96f769207263245"
CWC_REPO := "https://github.com/iden3/circom-witnesscalc"
TOOLS := ROOT / ".tools"
BUILD_CIRCUIT := TOOLS / "build-circuit" / "bin" / "build-circuit"

# Sync targets in sibling contracts/ checkout. Updated for new src/ layout
# (verifiers grouped under src/verifiers/).
CONTRACTS_VERIFIER := ROOT / ".." / "contracts" / "src" / "verifiers" / "Verifier.sol"
CONTRACTS_TREE_BATCH_VERIFIER := ROOT / ".." / "contracts" / "src" / "verifiers" / "TreeUpdateBatchVerifier.sol"

default:
    @just --list

# === transact circuit ===
#
# `Transact(11, 4, 6)` — src/4x6.circom. The only transact shape: the three
# narrower ones were removed once 4x6 landed, since each cost a ceremony per
# release and 20-40 MB in every npm install for no unique coverage.

# Compile 4x6.circom -> r1cs + wasm + sym, print constraint count.
compile-4x6: (_compile "4x6")

# Phase-2 trusted setup for 4x6 (single-contributor; INSECURE — prototype only).
setup-4x6: (_setup "4x6" PTAU17)

# Compile + trusted setup for 4x6.
build-artifacts-4x6: compile-4x6 setup-4x6

# === tree_update_batch circuit ===

# Compile tree_update_batch.circom -> r1cs + wasm + sym, print constraint count.
compile-batch: (_compile "tree_update_batch")

# Build the native witness-calculation graph the relayer proves against.
#
# Replaces the circom-emitted wasm witness generator: the relayer evaluates this
# graph in-process instead of running wasm under wasmer.
#
# Two invariants, both enforced below rather than trusted:
#
#   --O1   `_compile` uses circom's default optimisation, but build-circuit
#          defaults to --O2. At --O2 the same source yields 25,426 constraints
#          instead of 57,106, so the graph would index signals the zkey does not
#          have.
#
#   cmp    build-circuit re-runs the circom front end, so its constraint system
#          is only *believed* to match the one the zkey was set up against.
#          Emitting its R1CS and diffing it against `_compile`'s output turns
#          that belief into a build failure. A graph that disagrees with the
#          zkey produces witnesses that fail verification at prove time.
#
# Depends on compile-batch for the R1CS to diff against.
build-graph: compile-batch _ensure-build-circuit
    echo "==> Building witness graph (build-circuit @ {{CWC_REV}})"
    "{{BUILD_CIRCUIT}}" "{{ROOT}}/src/tree_update_batch.circom" "{{BUILD}}/tree_update_batch.wcd" \
        -l "{{ROOT}}/node_modules" --O1 --r1cs "{{BUILD}}/tree_update_batch.graph.r1cs"
    echo "==> Checking the graph's constraint system matches the compiled one"
    cmp "{{BUILD}}/tree_update_batch.graph.r1cs" "{{BUILD}}/tree_update_batch.r1cs"
    # The r1cs was emitted only for that diff, and build-circuit drops two
    # signal-map debug files into the working directory.
    rm -f "{{BUILD}}/tree_update_batch.graph.r1cs" \
          "{{ROOT}}/log_input_signals.txt" "{{ROOT}}/log_input_signals_new.txt"
    echo "==> Graph at {{BUILD}}/tree_update_batch.wcd"

# Install the pinned build-circuit into .tools/ unless it is already there.
_ensure-build-circuit:
    @if [ ! -x "{{BUILD_CIRCUIT}}" ]; then \
        echo "==> Installing build-circuit @ {{CWC_REV}} (compiles the circom front end; slow)"; \
        cargo install --git "{{CWC_REPO}}" --rev "{{CWC_REV}}" --locked build-circuit \
            --root "{{TOOLS}}/build-circuit"; \
    fi

# tree_update_batch at MAX_L=8, depth 11 has 113,502 constraints against the 2^17
# domain — 17,570 of headroom, and the tighter of the two circuits. A leaf slot
# costs roughly 12k constraints, so this is what a further widening breaks first;
# `just budget` pins the domain so growth past it fails CI rather than silently
# doubling proving time.
#
# The ceremony is a second line of defence on the same bound: `groth16 setup`
# fails outright when the constraint count exceeds the ptau, rather than building
# against a domain the budget did not sanction.

# On the 2^17 ptau, not 2^16: at MAX_L = 8 and depth 11 this circuit is 113,502
# constraints. It shares the ptau with 4x6 and is the tighter of the two.

# Phase-2 trusted setup for tree_update_batch (single-contributor; INSECURE).
setup-batch: (_setup "tree_update_batch" PTAU17)

# The four snarkjs calls every phase-2 setup makes, written once.
#
# Was copied per shape, which is how `setup-batch` ended up pointing at the 2^16
# ptau after the circuit outgrew it — the kind of drift a shared recipe cannot
# have. `groth16 setup` fails outright when the constraint count exceeds the
# ptau, so a wrong argument here is loud rather than silent.
_setup shape ptau:
    just _fetch-ptau "{{ptau}}"
    echo "==> Phase-2 setup ({{shape}}, {{ptau}})"
    npx snarkjs groth16 setup "{{BUILD}}/{{shape}}.r1cs" "{{PTAU_DIR}}/{{ptau}}" "{{BUILD}}/{{shape}}_0.zkey"
    echo "==> Single contribution (PROTOTYPE ONLY)"
    npx snarkjs zkey contribute "{{BUILD}}/{{shape}}_0.zkey" "{{BUILD}}/{{shape}}_final.zkey" --name="prototype-contributor" -e="$(openssl rand -hex 32)"
    echo "==> Export verification key"
    npx snarkjs zkey export verificationkey "{{BUILD}}/{{shape}}_final.zkey" "{{BUILD}}/{{shape}}_verification_key.json"
    echo "==> Export Solidity verifier"
    npx snarkjs zkey export solidityverifier "{{BUILD}}/{{shape}}_final.zkey" "{{BUILD}}/Verifier_{{shape}}.sol"
    echo "==> Done. Verifier at {{BUILD}}/Verifier_{{shape}}.sol"

# Prove + verify a tree_update_batch witness.
prove-batch input="":
    INPUT="{{ if input == "" { ROOT / "circuits/test/tree_update_batch_input.json" } else { input } }}"; \
    echo "==> Compute witness from $INPUT"; \
    node "{{BUILD}}/tree_update_batch_js/generate_witness.js" "{{BUILD}}/tree_update_batch_js/tree_update_batch.wasm" "$INPUT" "{{BUILD}}/tree_update_batch_witness.wtns"; \
    echo "==> Prove (groth16)"; \
    npx snarkjs groth16 prove "{{BUILD}}/tree_update_batch_final.zkey" "{{BUILD}}/tree_update_batch_witness.wtns" "{{BUILD}}/tree_update_batch_proof.json" "{{BUILD}}/tree_update_batch_public.json"; \
    echo "==> Verify"; \
    npx snarkjs groth16 verify "{{BUILD}}/tree_update_batch_verification_key.json" "{{BUILD}}/tree_update_batch_public.json" "{{BUILD}}/tree_update_batch_proof.json"

# The two are ceremony-paired — a spend's output leaves are inserted by the
# batch circuit, so they share DEPTH.

# Build everything: 4x6 + tree_update_batch.
all-tree: build-artifacts-4x6 compile-batch setup-batch

# === rebuild + sync into contracts/ ===
#
# WARNING: every recipe here re-runs the prototype single-contributor ceremony
# (INSECURE — see `_setup`). Existing proofs and the committed contract fixtures
# become invalid.

# Full rebuild of the transact shape, syncing the verifier into contracts/.
rebuild-4x6: build-artifacts-4x6
    @echo "==> Syncing Verifier_4x6.sol -> {{CONTRACTS_VERIFIER}}"
    cp "{{BUILD}}/Verifier_4x6.sol" "{{CONTRACTS_VERIFIER}}"
    @just _rebuild-report "4x6" "{{BUILD}}/4x6.r1cs" "{{BUILD}}/4x6_js/4x6.wasm" "{{BUILD}}/4x6_final.zkey" "{{BUILD}}/4x6_verification_key.json" "{{CONTRACTS_VERIFIER}}"

# Syncs TreeUpdateBatchVerifier.sol into contracts/src/verifiers/.

# Full rebuild of the tree_update_batch shape after circuit edits.
rebuild-batch: compile-batch setup-batch
    @echo "==> Patching contract name (Groth16Verifier -> TreeUpdateBatchGroth16Verifier)"
    @sed 's/contract Groth16Verifier/contract TreeUpdateBatchGroth16Verifier/' "{{BUILD}}/Verifier_tree_update_batch.sol" > "{{BUILD}}/TreeUpdateBatchVerifier.patched.sol"
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
# build/4x6.r1cs.

# Build the native arm64 Picus image, avoiding the emulated upstream one.
picus-image:
    docker build --platform linux/arm64 -t picus:arm64 \
        -f "{{ROOT}}/docker/picus-arm64.Dockerfile" "{{ROOT}}/docker"

#   just picus                     # 4x6, weak (default) safety
#   just picus tree_update_batch   # the other circuit under src/
#   just picus tree_update_batch 1 # strong safety
#
# The circuit name comes first, so strong safety on the default shape is
# `just picus 4x6 1`.

# Check one circuit's R1CS for under-constrainedness (needs Docker). STRONG=1 for strong safety.
picus CIRCUIT="4x6" STRONG="":
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
    for circuit in 4x6 tree_update_batch; do
        echo "==> picus: $circuit"
        just picus "$circuit" "{{STRONG}}" || failed+=("$circuit")
    done
    if [ ${#failed[@]} -gt 0 ]; then
        echo "==> picus failed: ${failed[*]}"
        exit 1
    fi
    echo "==> picus: all circuits properly constrained"

# === package ===

# Full rebuild + verify for npm publish. RE-RUNS THE TRANSACT CEREMONY and so
# invalidates existing proofs — see `package-check` for the gate alone. Copies
# the witness wasm out of `build/4x6_js/` to a flat `build/4x6.wasm` so the
# package `files` whitelist (and `exports` subpath map) resolves without shipping
# the redundant `4x6_js/` glue. Then runs `scripts/check-artifacts.ts` to assert
# every artifact is present and sized in range.
#
# 4x6 pulls the 2^17 ptau, which `_setup` fetches on demand.
#
# Depends on `build-artifacts-4x6` (NOT `rebuild-4x6`) so the publish workflow
# does not require a sibling contracts/ checkout for the Verifier.sol sync step.

# Full rebuild + publish gate. RE-RUNS THE CEREMONY, invalidating existing proofs.
package: build-artifacts-4x6
    @just package-check

# Stage the flat wasms and run the publish gate against whatever is ALREADY in
# build/ — no compile, no ceremony.
#
# Split out of `package` because that recipe runs a trusted-setup ceremony as a
# side effect. It mints a fresh zkey from fresh entropy, which
# invalidates every proof built against the previous one — including the
# committed fixtures in ../contracts (proof_transfer.json,
# proof_deposit_batch_n1.json). Reaching for `just package` to re-check the gate
# therefore breaks those fixtures silently. Use this instead.
#
# Missing artifacts are left to check-artifacts.ts to report, which names each
# one and how to rebuild it.

# Run the publish gate against whatever is already in build/. No compile, no ceremony.
package-check:
    @echo "==> Staging build/4x6.wasm (no rebuild)"
    @[ -f "{{BUILD}}/4x6_js/4x6.wasm" ] && cp "{{BUILD}}/4x6_js/4x6.wasm" "{{BUILD}}/4x6.wasm" || echo "    skip: build/4x6_js/4x6.wasm absent"
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
