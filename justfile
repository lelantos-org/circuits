set shell := ["bash", "-ceuo", "pipefail"]

# === paths ===
ROOT := justfile_directory()
BUILD := ROOT / "build"
PTAU_DIR := ROOT / "ptau"
# Byte-identical copies of the Hermez ptau files, as unauthenticated release assets.
PTAU_URL_BASE := "https://github.com/lelantos-org/ptau/releases/download/hermez"
# Transact(11,4,6) is 28,775 constraints and TreeUpdateBatch(11,8) is 16,802.
# Both need a 2^15 domain and are set up from the 2^16 ceremony file, which
# serves any domain up to its own. snarkjs sizes the domain from
# `nConstraints + nPubInputs + nOutputs`, capping 2^15 at 32,764 constraints and
# 2^16 at 65,532.
PTAU16 := "powersOfTau28_hez_final_16.ptau"

# Verified on every fetch, including cache hits. snarkjs reports a truncated or
# substituted ptau only as `Invalid File format` late in setup.
PTAU16_SHA := "1c401abb57c9ce531370f3015c3e75c0892e0f32b8b1e94ace0f6682d9695922"

# Optimization level of the shipped constraint systems. `--O2` substitutes every
# linear constraint away; circom's default, `--O1`, keeps them. `_compile`,
# `build-graph` and test/lib/constants.ts must agree.
CIRCOM_OPT := "--O2"

# Pinned iden3/circom-witnesscalc revision; `build-circuit` is not on crates.io.
# The relayer's `circom-witnesscalc` dependency must use the same revision: a
# mismatched graph reader fails with "Invalid magic". Installed with `--locked`
# because build-circuit depends on the circom crates by branch.
CWC_REV := "d48eb7c97857d46b8a75c94ab96f769207263245"
CWC_REPO := "https://github.com/iden3/circom-witnesscalc"
TOOLS := ROOT / ".tools"
BUILD_CIRCUIT := TOOLS / "build-circuit" / "bin" / "build-circuit"

# Sync targets in the sibling contracts/ checkout.
CONTRACTS_VERIFIER := ROOT / ".." / "contracts" / "src" / "verifiers" / "Verifier.sol"
CONTRACTS_TREE_BATCH_VERIFIER := ROOT / ".." / "contracts" / "src" / "verifiers" / "TreeUpdateBatchVerifier.sol"

default:
    @just --list

# === transact circuit ===
#
# `Transact(11, 4, 6)` — src/4x6.circom, the only published transact shape.

# Compile 4x6.circom -> r1cs + wasm + sym, print constraint count.
compile-4x6: (_compile "4x6")

# Phase-2 trusted setup for 4x6 (single-contributor; insecure, not for production).
setup-4x6: (_setup "4x6" PTAU16)

# Compile + trusted setup for 4x6.
build-artifacts-4x6: compile-4x6 setup-4x6

# === tree_update_batch circuit ===

# Compile tree_update_batch.circom -> r1cs + wasm + sym, print constraint count.
compile-batch: (_compile "tree_update_batch")

# build-circuit runs at `_compile`'s optimization level, so the two number
# signals identically. `cmp` checks the graph's R1CS against `_compile`'s: a
# graph that disagrees with the zkey produces witnesses that fail verification.

# Build the native witness-calculation graph the relayer proves against.
build-graph: compile-batch _ensure-build-circuit
    echo "==> Building witness graph (build-circuit @ {{CWC_REV}})"
    "{{BUILD_CIRCUIT}}" "{{ROOT}}/src/tree_update_batch.circom" "{{BUILD}}/tree_update_batch.wcd" \
        -l "{{ROOT}}/node_modules" {{CIRCOM_OPT}} --r1cs "{{BUILD}}/tree_update_batch.graph.r1cs"
    echo "==> Checking the graph's constraint system matches the compiled one"
    cmp "{{BUILD}}/tree_update_batch.graph.r1cs" "{{BUILD}}/tree_update_batch.r1cs"
    # The r1cs is emitted only for the comparison; build-circuit also writes two
    # signal-map debug files into the working directory.
    rm -f "{{BUILD}}/tree_update_batch.graph.r1cs" \
          "{{ROOT}}/log_input_signals.txt" "{{ROOT}}/log_input_signals_new.txt"
    echo "==> Graph at {{BUILD}}/tree_update_batch.wcd"

# The install needs `protoc` on PATH; without it prost-build fails with a
# dependency compile error.

# Install the pinned build-circuit into .tools/ unless it is already there.
_ensure-build-circuit:
    @if [ ! -x "{{BUILD_CIRCUIT}}" ]; then \
        if ! command -v protoc >/dev/null 2>&1; then \
            echo "error: protoc not found; build-circuit needs it to compile its protobuf schema." >&2; \
            echo "  macOS:  brew install protobuf" >&2; \
            echo "  Debian: apt-get install -y protobuf-compiler" >&2; \
            exit 1; \
        fi; \
        echo "==> Installing build-circuit @ {{CWC_REV}} (compiles the circom front end; slow)"; \
        cargo install --git "{{CWC_REPO}}" --rev "{{CWC_REV}}" --locked build-circuit \
            --root "{{TOOLS}}/build-circuit"; \
    fi

# Phase-2 trusted setup for tree_update_batch (single-contributor; insecure).
setup-batch: (_setup "tree_update_batch" PTAU16)

# Phase-2 setup shared by every shape. Fails when the constraint count exceeds the ptau.
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

# The two circuits share DEPTH: the batch circuit inserts a spend's output leaves.

# Build everything: 4x6 + tree_update_batch.
all-tree: build-artifacts-4x6 compile-batch setup-batch

# === rebuild + sync into contracts/ ===
#
# Warning: every recipe here re-runs the single-contributor ceremony (insecure,
# not for production), invalidating existing proofs and the committed contract
# fixtures.

# Full rebuild of the transact shape, syncing the verifier into contracts/.
rebuild-4x6: build-artifacts-4x6
    @echo "==> Syncing Verifier_4x6.sol -> {{CONTRACTS_VERIFIER}}"
    cp "{{BUILD}}/Verifier_4x6.sol" "{{CONTRACTS_VERIFIER}}"
    @just _rebuild-report "4x6" "{{BUILD}}/4x6.r1cs" "{{BUILD}}/4x6_js/4x6.wasm" "{{BUILD}}/4x6_final.zkey" "{{BUILD}}/4x6_verification_key.json" "{{CONTRACTS_VERIFIER}}"

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

# Every run prints its fast-check seed on stderr. Replay a run:
#
#   FUZZ=heavy FUZZ_SEED=1234 just test-fuzz
#
# Replay one shrunk counterexample with the `path` from the fast-check report
# (a path is specific to one property):
#
#   FUZZ_SEED=1234 FUZZ_PATH=<path> npm run test:fuzz -- --grep "<test name>"

# Run heavy fuzz suite. FUZZ_SEED=N to replay a previous run.
test-fuzz:
    npm run test:fuzz

# === underconstraint search ===
#
# Mutates a valid witness vector and checks whether the R1CS is still satisfied.
# Detects single-signal underconstraints only; `picus` decides multi-signal
# cases.

# Search for underconstrained signals by mutating valid witnesses.
underconstrained:
    FUZZ=${FUZZ:-medium} NODE_OPTIONS="--import tsx/esm" \
        ./node_modules/.bin/mocha --reporter spec --timeout 1800000 --exit \
        test/tooling/underconstrained_selftest.test.ts test/fuzz/underconstrained.fuzz.test.ts \
        test/fuzz/underconstrained_batch.fuzz.test.ts

# === mutation fuzzing ===
#
# Plants one defect at a time in a private copy of src/ (a dropped constraint,
# `<==` turned into `<--`, a transposed wire, a shifted index) and runs the
# suites, the second-witness search, lint and the lean citation checks against
# it. A mutant nothing rejects is a constraint nothing tests; accepted ones are
# pinned with a reason in test/mutation/survivors.json.
#
#   just mutate                          # a sample: FUZZ=light|medium|heavy = 8 / 40 / 160
#   just mutate --all --resume           # every mutant, continuing an interrupted run
#   just mutate --file balance --all     # every mutant of one file
#   just mutate --only <id>              # one mutant, by the id a run prints
#   just mutate --only <id> --matrix     # every gate, not only the first to reject
#   just mutate --list --op drop-assert  # print mutants without running them
#
# Earlier runs are remembered in build/.mutation/history.json: the test that
# rejected a mutant before runs first, and a sample prefers mutants that were
# weak or never run. A killed mutant then costs seconds; a surviving one runs
# every gate, about three minutes.

# Mutate src/ and check that a gate rejects each mutant. See scripts/mutate.ts for options.
mutate *ARGS:
    NODE_OPTIONS="--import tsx/esm" node "{{ROOT}}/scripts/mutate.ts" {{ARGS}}

# === constraint budget ===

# Every shape must fit its FFT domain and match its count in budget.json. Reads
# the r1cs; run after `compile*`.

# Check every shape against its constraint budget.
budget:
    @echo "==> Constraint budget"
    NODE_OPTIONS="--import tsx/esm" node "{{ROOT}}/scripts/check-budget.mjs"

# Accept new constraint counts into budget.json. Review the diff.
budget-update:
    NODE_OPTIONS="--import tsx/esm" node "{{ROOT}}/scripts/check-budget.mjs" --update

# === golden vectors ===

# Nothing is written if a compiled-circuit witness `y` disagrees with the
# TypeScript Horner evaluation. Slot names come from
# lean/expected/layout-<shape>.txt; run `just lean-update` first if the layout
# changed.

# Regenerate vectors/, the cross-repo test vectors consumed by @lelantos-org/sdk.
vectors:
    NODE_OPTIONS="--import tsx/esm" node "{{ROOT}}/scripts/gen-vectors.ts"

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

# ../contracts commits its own copies of vectors/ files, because forge cannot
# read across repositories. Skips when the sibling checkout is absent.

# Check the copies downstream consumers keep of vectors/.
vectors-consumers-check:
    #!/usr/bin/env bash
    set -euo pipefail
    contracts="{{ROOT}}/../contracts"
    if [ ! -d "$contracts" ]; then
        echo "==> ../contracts not checked out; skipping consumer drift check"
        exit 0
    fi
    status=0
    for pair in \
        "tree-update-batch-8.json:tree_update_batch_vector.json" \
        "transact-4x6.json:transact_4x6_vector.json"
    do
        ours="{{ROOT}}/vectors/${pair%%:*}"
        theirs="$contracts/test/fixtures/${pair##*:}"
        if [ ! -f "$theirs" ]; then
            echo "MISSING  $theirs"; status=1; continue
        fi
        if ! diff -q "$ours" "$theirs" >/dev/null; then
            echo "DRIFTED  $theirs"
            echo "         differs from $ours"
            echo "         re-copy it: cp \"$ours\" \"$theirs\""
            status=1
        fi
    done
    if [ "$status" -ne 0 ]; then
        echo
        echo "A consumer's vector copy is stale. The Solidity suite would keep passing"
        echo "against the old layout while the circuit has moved."
        exit 1
    fi
    echo "==> consumer vector copies up to date"

# === contracts proof fixture ===
#
# Proves a deposit flush and two spends of the deposited note for requests the
# pool accepts, written to ../contracts/test/fixtures/masp_flow_proof.json.
# `keys` must hold the zkeys and verification keys the contracts' verifiers
# were generated from. The wasm is taken from beside the keys or from
# build/<shape>_js/. Proving is randomized, so every run rewrites the proofs.

# Regenerate the MASP-level proof fixture in ../contracts from `keys`.
masp-fixture keys=(BUILD / "prototype-0.18.0"):
    NODE_OPTIONS="--import tsx/esm" node "{{ROOT}}/scripts/gen-masp-fixture.ts" --keys "{{keys}}"

# The linted tree contains no `<--` (the recipe checks), so CS0005 / CS0015 /
# CS0017 run unwaived. Waived passes; to audit, run without `--allow` and
# confirm every reported site is listed here:
#
#   CS0010 non-strict-binary-conversion
#       Each Num2Bits site uses n < 254 bits, so the decomposition is unique.
#       Sites: balance.circom (RangeCheck64, 64 bits), common.circom (2 bits),
#       batch_append.circom (COUNT_BITS; 2*DEPTH bits, 22 at DEPTH = 11).
#
#   CS0014 unconstrained-less-than
#       batch_append.circom `LessThan(COUNT_BITS+1)`: `k` is a compile-time
#       constant and `Num2Bits(COUNT_BITS)` on `actual_count - 1` bounds
#       `actual_count` by 2^COUNT_BITS.
#
#   CS0018 unused-output-signal
#       MerkleLevel4 consumes the `PathIndexSelectors` selectors output; `bits`
#       is the redundant view.

# Static analysis over src/lib and the top-level circuits (needs circomspect).
lint:
    @command -v circomspect >/dev/null || { echo "circomspect not found. Install: cargo install circomspect"; exit 1; }
    @test -z "$(grep -rl -- '<--' "{{ROOT}}/src/lib" "{{ROOT}}/src"/*.circom || true)" \
        || { echo "a '<--' hint appeared in a linted circuit; review it before waiving CS0005/CS0015/CS0017"; exit 1; }
    circomspect "{{ROOT}}/src/lib" "{{ROOT}}/src"/*.circom -L "{{ROOT}}/node_modules" \
        --allow CS0010 --allow CS0014 --allow CS0018

# Delete build/, including artifacts, keys and verifiers.
clean:
    rm -rf "{{BUILD}}"

# === lean proofs ===

# Elaborate and kernel-check every proof; also runs the namespace-wide axiom guard.
lean-build:
    cd "{{ROOT}}/lean" && lake build

# The Lean model mirrors the source signal by signal, so the map is checked
# against `--O1` symbol tables: `--O1` drops only a signal that a constraint pins
# to a constant or to another signal, while `--O2` also substitutes away every
# linearly defined one.

# Check model-to-circuit signal parity (compiles build/o1/*.sym).
signal-parity:
    @echo "==> Model signal parity"
    mkdir -p "{{BUILD}}/o1"
    circom "{{ROOT}}/src/4x6.circom" --sym --O1 -o "{{BUILD}}/o1" -l "{{ROOT}}/node_modules"
    circom "{{ROOT}}/src/tree_update_batch.circom" --sym --O1 -o "{{BUILD}}/o1" -l "{{ROOT}}/node_modules"
    cd "{{ROOT}}" && REQUIRE_ARTIFACTS=1 NODE_OPTIONS="--import tsx/esm" \
        ./node_modules/.bin/mocha --reporter spec --timeout 120000 --exit \
        test/formal/signal_parity.test.ts

# Everything CI runs against the Lean development.
lean-check:
    cd "{{ROOT}}/lean" && ./scripts/check-all.sh

# Regenerate the two golden files under lean/expected/ after an intentional change.
lean-update:
    cd "{{ROOT}}/lean" && ./scripts/check-axioms.sh --update && ./scripts/dump-layout.sh --update

# Picus analyses the R1CS circom emits. It needs Docker and an image, built once
# with:
#
#   docker build -t picus:local https://github.com/Veridise/Picus.git
#
# Upstream publishes amd64 only; on arm64 `just picus-image` builds a native
# image, which `picus` prefers when present. Picus recommends --O0 input, so
# `picus` compiles its own r1cs.

# Build the native arm64 Picus image, avoiding the emulated upstream one.
picus-image:
    docker build --platform linux/arm64 -t picus:arm64 \
        -f "{{ROOT}}/docker/picus-arm64.Dockerfile" "{{ROOT}}/docker"

#   just picus                     # 4x6, weak (default) safety
#   just picus tree_update_batch   # the other circuit under src/
#   just picus tree_update_batch 1 # strong safety

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
    # Picus reports its verdict via exit code (picus/exit.rkt): 8 safe, 9 unsafe,
    # 0 unknown. A safe result exits non-zero, so the code is translated below.
    case "$code" in
        8)  echo "==> {{CIRCUIT}}: properly constrained" ;;
        9)  echo "==> {{CIRCUIT}}: UNDER-CONSTRAINED"; exit 1 ;;
        0)  echo "==> {{CIRCUIT}}: unknown — Picus could not decide (timeout or unsupported)"; exit 1 ;;
        *)  echo "==> {{CIRCUIT}}: Picus error (exit $code)"; exit 1 ;;
    esac

# `picus tree_update_batch` passes only at weak safety, because IsZero's inverse
# hint is unconstrained when its input is zero. `BatchAppend` has no hints, so
# it is checked at strong safety at the deployed shape.

# Strong-safety Picus over a standalone BatchAppend(DEPTH, MAX_L) (needs Docker).
picus-batch-append DEPTH="11" MAX_L="8":
    #!/usr/bin/env bash
    set -euo pipefail
    command -v docker >/dev/null || { echo "docker not found"; exit 1; }
    if docker image inspect picus:arm64 >/dev/null 2>&1; then
        image=picus:arm64
    elif docker image inspect picus:local >/dev/null 2>&1; then
        image=picus:local
    else
        echo "no Picus image. Build one: just picus-image (native arm64)"
        exit 1
    fi
    dir="{{BUILD}}/picus-batch-append"
    name="batch_append_{{DEPTH}}_{{MAX_L}}"
    mkdir -p "$dir"
    printf 'pragma circom 2.2.3;\ninclude "%s";\ncomponent main = BatchAppend({{DEPTH}}, {{MAX_L}});\n' \
        "{{ROOT}}/src/lib/batch_append.circom" > "$dir/$name.circom"
    circom "$dir/$name.circom" --r1cs --sym --O0 -o "$dir" -l "{{ROOT}}/node_modules"
    code=0
    docker run --rm -v "$dir:/data" "$image" \
        ./run-picus --solver z3 --timeout 10000 --strong "/data/$name.r1cs" || code=$?
    case "$code" in
        8)  echo "==> $name: properly constrained (strong)" ;;
        9)  echo "==> $name: UNDER-CONSTRAINED"; exit 1 ;;
        0)  echo "==> $name: unknown — Picus could not decide"; exit 1 ;;
        *)  echo "==> $name: Picus error (exit $code)"; exit 1 ;;
    esac

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

# Depends on `build-artifacts-4x6`, not `rebuild-4x6`, so the publish workflow
# does not require a sibling contracts/ checkout.

# Full rebuild + publish gate. Re-runs the ceremony, invalidating existing proofs.
package: build-artifacts-4x6
    @just package-check

# Stages build/4x6_js/4x6.wasm as the flat build/4x6.wasm that the package
# `files` and `exports` reference, then runs scripts/check-artifacts.ts, which
# reports each missing artifact and how to rebuild it.

# Run the publish gate against whatever is already in build/. No compile, no ceremony.
package-check:
    @echo "==> Staging build/4x6.wasm (no rebuild)"
    @[ -f "{{BUILD}}/4x6_js/4x6.wasm" ] && cp "{{BUILD}}/4x6_js/4x6.wasm" "{{BUILD}}/4x6.wasm" || echo "    skip: build/4x6_js/4x6.wasm absent"
    @echo "==> Verifying artifacts"
    NODE_OPTIONS="--import tsx/esm" node scripts/check-artifacts.ts

# === internal helpers (prefixed `_`) ===

# Compile src/<circuit>.circom. Every shape shares these flags; `budget` relies on it.
_compile circuit:
    mkdir -p "{{BUILD}}"
    echo "==> Compiling {{ROOT}}/src/{{circuit}}.circom"
    circom "{{ROOT}}/src/{{circuit}}.circom" --r1cs --wasm --sym {{CIRCOM_OPT}} -o "{{BUILD}}" -l "{{ROOT}}/node_modules"
    echo "==> Constraint info"
    npx snarkjs r1cs info "{{BUILD}}/{{circuit}}.r1cs"

_fetch-ptau file:
    #!/usr/bin/env bash
    set -euo pipefail
    case "{{file}}" in
        "{{PTAU16}}") want="{{PTAU16_SHA}}" ;;
        *) echo "no pinned digest for {{file}}" >&2; exit 1 ;;
    esac
    mkdir -p "{{PTAU_DIR}}"
    dest="{{PTAU_DIR}}/{{file}}"
    if [ ! -f "$dest" ]; then
        echo "==> Downloading {{file}}"
        # -f makes curl fail on HTTP errors instead of writing the error body and
        # exiting 0. Downloading to .part prevents an interrupted fetch from being
        # treated as a complete file on the next run.
        curl -fL --retry 3 --retry-all-errors "{{PTAU_URL_BASE}}/{{file}}" -o "$dest.part"
        mv "$dest.part" "$dest"
    fi
    got=$({ sha256sum "$dest" 2>/dev/null || shasum -a 256 "$dest"; } | cut -d' ' -f1)
    if [ "$got" != "$want" ]; then
        echo "==> ptau digest mismatch for {{file}}" >&2
        echo "    got  $got" >&2
        echo "    want $want" >&2
        echo "    remove $dest and re-run to refetch" >&2
        exit 1
    fi

_rebuild-report name r1cs wasm zkey vk verifier:
    @echo "==> rebuild ({{name}}) complete"
    @echo "    r1cs:        {{r1cs}}"
    @echo "    wasm:        {{wasm}}"
    @echo "    zkey:        {{zkey}}"
    @echo "    vk:          {{vk}}"
    @echo "    verifier:    {{verifier}}"
