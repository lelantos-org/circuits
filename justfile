set shell := ["bash", "-ceuo", "pipefail"]

# === paths ===
ROOT := justfile_directory()
BUILD := ROOT / "build"
PTAU_DIR := ROOT / "ptau"
# The Hermez files were served from `https://storage.googleapis.com/zkevm/ptau`
# until that bucket started refusing anonymous reads (403 on every object); the
# hermez and PSE S3 mirrors are gone the same way. `lelantos-org/ptau` holds
# byte-identical copies as release assets, which are unauthenticated and not
# metered against any bandwidth quota.
PTAU_URL_BASE := "https://github.com/lelantos-org/ptau/releases/download/hermez"
# Both circuits are on the 2^17 ceremony: Transact(11,4,6) is 100,320 constraints
# and TreeUpdateBatch(11,8) is 113,502, so neither fits 2^16. snarkjs picks the
# domain from `nConstraints + nPubInputs + nOutputs`, which caps a 2^16 ceremony
# at 65,533 constraints. See `budget` below.
#
# `_setup` takes the ptau as an argument; PTAU16 is available for a smaller
# circuit and is not referenced by any recipe.
PTAU16 := "powersOfTau28_hez_final_16.ptau"
PTAU17 := "powersOfTau28_hez_final_17.ptau"

# Checked on every fetch, including on a cache hit. A truncated or substituted
# ptau is not self-describing: snarkjs reports it as `Invalid File format` from
# somewhere deep in the setup, long after the bad bytes landed.
PTAU16_SHA := "1c401abb57c9ce531370f3015c3e75c0892e0f32b8b1e94ace0f6682d9695922"
PTAU17_SHA := "6b662a324867139fb1a20a324d90b6ff61856dfb23f59326909f14b0e2483ae0"

# Pinned revision of iden3/circom-witnesscalc, which supplies the relayer's
# native witness calculator. `build-circuit` is not published to crates.io; it
# lives in that repo's `extensions/` and pulls the circom compiler from git, so
# it is installed from a fixed commit rather than a version range.
#
# The relayer's `circom-witnesscalc` dependency must be pinned to this SAME
# revision: the graph format is versioned, and a mismatched reader rejects the
# file with "Invalid magic".
#
# `--locked` below is required: build-circuit depends on the circom compiler
# crates by branch (`master`), so without the committed lockfile the install
# resolves an incompatible circom and fails to build.
CWC_REV := "d48eb7c97857d46b8a75c94ab96f769207263245"
CWC_REPO := "https://github.com/iden3/circom-witnesscalc"
TOOLS := ROOT / ".tools"
BUILD_CIRCUIT := TOOLS / "build-circuit" / "bin" / "build-circuit"

# Sync targets in the sibling contracts/ checkout, under src/verifiers/.
CONTRACTS_VERIFIER := ROOT / ".." / "contracts" / "src" / "verifiers" / "Verifier.sol"
CONTRACTS_TREE_BATCH_VERIFIER := ROOT / ".." / "contracts" / "src" / "verifiers" / "TreeUpdateBatchVerifier.sol"

default:
    @just --list

# === transact circuit ===
#
# `Transact(11, 4, 6)` — src/4x6.circom, the only published transact shape.

# Compile 4x6.circom -> r1cs + wasm + sym, print constraint count.
compile-4x6: (_compile "4x6")

# Phase-2 trusted setup for 4x6 (single-contributor; INSECURE — prototype only).
setup-4x6: (_setup "4x6" PTAU17)

# Compile + trusted setup for 4x6.
build-artifacts-4x6: compile-4x6 setup-4x6

# === tree_update_batch circuit ===

# Compile tree_update_batch.circom -> r1cs + wasm + sym, print constraint count.
compile-batch: (_compile "tree_update_batch")

# The relayer evaluates this graph in-process instead of running the
# circom-emitted wasm witness generator. Two invariants are enforced below:
#
#   --O1   `_compile` uses circom's default optimisation while build-circuit
#          defaults to --O2, which yields a different constraint system; the
#          graph would then index signals the zkey does not have.
#
#   cmp    build-circuit re-runs the circom front end, so its R1CS is diffed
#          against `_compile`'s output. A graph that disagrees with the zkey
#          produces witnesses that fail verification at prove time.

# Build the native witness-calculation graph the relayer proves against.
build-graph: compile-batch _ensure-build-circuit
    echo "==> Building witness graph (build-circuit @ {{CWC_REV}})"
    "{{BUILD_CIRCUIT}}" "{{ROOT}}/src/tree_update_batch.circom" "{{BUILD}}/tree_update_batch.wcd" \
        -l "{{ROOT}}/node_modules" --O1 --r1cs "{{BUILD}}/tree_update_batch.graph.r1cs"
    echo "==> Checking the graph's constraint system matches the compiled one"
    cmp "{{BUILD}}/tree_update_batch.graph.r1cs" "{{BUILD}}/tree_update_batch.r1cs"
    # The r1cs is emitted only for that diff; build-circuit also drops two
    # signal-map debug files into the working directory.
    rm -f "{{BUILD}}/tree_update_batch.graph.r1cs" \
          "{{ROOT}}/log_input_signals.txt" "{{ROOT}}/log_input_signals_new.txt"
    echo "==> Graph at {{BUILD}}/tree_update_batch.wcd"

# Install the pinned build-circuit into .tools/ unless it is already there.
#
# `circom-witnesscalc` compiles its protobuf schema in a build script, so the
# install needs `protoc` on PATH. Checked up front because prost-build's own
# failure surfaces from inside a dependency's build script and reads as a
# compile error rather than a missing tool.
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

# tree_update_batch at MAX_L=8, depth 11 is the tighter of the two circuits:
# 113,527 constraints against a 131,069 ceiling on the 2^17 domain (snarkjs
# sizes the domain from nConstraints + nPubInputs + nOutputs and needs the sum
# below 2^17). A leaf slot costs roughly 12k constraints, so a further widening
# breaks this bound first. `just budget` pins the domain so growth past it fails
# CI; `groth16 setup` is a second check on the same bound, failing outright when
# the constraint count exceeds the ptau.

# Phase-2 trusted setup for tree_update_batch (single-contributor; INSECURE).
setup-batch: (_setup "tree_update_batch" PTAU17)

# The four snarkjs calls every phase-2 setup makes, written once so the ptau
# cannot drift between shapes. `groth16 setup` fails outright when the
# constraint count exceeds the ptau.
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

# The two circuits are ceremony-paired: a spend's output leaves are inserted by
# the batch circuit, so they share DEPTH.

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

# Every run pins a fast-check seed and announces it on stderr, so a failure is
# reproducible. Set FUZZ_SEED to replay one:
#
#   FUZZ=heavy FUZZ_SEED=1234 just test-fuzz
#
# To land straight on a single shrunk counterexample, add the `path` from the
# fast-check report and grep to that test — a path belongs to one property, so
# it needs the grep:
#
#   FUZZ_SEED=1234 FUZZ_PATH=<path> npm run test:fuzz -- --grep "<test name>"
#
# CI writes the replay line into the job summary; see .github/workflows/fuzz.yml.

# Run heavy fuzz suite. FUZZ_SEED=N to replay a previous run.
test-fuzz:
    npm run test:fuzz

# === underconstraint search ===
#
# Mutates an honest WITNESS VECTOR and asks the R1CS whether it still satisfies,
# which is the half `test-tamper` cannot reach: the tamper suites mutate the
# input object, and the witness calculator turns any input it accepts into a
# self-consistent witness, so a signal the template computes but never
# constrains is invisible from there. See test/lib/underconstrained.ts.
#
# Unlike `picus` this needs no docker, so it runs in the normal suite. The batch
# shape dominates the runtime: a few minutes at FUZZ=medium, more at heavy. It is strictly weaker: single-signal only. `picus` decides
# multi-signal underconstraints and is the tool to reach for when this is clean
# but the question is still open.
underconstrained:
    FUZZ=${FUZZ:-medium} NODE_OPTIONS="--import tsx/esm" \
        ./node_modules/.bin/mocha --reporter spec --timeout 1800000 --exit \
        test/underconstrained_selftest.test.ts test/fuzz/underconstrained.fuzz.test.ts \
        test/fuzz/underconstrained_batch.fuzz.test.ts

# === constraint budget ===

# Every shape must fit its FFT domain and its exact count must match
# budget.json, so a change lands as a reviewable diff. Reads the r1cs, so run
# after `compile*`.

# Check every shape against its constraint budget.
budget:
    @echo "==> Constraint budget"
    NODE_OPTIONS="--import tsx/esm" node "{{ROOT}}/scripts/check-budget.mjs"

# Accept new constraint counts into budget.json. Review the diff.
budget-update:
    NODE_OPTIONS="--import tsx/esm" node "{{ROOT}}/scripts/check-budget.mjs" --update

# === asset id separation ===
#
# A deposit leaf is pinned only by cv_dep = leaf_public_in · V^leaf_asset + rcv·H,
# and every V^a is a known multiple m(a)·BASE0 (src/README.md § 5), so two ids
# whose multipliers share a large factor admit v·V^a == v'·V^a' inside the
# circuit's 64-bit value range, letting a depositor pay the cheap side and spend
# the leaf as the expensive one. Run this over the id set BEFORE registering it:
# `AssetRegistry.addAsset` takes an arbitrary uint64 and checks nothing here.

# Check a set of asset ids for deposit-binding collisions.
asset-ids +ids:
    @echo "==> Asset id separation"
    NODE_OPTIONS="--import tsx/esm" node "{{ROOT}}/scripts/check-asset-ids.ts" {{ids}}

# Check the gate itself against a known colliding pair.
asset-ids-self-test:
    NODE_OPTIONS="--import tsx/esm" node "{{ROOT}}/scripts/check-asset-ids.ts" --self-test

# === golden vectors ===

# Every `y` is read out of a witness produced by the compiled circuit and
# compared against the TypeScript Horner evaluation; the generator refuses to
# write on disagreement. Slot names come from lean/expected/layout-<shape>.txt,
# so run `just lean-update` first if the layout changed.

# Regenerate vectors/ — the cross-repo contract consumed by @lelantos-org/sdk.
vectors:
    NODE_OPTIONS="--import tsx/esm" node "{{ROOT}}/scripts/gen-vectors.ts"

# Run in CI: a circuit or layout change not accompanied by `just vectors` fails
# here.

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

# Check the copies downstream consumers keep of vectors/.
#
# `contracts/` pins `PubInputs.compress` against a COPY of
# vectors/tree-update-batch-8.json, checked into its own repo because forge
# cannot read across a repository boundary. A copy is a second source of truth:
# regenerate here, forget to re-copy, and the Solidity suite keeps passing
# against the old layout while the circuit has moved. That is precisely the
# binding the copy exists to anchor.
#
# Skips cleanly when the sibling checkout is absent, so the circuits repo still
# builds alone.
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

# Static analysis via Trail of Bits circomspect. Install: cargo install circomspect
#
# Scope is `src/lib/` plus the top-level `src/*.circom` entry points. The tree
# contains no `<--`, so the CS0005 / CS0015 / CS0017 passes (signal-assignment,
# unconstrained-division, under-constrained-signal) run unwaived on every
# compiled circuit. Re-check `grep -rn '<--' src/lib src/*.circom` before adding
# any waiver.
#
# Suppressed analysis passes and their rationale. To audit, run without the
# `--allow` flags and confirm every reported site falls under one of these
# categories. Re-evaluate whenever the listed sites change.
#
#   CS0010 non-strict-binary-conversion
#       Each Num2Bits site uses n < 254 bits, so 2^n < p and the field-element
#       decomposition is unique (no aliasing).
#       Sites: balance.circom / asset_gen.circom (64 bits),
#              value_commit.circom (RCV_BITS = 252), common.circom (2 bits),
#              tree_update_batch.circom (COUNT_BITS = 2; 2*DEPTH bits,
#              DEPTH <= 32 ⇒ n <= 64).
#
#   CS0014 unconstrained-less-than
#       tree_update_batch.circom `LessThan(COUNT_BITS+1)` with inputs `k`
#       (compile-time loop var, constant in R1CS) and `actual_count`
#       (bounded by `Num2Bits(COUNT_BITS=2)` in step 1, so <= 2^2).
#
#   CS0018 unused-output-signal
#       Components are instantiated for their internal constraints and not every
#       output is propagated. Sites:
#         - SpentNote/OutputNote: only the cv branch's `vc_dep.rH` is threaded
#           out; the deposit-branch rH is bound internally by ValueCommit.
#         - QuaternaryInsertLevel/MerkleLevel4: the `PathIndexSelectors`
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

# Model-to-circuit signal parity. Needs build/*.sym, so it is the one check that
# wants the production compile rather than circom_tester's own artifacts; run
# `just compile-4x6 compile-batch` first. REQUIRE_ARTIFACTS=1 makes a missing
# artifact a failure instead of a skip, so this can never pass by doing nothing.
signal-parity:
    @echo "==> Model signal parity"
    cd "{{ROOT}}" && REQUIRE_ARTIFACTS=1 NODE_OPTIONS="--import tsx/esm" \
        ./node_modules/.bin/mocha --reporter spec --timeout 120000 --exit \
        test/formal/signal_parity.test.ts

# Everything CI runs against the Lean development.
lean-check:
    cd "{{ROOT}}/lean" && ./scripts/check-all.sh

# Regenerate the two golden files under lean/expected/ after an intentional change.
lean-update:
    cd "{{ROOT}}/lean" && ./scripts/check-axioms.sh --update && ./scripts/dump-layout.sh --update

# Complements the Lean proofs: those cover the modeled constraint system, while
# Picus reads the R1CS circom emits. Not part of `lean-check` or CI, since it
# needs Docker and a 4.5 GB image, built once with:
#
#   docker build -t picus:local https://github.com/Veridise/Picus.git
#
# Upstream publishes amd64 only, so on arm64 `just picus-image` builds a native
# image and `picus` prefers it when present. Picus recommends --O0 input, so a
# separate artifact is compiled rather than reusing build/4x6.r1cs.

# Build the native arm64 Picus image, avoiding the emulated upstream one.
picus-image:
    docker build --platform linux/arm64 -t picus:arm64 \
        -f "{{ROOT}}/docker/picus-arm64.Dockerfile" "{{ROOT}}/docker"

#   just picus                     # 4x6, weak (default) safety
#   just picus tree_update_batch   # the other circuit under src/
#   just picus tree_update_batch 1 # strong safety
#   just picus 4x6 1               # strong safety on the default shape

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
    # Picus signals its verdict through the exit code (picus/exit.rkt): 8 safe,
    # 9 unsafe, 0 unknown. A passing run exits non-zero, so the code is
    # translated below.
    case "$code" in
        8)  echo "==> {{CIRCUIT}}: properly constrained" ;;
        9)  echo "==> {{CIRCUIT}}: UNDER-CONSTRAINED"; exit 1 ;;
        0)  echo "==> {{CIRCUIT}}: unknown — Picus could not decide (timeout or unsupported)"; exit 1 ;;
        *)  echo "==> {{CIRCUIT}}: Picus error (exit $code)"; exit 1 ;;
    esac

# Continues past a failing circuit so one result does not hide the others, then
# exits non-zero if any failed.

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
# invalidates existing proofs; `package-check` runs the gate alone. Copies the
# witness wasm out of `build/4x6_js/` to a flat `build/4x6.wasm` so the package
# `files` whitelist and `exports` subpath map resolve without shipping the
# `4x6_js/` glue, then runs `scripts/check-artifacts.ts`.
#
# Depends on `build-artifacts-4x6` and NOT `rebuild-4x6`, so the publish workflow
# does not require a sibling contracts/ checkout for the Verifier.sol sync step.

# Full rebuild + publish gate. RE-RUNS THE CEREMONY, invalidating existing proofs.
package: build-artifacts-4x6
    @just package-check

# Stage the flat wasms and run the publish gate against whatever is ALREADY in
# build/ — no compile, no ceremony.
#
# Separate from `package`, which runs a trusted-setup ceremony: that mints a
# fresh zkey from fresh entropy and invalidates every proof built against the
# previous one, including the committed fixtures in ../contracts
# (proof_transfer.json, proof_deposit_batch_n1.json).
#
# Missing artifacts are reported by check-artifacts.ts, which names each one and
# how to rebuild it.

# Run the publish gate against whatever is already in build/. No compile, no ceremony.
package-check:
    @echo "==> Staging build/4x6.wasm (no rebuild)"
    @[ -f "{{BUILD}}/4x6_js/4x6.wasm" ] && cp "{{BUILD}}/4x6_js/4x6.wasm" "{{BUILD}}/4x6.wasm" || echo "    skip: build/4x6_js/4x6.wasm absent"
    @echo "==> Verifying artifacts"
    NODE_OPTIONS="--import tsx/esm" node scripts/check-artifacts.ts

# === internal helpers (prefixed `_`) ===

# Compile one src/<circuit>.circom to r1cs + wasm + sym and print its constraint
# count. The named `compile*` recipes are thin wrappers so the flags cannot drift
# between shapes; the constraint budget compares the shapes against one another.
_compile circuit:
    mkdir -p "{{BUILD}}"
    echo "==> Compiling {{ROOT}}/src/{{circuit}}.circom"
    circom "{{ROOT}}/src/{{circuit}}.circom" --r1cs --wasm --sym -o "{{BUILD}}" -l "{{ROOT}}/node_modules"
    echo "==> Constraint info"
    npx snarkjs r1cs info "{{BUILD}}/{{circuit}}.r1cs"

_fetch-ptau file:
    #!/usr/bin/env bash
    set -euo pipefail
    case "{{file}}" in
        "{{PTAU16}}") want="{{PTAU16_SHA}}" ;;
        "{{PTAU17}}") want="{{PTAU17_SHA}}" ;;
        *) echo "no pinned digest for {{file}}" >&2; exit 1 ;;
    esac
    mkdir -p "{{PTAU_DIR}}"
    dest="{{PTAU_DIR}}/{{file}}"
    if [ ! -f "$dest" ]; then
        echo "==> Downloading {{file}}"
        # -f matters: without it curl writes the HTTP error body into the file
        # and exits 0, so a dead mirror looks like a corrupt ceremony.
        # Downloads to .part so an interrupted fetch is not mistaken for a
        # complete file on the next run.
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
