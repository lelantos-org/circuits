#!/usr/bin/env bash
# Run every check CI runs, in the order that fails fastest.
#
# `lake build` is the proof check: compiling a Lean module elaborates and kernel-checks
# every proof in it, and it also runs the environment-wide axiom scan in
# `Lelantos.Meta.AxiomGuard`. The rest compare the development against artefacts outside
# it — the primality of the field modulus, the recorded trusted base, the public-input
# layout the SDK and the contract also implement, the source citations the doc comments
# carry, the constraints those citations reach, and the Lean names the prose claims
# exist.
set -euo pipefail

cd "$(dirname "$0")/.."

step() { printf '\n\033[1m==> %s\033[0m\n' "$1"; }

step "Arithmetic axioms (external)"
python3 scripts/check-prime.py

step "Build and proof check"
lake build

step "No admitted proofs"
if grep -rn '\bsorry\b' Lelantos/ Lelantos.lean; then
  echo "FAIL: a proof is admitted with sorry"
  exit 1
fi
echo "OK: no admitted proofs."

step "Trusted base"
./scripts/check-axioms.sh

step "Public-input layout"
./scripts/dump-layout.sh

step "Source citations"
python3 scripts/check-citations.py

step "Constraint coverage"
python3 scripts/check-coverage.py

step "Names the prose claims"
python3 scripts/check-names.py

printf '\n\033[1mAll checks passed.\033[0m\n'
