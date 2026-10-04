#!/usr/bin/env bash
# Runs every check CI runs, ordered so the fastest-failing checks come first.
#
# `lake build` also runs the environment-wide axiom scan in `Lelantos.Meta.AxiomGuard`.
# `leanchecker` replays every declaration through the kernel independently of the
# elaborator.
set -euo pipefail

cd "$(dirname "$0")/.."

step() { printf '\n\033[1m==> %s\033[0m\n' "$1"; }

step "Arithmetic axioms (external)"
python3 scripts/check-prime.py

step "Build and proof check"
lake build

step "Kernel re-check"
./scripts/prune-stale-build.sh
lake env leanchecker
echo "OK: leanchecker replayed every Lelantos module."

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
