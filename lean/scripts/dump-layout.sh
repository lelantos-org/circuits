#!/usr/bin/env bash
# Dump the public-input layout that the Lean model uses, and diff it against the
# checked-in expectation.
#
# The layout is the highest-risk piece of hand transcription in the whole development:
# it must agree with `src/lib/poly_eval.circom :: TransactCompressN`,
# `contracts/src/lib/PubInputs.sol :: compress(Transact, aux)` and
# `sdk/src/bundle/snark-compression.ts :: flatten`. Four implementations, one order.
#
# `lean/expected/layout-2x2.txt` is consumed by `src/test/formal/layout_parity.test.ts`, which
# checks it against the SDK. This script checks it against Lean.
#
# Regenerate after an intentional layout change:  lean/scripts/dump-layout.sh --update
set -euo pipefail

cd "$(dirname "$0")/.."
EXPECTED=expected/layout-2x2.txt
ACTUAL=$(mktemp)
SRC=$(mktemp /tmp/layoutXXXXXX.lean)
trap 'rm -f "$ACTUAL" "$SRC"' EXIT

cat > "$SRC" <<'LEAN'
import Lelantos
open Lelantos
def main : IO Unit := do
  for name in layoutNames 2 2 do
    IO.println (name.replace "Lelantos.PISlot." "")
#eval main
LEAN

lake env lean "$SRC" 2>/dev/null > "$ACTUAL"

if [ ! -s "$ACTUAL" ]; then
  echo "FAIL: Lean produced no layout output"
  exit 1
fi

if [ "${1:-}" = "--update" ]; then
  cp "$ACTUAL" "$EXPECTED"
  echo "updated $EXPECTED"
  cat -n "$EXPECTED"
  exit 0
fi

if ! diff -u "$EXPECTED" "$ACTUAL"; then
  echo
  echo "FAIL: the Lean public-input layout changed."
  echo "It must stay in lockstep with TransactCompressN, PubInputs.sol and the SDK."
  exit 1
fi

echo "OK: Lean layout matches $EXPECTED ($(wc -l < "$EXPECTED" | tr -d ' ') slots)."
