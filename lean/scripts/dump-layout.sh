#!/usr/bin/env bash
# Dump the public-input layout that the Lean model uses, and diff it against the
# checked-in expectation, for every shape the repository ships.
#
# The layout is the highest-risk piece of hand transcription in the whole development:
# it must agree with `src/lib/poly_eval.circom :: TransactCompressN`,
# `contracts/src/lib/PubInputs.sol :: compress(Transact, aux)` and
# `sdk/src/bundle/snark-compression.ts :: flatten`. Four implementations, one order.
#
# `lean/expected/layout-2x2.txt` is additionally consumed by
# `src/test/formal/layout_parity.test.ts`, which checks it against the SDK; that link exists
# for the 2x2 shape only. For 2x3 and 3x3 this script pins Lean against its own expectation,
# which catches an accidental layout change but does not cross-check the SDK.
#
# Regenerate after an intentional layout change:  lean/scripts/dump-layout.sh --update
set -euo pipefail

cd "$(dirname "$0")/.."

# shape name -> N_IN N_OUT, matching src/2x2.circom, src/2x3.circom, src/3x3.circom.
SHAPES=("2x2 2 2" "2x3 2 3" "3x3 3 3")

ACTUAL=$(mktemp)
SRC=$(mktemp /tmp/layoutXXXXXX.lean)
trap 'rm -f "$ACTUAL" "$SRC"' EXIT

status=0

for shape in "${SHAPES[@]}"; do
  read -r name nIn nOut <<<"$shape"
  EXPECTED="expected/layout-${name}.txt"

  cat > "$SRC" <<LEAN
import Lelantos
open Lelantos
def main : IO Unit := do
  for name in layoutNames ${nIn} ${nOut} do
    IO.println (name.replace "Lelantos.PISlot." "")
#eval main
LEAN

  lake env lean "$SRC" 2>/dev/null > "$ACTUAL"

  if [ ! -s "$ACTUAL" ]; then
    echo "FAIL: Lean produced no layout output for ${name}"
    exit 1
  fi

  if [ "${1:-}" = "--update" ]; then
    cp "$ACTUAL" "$EXPECTED"
    echo "updated $EXPECTED ($(wc -l < "$EXPECTED" | tr -d ' ') slots)"
    continue
  fi

  if ! diff -u "$EXPECTED" "$ACTUAL"; then
    echo
    echo "FAIL: the Lean public-input layout changed for ${name}."
    echo "It must stay in lockstep with TransactCompressN, PubInputs.sol and the SDK."
    status=1
  else
    echo "OK: Lean layout matches $EXPECTED ($(wc -l < "$EXPECTED" | tr -d ' ') slots)."
  fi
done

exit "$status"
