#!/usr/bin/env bash
# Dumps the Lean model's public-input layout for every shipped shape and diffs it
# against the checked-in expectation.
#
# The layout is hand-transcribed and must agree with
# `src/lib/poly_eval.circom :: TransactCompressN`,
# `contracts/src/lib/PubInputs.sol :: compress(Transact, aux)` and
# `test/ref/compress.ts :: coeffs`.
#
# `lean/expected/layout-4x6.txt` is also checked by `test/formal/layout_parity.test.ts`
# against `test/ref/compress.ts`, the generator of the published `vectors/`.
#
# Transact dump: the 13 words `PubInputs.sol` evaluates, the logical public inputs
# that are signals of the circuit; it hashes 38 words to derive `z`. Hashed but not
# evaluated, so absent from the dump: the digest of the thirteen (a public output of
# the circuit, also passed to the verifier) and the words that are not circuit
# signals (the five address and chain words, the FMD clue triples, the payload
# digest). The calldata prefix is 19 words (`src/4x6.circom`), which fixes the
# offsets of the uint64 and address words `compress` re-masks in assembly.
#
# Batch dump: all `4 + 4*MAX_L` words are signals of `tree_update_batch.circom`, so
# all 36 are coefficients. Its digest is a public output, hashed (37 words in all)
# and not evaluated. `test/formal/batch_layout_parity.test.ts` asserts the same
# against the published vector.
#
# Regenerate after an intentional layout change:  lean/scripts/dump-layout.sh --update
set -euo pipefail

cd "$(dirname "$0")/.."

# shape name -> N_IN N_OUT, matching the entry points under src/.
SHAPES=("4x6 4 6")

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

# `BatchCompress(MAX_L)`, matching `src/tree_update_batch.circom`'s instantiation.
for maxL in 8; do
  EXPECTED="expected/layout-batch-${maxL}.txt"

  cat > "$SRC" <<LEAN
import Lelantos
open Lelantos
def main : IO Unit := do
  for name in batchLayoutNames ${maxL} do
    IO.println (name.replace "Lelantos.BatchPISlot." "")
#eval main
LEAN

  lake env lean "$SRC" 2>/dev/null > "$ACTUAL"

  if [ ! -s "$ACTUAL" ]; then
    echo "FAIL: Lean produced no batch layout output for MAX_L=${maxL}"
    exit 1
  fi

  if [ "${1:-}" = "--update" ]; then
    cp "$ACTUAL" "$EXPECTED"
    echo "updated $EXPECTED ($(wc -l < "$EXPECTED" | tr -d ' ') slots)"
    continue
  fi

  if ! diff -u "$EXPECTED" "$ACTUAL"; then
    echo
    echo "FAIL: the Lean batch layout changed for MAX_L=${maxL}."
    echo "It must stay in lockstep with BatchCompress, PubInputs.sol and the SDK."
    status=1
  else
    echo "OK: Lean batch layout matches $EXPECTED ($(wc -l < "$EXPECTED" | tr -d ' ') slots)."
  fi
done

exit "$status"
