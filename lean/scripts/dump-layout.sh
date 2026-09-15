#!/usr/bin/env bash
# Dumps the Lean model's public-input layout for every shipped shape and diffs it
# against the checked-in expectation.
#
# The layout is hand-transcribed and must agree with
# `src/lib/poly_eval.circom :: TransactCompressN`,
# `contracts/src/lib/PubInputs.sol :: compress(Transact, aux)` and
# `test/ref/compress.ts :: coeffs`: four implementations of one order.
#
# `lean/expected/layout-4x6.txt` is also consumed by `test/formal/layout_parity.test.ts`,
# which checks it against `test/ref/compress.ts`, the generator of the published
# `vectors/`. This links the order to the SDK without either repo importing the other.
#
# Two layouts are dumped, the transact shapes and `BatchCompress(MAX_L)`, and they
# differ in kind.
#
# The 46-slot transact dump is the polynomial, not the challenge preimage.
# `PubInputs.sol` hashes 70 words to derive `z` and evaluates only these 46. The five
# address words, the FMD clue triples and the payload digest are bound through the
# challenge because the circuit does not constrain them; an unconstrained coefficient
# would be a free variable a prover could use to solve `y = Σ c_k z^k`. The calldata
# prefix is 50 words, which fixes the offsets of the uint64 and address words
# `compress` re-masks in assembly.
#
# The batch dump has no such split: all `4 + 6*MAX_L` words are signals of
# `tree_update_batch.circom`, so all 52 are coefficients and must be evaluated for
# soundness. `test/formal/batch_layout_parity.test.ts` asserts the same against the
# published vector, with this file as the Lean reference.
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
