#!/usr/bin/env bash
# Fail if the trusted base changed.
#
# `#print axioms` is the only authoritative statement of what this development assumes.
# This script captures it and diffs against the checked-in expectation, so an axiom can
# never be added without the diff showing up in review.
#
# Regenerate after an intentional change:  lean/scripts/check-axioms.sh --update
set -euo pipefail

cd "$(dirname "$0")/.."
EXPECTED=expected/axioms.txt
ACTUAL=$(mktemp)
trap 'rm -f "$ACTUAL"' EXIT

lake env lean Lelantos/Meta/Assumptions.lean 2>/dev/null \
  | tr -d '\n' \
  | sed 's/'"'"'Lelantos/\n'"'"'Lelantos/g' \
  | sed 's/  */ /g' \
  | sed '/^$/d' \
  > "$ACTUAL"

if [ ! -s "$ACTUAL" ]; then
  echo "FAIL: no axiom output -- 'lake env lean Lelantos/Meta/Assumptions.lean' produced nothing."
  echo "Run it directly to see the error; without this guard --update would install an"
  echo "empty expectation and the check would pass forever."
  exit 1
fi

if [ "${1:-}" = "--update" ]; then
  cp "$ACTUAL" "$EXPECTED"
  echo "updated $EXPECTED"
  cat "$EXPECTED"
  exit 0
fi

if ! diff -u "$EXPECTED" "$ACTUAL"; then
  echo
  echo "FAIL: the axiom set changed."
  echo "If this is intentional, review the diff above, then run:"
  echo "  lean/scripts/check-axioms.sh --update"
  exit 1
fi

echo "OK: trusted base unchanged."
