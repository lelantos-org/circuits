#!/usr/bin/env bash
# Deletes build outputs of `Lelantos` modules that have no `.lean` source.
#
# `lake build` never removes oleans, and CI restores `.lake` from cache, so a deleted
# or renamed module leaves an orphaned olean. `lake build` ignores it because nothing
# imports it, but `leanchecker` replays every olean under the `Lelantos` prefix against
# the current oleans of its imports and fails on mismatched declarations ("unknown
# constant", "constant has already been declared").
#
# Only files under `.lake/build` whose module has no `.lean` source are removed.
set -euo pipefail

cd "$(dirname "$0")/.."

removed=0
for root in .lake/build/lib/lean .lake/build/ir; do
  [ -d "$root" ] || continue
  while IFS= read -r -d '' file; do
    rel="${file#"$root"/}"
    # `Lelantos/Gadgets/Insert.olean.hash` -> `Lelantos/Gadgets/Insert`. Module
    # directories contain no dots, so the first dot starts the extension.
    module="${rel%%.*}"
    if [ ! -f "$module.lean" ]; then
      rm -f "$file"
      echo "removed $file"
      removed=$((removed + 1))
    fi
  done < <(find "$root" \( -path "$root/Lelantos/*" -o -path "$root/Lelantos.*" \) -type f -print0)
done
echo "OK: $removed stale build output(s) pruned."
