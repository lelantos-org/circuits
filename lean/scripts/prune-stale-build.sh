#!/usr/bin/env bash
# Delete the build outputs of `Lelantos` modules whose source no longer exists.
#
# `lake build` writes an olean per module and never removes one, so deleting or
# renaming a `.lean` file leaves its old olean behind — and CI restores `.lake`
# from cache, so the orphan outlives a clean checkout too. The build does not
# care, because nothing imports it. `leanchecker` does: it replays every olean
# under the `Lelantos` prefix, imported or not, against the current oleans of
# the modules the orphan once imported, and fails on the first declaration that
# moved ("unknown constant", "constant has already been declared").
#
# Only files under `.lake/build` are touched, and only those whose module has no
# `.lean` source.
set -euo pipefail

cd "$(dirname "$0")/.."

removed=0
for root in .lake/build/lib/lean .lake/build/ir; do
  [ -d "$root" ] || continue
  while IFS= read -r -d '' file; do
    rel="${file#"$root"/}"
    # `Lelantos/Gadgets/Insert.olean.hash` -> `Lelantos/Gadgets/Insert`. Module
    # directories carry no dots, so the first dot starts the extension.
    module="${rel%%.*}"
    if [ ! -f "$module.lean" ]; then
      rm -f "$file"
      echo "removed $file"
      removed=$((removed + 1))
    fi
  done < <(find "$root" \( -path "$root/Lelantos/*" -o -path "$root/Lelantos.*" \) -type f -print0)
done
echo "OK: $removed stale build output(s) pruned."
