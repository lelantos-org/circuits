"""What every check under `lean/scripts/` needs: where the repo is, which files to
read, and how to report.

Three checks share this — `check-citations.py`, `check-coverage.py`,
`check-names.py` — and they had three copies of the repo paths and two of the
directory walk. That is the same duplication these checks exist to find in the prose,
so keeping it here is not tidiness for its own sake.

`check-axioms.sh` and `dump-layout.sh` are the same kind of check in shell, because
what they run is `lake`. They follow the same output convention by hand.
"""

from __future__ import annotations

import os
from typing import Iterator

# `lean/scripts/` -> `lean/` -> the circuits root. `contracts/` and `sdk/` are
# siblings of the circuits root rather than children, which is why several checks
# search both it and its parent.
LEAN = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
REPO = os.path.abspath(os.path.join(LEAN, ".."))
SRC = os.path.join(REPO, "src")
SEARCH_ROOTS = [REPO, os.path.dirname(REPO)]

# The prose under check: Lean sources and the two markdown files beside them. Doc
# comments and tables make the same kinds of claim and are checked the same way.
SCANNED_SUFFIXES = (".lean", ".md")

# Build output and vendored code. `.lake` holds Mathlib, which is large and not ours.
SKIPPED_DIRS = {".lake", "build", "node_modules"}


def scanned_files() -> Iterator[str]:
    """Every Lean source and markdown file under `lean/`, in a stable order."""
    for dirpath, dirnames, filenames in os.walk(LEAN):
        dirnames[:] = [d for d in dirnames if d not in SKIPPED_DIRS]
        for name in sorted(filenames):
            if name.endswith(SCANNED_SUFFIXES):
                yield os.path.join(dirpath, name)


def report(failures: list[str], total: int, noun: str, verb: str = "resolve",
           hint: tuple[str, ...] = ()) -> int:
    """The `OK:` / `FAIL:` convention these checks share, and their exit status.

    One line per failure, then a count, then what to do about it — the shape
    `check-all.sh` prints in sequence and CI greps. Returns the exit status so a
    caller's `main` is `return report(...)`.
    """
    if not failures:
        print(f"OK: {total} {noun} {verb}.")
        return 0
    for reason in failures:
        print(f"  {reason}")
    print(f"\nFAIL: {len(failures)} of {total} {noun} do not {verb}.")
    for line in hint:
        print(line)
    return 1
