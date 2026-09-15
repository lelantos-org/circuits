"""Shared helpers for `check-citations.py`, `check-coverage.py` and `check-names.py`:
repository paths, the scanned file set, and result reporting.

`check-axioms.sh` and `dump-layout.sh` are shell checks (they invoke `lake`) that
follow the same output convention.
"""

from __future__ import annotations

import os
from typing import Iterator

# `lean/scripts/` -> `lean/` -> the circuits root. `contracts/` and `sdk/` are siblings
# of the circuits root, so checks search both the root and its parent.
LEAN = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
REPO = os.path.abspath(os.path.join(LEAN, ".."))
SRC = os.path.join(REPO, "src")
SEARCH_ROOTS = [REPO, os.path.dirname(REPO)]

# Sibling repositories. A citation into them resolves only when they are checked out
# alongside this one. CI checks out this repository alone, where such a citation is
# unverifiable rather than wrong, so it is skipped (as `just vectors-consumers-check`
# does) to keep the result independent of workspace layout.
EXTERNAL_ROOTS = ("contracts", "sdk")


def outside_checkout(path: str) -> bool:
    """Whether `path` names a sibling repository that is not checked out here."""
    root = path.split("/", 1)[0]
    if root not in EXTERNAL_ROOTS:
        return False
    return not any(os.path.isdir(os.path.join(r, root)) for r in SEARCH_ROOTS)


# Scanned prose: Lean sources and markdown files, checked identically.
SCANNED_SUFFIXES = (".lean", ".md")

# Build output and vendored code (`.lake` holds Mathlib).
SKIPPED_DIRS = {".lake", "build", "node_modules"}


def scanned_files() -> Iterator[str]:
    """Every Lean source and markdown file under `lean/`, in a stable order."""
    for dirpath, dirnames, filenames in os.walk(LEAN):
        dirnames[:] = [d for d in dirnames if d not in SKIPPED_DIRS]
        for name in sorted(filenames):
            if name.endswith(SCANNED_SUFFIXES):
                yield os.path.join(dirpath, name)


def report(failures: list[str], total: int, noun: str, verb: str = "resolve",
           hint: tuple[str, ...] = (), note: str = "") -> int:
    """Print the shared `OK:` / `FAIL:` report and return the exit status.

    On failure, prints one line per failure, a count, then `hint`. `note` describes
    items that were skipped and is appended to the OK line so skips remain visible.
    """
    tail = f" ({note})" if note else ""
    if not failures:
        print(f"OK: {total} {noun} {verb}{tail}.")
        return 0
    for reason in failures:
        print(f"  {reason}")
    print(f"\nFAIL: {len(failures)} of {total} {noun} do not {verb}.")
    for line in hint:
        print(line)
    return 1
