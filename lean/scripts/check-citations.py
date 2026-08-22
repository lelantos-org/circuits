#!/usr/bin/env python3
"""Resolve every source citation in the Lean development.

Doc comments cite the circom they mirror, either in full —

    `src/lib/transact.circom:97-122`

— or, once a file has been named earlier in the same Lean module, in the bare
continuation form `:150-151`, which resolves against that file.

Two things about a citation can be checked mechanically: the file it names
exists, and the lines it names are inside that file. Both are what rots when a
source is renamed, deleted, or shortened. What cannot be checked is whether the
cited lines say what the doc comment claims, so a drift of a few lines inside a
surviving file still passes.

    python3 scripts/check-citations.py            # check, from lean/
    python3 scripts/check-citations.py --list     # also print every citation
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from typing import Iterator, NamedTuple

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
LEAN = os.path.join(REPO, "lean")

# Roots a citation may point at. Anchored so that a path appearing inside a
# longer one — `node_modules/circomlibjs/src/babyjub.js` — is not mistaken for a
# repo-relative `src/...` path.
FULL = re.compile(
    r"(?<![\w/])(?P<path>(?:src|lean|scripts|contracts)/[\w./-]+\.\w+)"
    r":(?P<lo>\d+)(?:-(?P<hi>\d+))?"
)
BARE = re.compile(r"`:(?P<lo>\d+)(?:[-,]\s*(?P<hi>\d+))?")

SCANNED_SUFFIXES = (".lean", ".md")
SKIPPED_DIRS = {".lake", "build", "node_modules"}


class Citation(NamedTuple):
    """One `path:lo-hi`, and where it was written."""

    source: str  # repo-relative file the citation appears in
    line: int  # line it appears on
    path: str  # repo-relative file it points at
    lo: int
    hi: int
    bare: bool  # written in the `:lo-hi` continuation form

    def describe(self) -> str:
        span = f"{self.lo}" if self.lo == self.hi else f"{self.lo}-{self.hi}"
        form = f"`:{span}` against {self.path}" if self.bare else f"{self.path}:{span}"
        return f"{self.source}:{self.line}: {form}"


def scanned_files() -> Iterator[str]:
    for dirpath, dirnames, filenames in os.walk(LEAN):
        dirnames[:] = [d for d in dirnames if d not in SKIPPED_DIRS]
        for name in sorted(filenames):
            if name.endswith(SCANNED_SUFFIXES):
                yield os.path.join(dirpath, name)


def citations_in(path: str) -> Iterator[Citation]:
    """Every citation in one file, in source order.

    A bare citation resolves against the most recent full one in the same file,
    which is the convention the Lean sources use. Bare citations before any full
    one have no referent and are skipped rather than guessed at.
    """
    source = os.path.relpath(path, REPO)
    context: str | None = None
    with open(path, encoding="utf-8", errors="replace") as handle:
        for lineno, text in enumerate(handle, 1):
            for match in FULL.finditer(text):
                context = match.group("path")
                lo = int(match.group("lo"))
                hi = int(match.group("hi") or lo)
                yield Citation(source, lineno, context, lo, hi, bare=False)
            for match in BARE.finditer(text):
                if context is None:
                    continue
                lo = int(match.group("lo"))
                hi = int(match.group("hi") or lo)
                yield Citation(source, lineno, context, lo, hi, bare=True)


def unresolvable(citation: Citation, line_counts: dict[str, int]) -> str | None:
    """The reason this citation does not resolve, or `None` if it does."""
    target = os.path.join(REPO, citation.path)
    if not os.path.exists(target):
        return f"{citation.describe()} — no such file"
    if citation.path not in line_counts:
        with open(target, "rb") as handle:
            line_counts[citation.path] = sum(1 for _ in handle)
    length = line_counts[citation.path]
    if citation.hi > length:
        return f"{citation.describe()} — that file has {length} lines"
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="print every citation checked")
    args = parser.parse_args()

    line_counts: dict[str, int] = {}
    failures: list[str] = []
    total = 0

    for path in scanned_files():
        for citation in citations_in(path):
            total += 1
            if args.list:
                print(f"  {citation.describe()}")
            reason = unresolvable(citation, line_counts)
            if reason is not None:
                failures.append(reason)

    if failures:
        for reason in failures:
            print(f"  {reason}")
        print(f"\nFAIL: {len(failures)} of {total} citations do not resolve.")
        return 1

    print(f"OK: {total} citations resolve.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
