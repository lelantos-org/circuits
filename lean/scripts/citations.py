"""Citation scanner shared by `check-citations.py` (does each citation resolve) and
`check-coverage.py` (do the citations cover every constraint).

A citation is one of three forms:

  * `src/lib/note.circom:61` or `:61-68`: full, self-contained;
  * `` `:61-68` ``: bare, resolving against the most recent path named in the same
    file, as used by Lean field doc comments and `FIDELITY.md` tables;
  * `src/lib/note.circom` with no line number: a mention, checked only for existence.
"""

from __future__ import annotations

import os
import re
import sys
from typing import Iterator, NamedTuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from checks import REPO

# Roots a citation may point at. The lookbehind prevents a path nested in a longer
# one (`node_modules/circomlibjs/src/babyjub.js`) from matching as `src/...`.
FULL = re.compile(
    r"(?<![\w/])(?P<path>(?:src|lean|scripts|contracts)/[\w./-]+\.\w+)"
    r":(?P<lo>\d+)(?:-(?P<hi>\d+))?"
)
# A bare citation, possibly a comma-separated list of spans: `` `:71-78, 119-120` ``.
# The list form covers a model field mirroring disjoint blocks, such as a gadget
# instantiated in one place and bound to an output in another. Every span in the list
# is parsed; the closing backtick is required and terminates the list.
BARE = re.compile(r"`:(?P<spans>\d+(?:-\d+)?(?:\s*,\s*\d+(?:-\d+)?)*)`")
SPAN = re.compile(r"(?P<lo>\d+)(?:-(?P<hi>\d+))?")

# A repo-relative path named without a line number, which `FULL` does not match. Only
# existence is checked, since there is no span to anchor against.
MENTION = re.compile(
    r"(?<![\w/])(?P<path>(?:src|lean|scripts|contracts|sdk|test|vectors)/[\w./-]+\.\w+)"
    r"(?![\w:])"
)

# A markdown heading naming a source file sets the referent for the bare citations
# below it without being a citation itself. `FIDELITY.md` heads each table with the
# transcribed file and cites lines bare; without this, those rows would resolve against
# the last full citation, or have no referent and go unchecked.
#
# Only headings set the referent; paths mentioned in prose do not.
ANCHOR = re.compile(
    r"^#{1,6}\s.*?(?<![\w/])(?P<path>(?:src|lean|scripts|contracts)/[\w./-]+\.\w+)"
    r"(?![\w./-]*:\d)"
)

class Citation(NamedTuple):
    """One `path:lo-hi`, and where it was written."""

    source: str  # repo-relative file the citation appears in
    line: int  # line it appears on
    path: str  # repo-relative file it points at
    lo: int
    hi: int
    bare: bool  # written in the `:lo-hi` continuation form
    context: str  # the doc line the citation was written on, for anchoring

    def describe(self) -> str:
        if self.hi == 0:
            return f"{self.source}:{self.line}: {self.path}"
        span = f"{self.lo}" if self.lo == self.hi else f"{self.lo}-{self.hi}"
        form = f"`:{span}` against {self.path}" if self.bare else f"{self.path}:{span}"
        return f"{self.source}:{self.line}: {form}"


def citations_in(path: str) -> Iterator[Citation]:
    """Every citation in one file, in source order.

    A bare citation resolves against the most recent full citation or heading path in
    the same file. Bare citations with no preceding referent are skipped.
    """
    source = os.path.relpath(path, REPO)
    context: str | None = None
    with open(path, encoding="utf-8", errors="replace") as handle:
        for lineno, text in enumerate(handle, 1):
            for match in FULL.finditer(text):
                context = match.group("path")
                lo = int(match.group("lo"))
                hi = int(match.group("hi") or lo)
                yield Citation(source, lineno, context, lo, hi, False, text)
            for match in ANCHOR.finditer(text):
                context = match.group("path")
            for match in MENTION.finditer(text):
                yield Citation(source, lineno, match.group("path"), 0, 0, False, text)
            for match in BARE.finditer(text):
                if context is None:
                    continue
                for span in SPAN.finditer(match.group("spans")):
                    lo = int(span.group("lo"))
                    hi = int(span.group("hi") or lo)
                    yield Citation(source, lineno, context, lo, hi, True, text)


# circom comments, stripped before a line is read as code, so `===` or identifiers in
# comments count neither as constraints nor as anchoring vocabulary.
COMMENT = re.compile(r"//.*$|/\*.*?\*/", re.S)


def strip_comment(line: str) -> str:
    return COMMENT.sub(" ", line)
