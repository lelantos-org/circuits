"""The citation scanner, shared by the checks that read citations.

`check-citations.py` asks whether each citation resolves; `check-coverage.py` asks
whether the citations together cover every constraint the circom emits. They are
different questions over the same scan, and two copies of a regex this fiddly would
drift — which is the failure mode both scripts exist to catch.

A citation is one of three forms:

  * `src/lib/note.circom:61` or `:61-68` — full, self-contained;
  * `` `:61-68` `` — bare, resolving against the most recent path named in the same
    file, which is the convention the Lean field doc comments and the `FIDELITY.md`
    tables use;
  * `src/lib/note.circom` with no line number — a mention, where existence is the
    only checkable claim.
"""

from __future__ import annotations

import os
import re
import sys
from typing import Iterator, NamedTuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from checks import REPO

# Roots a citation may point at. Anchored so that a path appearing inside a
# longer one — `node_modules/circomlibjs/src/babyjub.js` — is not mistaken for a
# repo-relative `src/...` path.
FULL = re.compile(
    r"(?<![\w/])(?P<path>(?:src|lean|scripts|contracts)/[\w./-]+\.\w+)"
    r":(?P<lo>\d+)(?:-(?P<hi>\d+))?"
)
# A bare citation, possibly a comma-separated list of spans: `` `:71-78, 119-120` ``.
# The list form is used where one model field mirrors two disjoint blocks — a gadget
# instantiated in one place and bound to an output in another. It used to be read as a
# single span, silently dropping everything after the first comma, so several fields
# that looked cited had no working citation at all; `check-coverage.py` is what
# surfaced that. The closing backtick is required, so a span list ends where it ends.
BARE = re.compile(r"`:(?P<spans>\d+(?:-\d+)?(?:\s*,\s*\d+(?:-\d+)?)*)`")
SPAN = re.compile(r"(?P<lo>\d+)(?:-(?P<hi>\d+))?")

# A repo-relative path named without a line number. `FULL` requires `:lineno`, so these
# were unchecked, and several had rotted: `src/2x2.circom` and `src/3x3.circom` were
# deleted shapes still described as deployed, and `sdk/src/bundle/snark-compression.ts`
# named a file that had moved to `test/ref/compress.ts`. Existence is all that can be
# checked here — there is no span to anchor against — but existence is what rots.
MENTION = re.compile(
    r"(?<![\w/])(?P<path>(?:src|lean|scripts|contracts|sdk|test|vectors)/[\w./-]+\.\w+)"
    r"(?![\w:])"
)

# A markdown heading naming a source file, which sets the referent for the bare
# citations under it without itself being one. `FIDELITY.md` heads each table with
# the file it transcribes and then cites lines bare; without this those rows resolve
# against whatever file was last named with a line number, which is either wrong or
# — before any full citation appears — nothing at all, leaving them unchecked.
#
# Headings only. A path mentioned in prose must not silently re-aim the rows that
# follow it, and several do exactly that.
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

    A bare citation resolves against the most recent path named in the same file,
    with or without a line number, which is the convention the Lean sources and
    `FIDELITY.md` use. Bare citations before any path have no referent and are
    skipped rather than guessed at.
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


# circom comments, stripped before a line is read as code. A `//` note mentioning
# `===` is not a constraint, and a template name quoted in a comment is not that
# template's vocabulary for anchoring purposes.
COMMENT = re.compile(r"//.*$|/\*.*?\*/", re.S)


def strip_comment(line: str) -> str:
    return COMMENT.sub(" ", line)
