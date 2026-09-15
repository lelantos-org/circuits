#!/usr/bin/env python3
"""Resolve every source citation in the Lean development.

Doc comments cite circom sources in full form, `src/lib/transact.circom:97-122`, or,
after a file is named earlier in the same Lean module, in the bare continuation form
`:150-151`, which resolves against that file.

Each citation is checked for:

  1. existence of the named file, including paths named without a line number;
  2. the cited lines lying within that file;
  3. the cited lines still matching the doc comment (anchoring).

Checks 1 and 2 detect renamed, deleted or shortened sources. Check 3 detects spans
that shifted because lines were inserted above them while remaining in range.

An *anchor* is an identifier inside backticks on the citing line (for example
`` `acc[0] <== 0` ``, `` `HashToAssetGen` ``, `` `is_deposit` ``) that also occurs in
the cited file. An anchor must occur within the cited span; otherwise the span has
moved. A citation with no anchors receives checks 1 and 2 only.

    python3 scripts/check-citations.py            # check, from lean/
    python3 scripts/check-citations.py --list     # also print every citation
"""

from __future__ import annotations

import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from checks import SEARCH_ROOTS, outside_checkout, report, scanned_files
from citations import Citation, citations_in, strip_comment

# Identifiers common to most circom lines, which cannot distinguish one span from another.
STOPWORDS = {"signal", "input", "output", "component", "template", "var", "for", "out", "in"}

# Anchors are taken only from backticked code on the citing line, the form doc comments
# and `FIDELITY.md` rows use to quote circom. Unquoted prose words are excluded because
# they can match unrelated spans.
QUOTED = re.compile(r"`([^`\n]+)`")
PATHLIKE = re.compile(r"[\w./-]*[\w-]/[\w./-]+")



WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_]{2,}")


def file_lines(path: str, cache: dict[str, list[str]]) -> list[str]:
    if path not in cache:
        for root in SEARCH_ROOTS:
            candidate = os.path.join(root, path)
            if os.path.exists(candidate):
                with open(candidate, encoding="utf-8", errors="replace") as handle:
                    cache[path] = handle.read().splitlines()
                break
    return cache[path]


def anchors(citation: Citation, lines: list[str]) -> set[str]:
    """Backticked words on the citing line that also occur in the cited file's code.

    Such a word is a quotation from the source and is expected within the cited span.
    """
    # Vocabulary excludes circom comments, so words appearing only in comments do not
    # anchor.
    vocabulary: set[str] = set()
    for line in lines:
        vocabulary.update(WORD.findall(strip_comment(line)))
    # Full-form paths are backticked, so paths are removed first; otherwise
    # `src/lib/note.circom:14` would anchor on "note", and a line naming two files would
    # anchor each on the other's directory.
    context = PATHLIKE.sub(" ", citation.context)
    quoted: set[str] = set()
    for fragment in QUOTED.findall(context):
        quoted.update(WORD.findall(fragment))
    return {
        word
        for word in quoted
        if word.lower() not in STOPWORDS and word in vocabulary
    }


def unresolvable(citation: Citation, source_cache: dict[str, list[str]],
                 group: list[tuple[int, int]] | None = None) -> str | None:
    """The reason this citation does not resolve, or `None` if it does."""
    target = next(
        (os.path.join(root, citation.path)
         for root in SEARCH_ROOTS
         if os.path.exists(os.path.join(root, citation.path))),
        None,
    )
    if target is None:
        return f"{citation.describe()} — no such file"
    if citation.hi == 0:  # a mention without lines: only existence is checked
        return None
    lines = file_lines(citation.path, source_cache)
    if citation.hi > len(lines):
        return f"{citation.describe()} — that file has {len(lines)} lines"

    found = anchors(citation, lines)
    if not found:
        return None
    # A doc line may carry several spans, e.g. `` `:71-78, 119-120` `` for a gadget
    # instantiated in one block and bound to an output in another. Its quotations
    # describe the spans jointly, so anchors are matched against their union.
    spans = group if group is not None else [(citation.lo, citation.hi)]
    span = "\n".join("\n".join(lines[lo - 1 : hi]) for lo, hi in spans)
    hits = {word for word in found if word in span}
    if hits:
        return None
    shown = ", ".join(sorted(found)[:4])
    hint = suggest(found, lines)
    return (f"{citation.describe()} — none of ({shown}) appear there; "
            f"the span has moved{hint}")


def suggest(found: set[str], lines: list[str]) -> str:
    """A hint for the span where the anchors occur together.

    Returns the narrowest run of lines covering the most anchors. This is accurate when
    a block moved intact and misleading when a constraint was rewritten.
    """
    hits: dict[str, list[int]] = {}
    for number, line in enumerate(lines, 1):
        body = strip_comment(line)
        for word in found:
            if word in WORD.findall(body):
                hits.setdefault(word, []).append(number)
    if not hits:
        return ""
    covered = sorted(hits)
    # Slide a 13-line window over each start line; keep the narrowest covering the most.
    best: tuple[tuple[int, int, int], int, int] | None = None
    for start in sorted({n for numbers in hits.values() for n in numbers}):
        reached = [w for w in covered if any(start <= n <= start + 12 for n in hits[w])]
        if not reached:
            continue
        end = max(n for w in reached for n in hits[w] if start <= n <= start + 12)
        score = (-len(reached), end - start, start)
        if best is None or score < best[0]:
            best = (score, start, end)
    if best is None:
        return ""
    _, start, end = best
    span = f"{start}" if start == end else f"{start}-{end}"
    return f" — try :{span}"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="print every citation checked")
    args = parser.parse_args()

    source_cache: dict[str, list[str]] = {}
    failures: list[str] = []
    total = 0
    skipped = 0

    for path in scanned_files():
        found = list(citations_in(path))
        # Spans written on one doc line, against one file, are anchored together.
        groups: dict[tuple[int, str], list[tuple[int, int]]] = {}
        for citation in found:
            if citation.hi:
                groups.setdefault((citation.line, citation.path), []).append(
                    (citation.lo, citation.hi))
        for citation in found:
            if outside_checkout(citation.path):
                skipped += 1
                continue
            total += 1
            if args.list:
                print(f"  {citation.describe()}")
            reason = unresolvable(citation, source_cache,
                                  groups.get((citation.line, citation.path)))
            if reason is not None:
                failures.append(reason)

    note = (f"{skipped} into sibling repositories not checked out here"
            if skipped else "")
    return report(failures, total, "citations", note=note)


if __name__ == "__main__":
    sys.exit(main())
