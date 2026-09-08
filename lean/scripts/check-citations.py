#!/usr/bin/env python3
"""Resolve every source citation in the Lean development.

Doc comments cite the circom they mirror, either in full —

    `src/lib/transact.circom:97-122`

— or, once a file has been named earlier in the same Lean module, in the bare
continuation form `:150-151`, which resolves against that file.

Three things about a citation can be checked mechanically:

  1. the file it names exists — including a path named with no line number at all,
     which is how a deleted circuit stays quoted as though it still shipped;
  2. the lines it names are inside that file;
  3. the lines it names still say what the doc comment claims they say.

The first two rot when a source is renamed, deleted or shortened. The third rots
whenever anything is inserted above the cited lines, which is far more common and
was invisible until this check existed: `src/lib/transact.circom` had drifted by 18
lines and `src/tree_update_batch.circom` by 25 and 72, every number still inside the
file and so every citation still "resolving".

Check 3 is anchoring. A doc comment that cites a line almost always quotes something
from it — `` `acc[0] <== 0` ``, `` `HashToAssetGen` ``, `` `is_deposit` ``. An
*anchor* is an identifier inside backticks on the citing line that also occurs
somewhere in the cited file: quoting it makes it that file's vocabulary rather than
the prose's, so it should occur in the cited span too. If it does not, the span moved.
A citation quoting nothing from its file is unanchored and gets checks 1 and 2 only.

    python3 scripts/check-citations.py            # check, from lean/
    python3 scripts/check-citations.py --list     # also print every citation
"""

from __future__ import annotations

import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from checks import SEARCH_ROOTS, report, scanned_files
from citations import Citation, citations_in, strip_comment

# Identifiers that appear in nearly every circom line, so finding one inside a span
# says nothing about whether it is the right span.
STOPWORDS = {"signal", "input", "output", "component", "template", "var", "for", "out", "in"}

# Anchors come only from backticked code on the citing line — the form every doc comment
# and every `FIDELITY.md` row already uses to quote the circom it mirrors. Prose words are
# not anchors: "balance" appears in a comment somewhere in `balance.circom` and would
# match a span it has nothing to do with.
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
    """Words on the citing line that belong to the cited file's vocabulary.

    A word appearing in the doc comment *and* somewhere in the circom source is a
    quotation from that source, so it should appear in the span the comment points at.
    A word appearing only in the prose says nothing about which lines are meant.
    """
    # Vocabulary from constraint lines only. A word occurring solely in circom comments
    # ("depth", "balance", "level") is prose on both sides and anchors nothing.
    vocabulary: set[str] = set()
    for line in lines:
        vocabulary.update(WORD.findall(strip_comment(line)))
    # Paths are written in backticks in the full form, so drop every path on the line
    # before looking for quotations — otherwise `src/lib/note.circom:14` anchors on
    # "note", and a line naming two files anchors each on the other's directory.
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
    if citation.hi == 0:  # a bare mention: existence is the whole check
        return None
    lines = file_lines(citation.path, source_cache)
    if citation.hi > len(lines):
        return f"{citation.describe()} — that file has {len(lines)} lines"

    found = anchors(citation, lines)
    if not found:
        return None
    # A doc line may carry several spans — `` `:71-78, 119-120` ``, one gadget
    # instantiated in one block and bound to an output in another. It has one comment,
    # so its quotations describe the blocks together; anchoring each span separately
    # would demand every word appear in every block.
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
    """Where the anchors actually are now, if they sit together somewhere.

    Only a hint: it finds the tightest run of lines covering the most anchors, which is
    right when a block moved wholesale and wrong when a constraint was genuinely
    rewritten. The person editing decides; this saves them the grep.
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
    # Slide a window over every start line and keep the narrowest span covering the most.
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

    for path in scanned_files():
        found = list(citations_in(path))
        # Spans written on one doc line, against one file, are anchored together.
        groups: dict[tuple[int, str], list[tuple[int, int]]] = {}
        for citation in found:
            if citation.hi:
                groups.setdefault((citation.line, citation.path), []).append(
                    (citation.lo, citation.hi))
        for citation in found:
            total += 1
            if args.list:
                print(f"  {citation.describe()}")
            reason = unresolvable(citation, source_cache,
                                  groups.get((citation.line, citation.path)))
            if reason is not None:
                failures.append(reason)

    return report(failures, total, "citations")


if __name__ == "__main__":
    sys.exit(main())
