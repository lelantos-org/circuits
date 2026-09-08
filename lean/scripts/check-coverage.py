#!/usr/bin/env python3
"""Every constraint the circom emits is cited by something in `lean/`.

`FIDELITY.md` opens by claiming that every `===` and `<==` in the transitive closure
of `src/4x6.circom` and `src/tree_update_batch.circom` — minus circomlib — appears in
its tables, with stated exceptions. That is the claim the whole fidelity argument
rests on, and it was checked by eye.

This checks it. `check-citations.py` asks whether each citation resolves; this asks
the other direction: whether the citations, taken together, reach every line that
emits a constraint. A constraint no citation names is a constraint the model may
simply not have — the "model omits" direction of `FIDELITY.md`'s table. That
direction is safe for `transact_sound`, which is why it can be recorded rather than
forbidden; what is not safe is not knowing.

## Covered, and covered how

A constraint line is **transcribed** when some citation of at most `NARROW` lines
contains it. Twenty is where the data separates: a citation of twenty lines or fewer
names one constraint, or one contiguous wiring block that a single model field
abstracts (`:225-243`, the nineteen `pe.<x> <== …` lines behind `PolyEvalSat`). A
wider one names a template — `insert.circom:24-95`, `merkle.circom:19-72` — and the
model field carrying it describes the template rather than transcribing its lines, so
it is not evidence about any particular line inside.

Everything else is the **residue**: uncited lines, and lines reached only by a
template-level pointer. The residue is pinned in `expected/coverage.txt` and diffed,
exactly as `check-axioms.sh` pins the trusted base. A new constraint that nothing
transcribes shows up in that diff, and the reviewer either cites it or accepts it
into the expectation with the rest.

Recording rather than forbidding is deliberate. Three parts of the circuit are
covered on purpose by a pointer or by nothing — `frontier_root.circom` is not
modelled at all, `fixed_base_mul.circom` collapses into the `escalarMul` axiom pair,
and `EmptySubtreeHashes` is a free parameter in Lean — and a hand-written allowlist
for those would need maintaining in step with a second hand-written list of reasons.
The expectation file is that list, generated.

Run:  python3 lean/scripts/check-coverage.py             # check, from lean/
      python3 lean/scripts/check-coverage.py --update    # accept a new residue
      python3 lean/scripts/check-coverage.py --summary   # per-file coverage table
"""

from __future__ import annotations

import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from checks import LEAN, REPO, scanned_files
from citations import citations_in, strip_comment

EXPECTED = os.path.join(LEAN, "expected", "coverage.txt")

# The two top-level circuits whose transitive closure is the circuit under proof.
ROOTS = ["src/4x6.circom", "src/tree_update_batch.circom"]

# `include` of a circomlib path leaves the repo; those templates are collapsed into
# axioms (`Lelantos.Meta.Assumptions`) and have no Lean counterpart by design.
INCLUDE = re.compile(r'^\s*include\s+"(?P<path>[^"]+)"')

# circom's two constraint-emitting operators. `<--` assigns without constraining and
# `-->` is its mirror; neither appears in this repo, and neither would count.
CONSTRAINT = re.compile(r"===|<==")

# A citation wider than this names a template, not a constraint. See the module note.
NARROW = 20


def closure() -> list[str]:
    """Every repo-owned circom file reachable from the two top-level circuits."""
    seen: set[str] = set()
    queue = list(ROOTS)
    while queue:
        rel = queue.pop()
        if rel in seen:
            continue
        path = os.path.join(REPO, rel)
        if not os.path.exists(path):
            print(f"FAIL: {rel} does not exist — the closure roots are stale.")
            sys.exit(1)
        seen.add(rel)
        base = os.path.dirname(rel)
        with open(path, encoding="utf-8", errors="replace") as handle:
            for line in handle:
                match = INCLUDE.match(line)
                if match is None:
                    continue
                target = os.path.normpath(os.path.join(base, match.group("path")))
                if target.startswith("src/"):
                    queue.append(target)
    return sorted(seen)


def constraint_lines(rel: str) -> list[tuple[int, str]]:
    """The (line number, text) of every constraint-emitting line in one file."""
    out: list[tuple[int, str]] = []
    with open(os.path.join(REPO, rel), encoding="utf-8", errors="replace") as handle:
        for number, text in enumerate(handle, 1):
            body = strip_comment(text)
            if CONSTRAINT.search(body):
                out.append((number, " ".join(body.split())))
    return out


def spans_by_width() -> tuple[dict[str, list[tuple[int, int]]],
                              dict[str, list[tuple[int, int]]]]:
    """Per circom file, the narrow citation spans and the wide ones, separately."""
    narrow: dict[str, list[tuple[int, int]]] = {}
    wide: dict[str, list[tuple[int, int]]] = {}
    for path in scanned_files():
        for citation in citations_in(path):
            if citation.hi == 0 or not citation.path.endswith(".circom"):
                continue
            bucket = narrow if citation.hi - citation.lo + 1 <= NARROW else wide
            bucket.setdefault(citation.path, []).append((citation.lo, citation.hi))
    return narrow, wide


def residue() -> tuple[list[str], dict[str, tuple[int, int]]]:
    """The residue, tagged, and per-file (transcribed, total) counts.

    Two tags, because they are not the same finding. `POINTER` is a constraint some
    citation reaches, but only through a span naming its whole template — the model
    describes that template rather than this line. `UNCITED` is a constraint nothing
    in `lean/` names at all, which is the one worth reading: either the model gained
    a field whose citation is missing, or the circuit has a constraint the model does
    not know about.
    """
    narrow, wide = spans_by_width()
    lines: list[str] = []
    counts: dict[str, tuple[int, int]] = {}
    for rel in closure():
        close = narrow.get(rel, [])
        far = wide.get(rel, [])
        found = constraint_lines(rel)
        hit = 0
        for number, text in found:
            if any(lo <= number <= hi for lo, hi in close):
                hit += 1
                continue
            tag = "POINTER" if any(lo <= number <= hi for lo, hi in far) else "UNCITED"
            lines.append(f"{tag} {rel}:{number}: {text}")
        counts[rel] = (hit, len(found))
    return lines, counts


def totals(counts: dict[str, tuple[int, int]]) -> tuple[int, int]:
    """Transcribed and total constraint counts, across the whole closure."""
    return (sum(hit for hit, _ in counts.values()),
            sum(all_ for _, all_ in counts.values()))


def print_summary(counts: dict[str, tuple[int, int]]) -> None:
    print(f"{'file':<40} {'transcribed':>12} {'total':>7}")
    for rel in sorted(counts):
        hit, all_ = counts[rel]
        print(f"  {rel:<38} {hit:>12} {all_:>7}")
    hit, all_ = totals(counts)
    print(f"  {'':<38} {hit:>12} {all_:>7}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--update", action="store_true",
                        help="accept the current residue into expected/coverage.txt")
    parser.add_argument("--summary", action="store_true",
                        help="print per-file transcription counts")
    args = parser.parse_args()

    lines, counts = residue()
    if args.summary:
        print_summary(counts)

    actual = "\n".join(lines) + ("\n" if lines else "")
    where = os.path.relpath(EXPECTED, REPO)

    if args.update:
        os.makedirs(os.path.dirname(EXPECTED), exist_ok=True)
        with open(EXPECTED, "w", encoding="utf-8") as handle:
            handle.write(actual)
        print(f"updated {where} ({len(lines)} lines)")
        return 0

    if not os.path.exists(EXPECTED):
        print(f"FAIL: {where} does not exist.")
        print("Create it with:  lean/scripts/check-coverage.py --update")
        return 1

    with open(EXPECTED, encoding="utf-8") as handle:
        expected = handle.read()

    if expected == actual:
        hit, all_ = totals(counts)
        uncited = sum(1 for line in lines if line.startswith("UNCITED"))
        print(f"OK: {hit} of {all_} constraints transcribed; residue "
              f"unchanged at {len(lines)} ({uncited} uncited, "
              f"{len(lines) - uncited} pointer-only).")
        return 0

    expected_set = set(expected.splitlines())
    actual_set = set(lines)
    for gone in sorted(expected_set - actual_set):
        print(f"  resolved: {gone}")
    for new in sorted(actual_set - expected_set):
        print(f"  NEW:      {new}")

    print("\nFAIL: the residue changed.")
    print("A NEW `UNCITED` line is a constraint nothing in lean/ names — usually the")
    print("model gained a field and its citation is missing, or the circuit gained a")
    print("constraint the model has not been told about. A NEW `POINTER` line is")
    print("reached only by a template-wide citation, which is evidence about the")
    print("template and not about that line. Cite it, or accept it:")
    print("  lean/scripts/check-coverage.py --update")
    return 1


if __name__ == "__main__":
    sys.exit(main())
