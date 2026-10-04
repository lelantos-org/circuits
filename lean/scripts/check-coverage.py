#!/usr/bin/env python3
"""Check that every constraint the circom emits is cited from `lean/`.

`FIDELITY.md` states that every `===` and `<==` in the transitive closure of
`src/4x6.circom` and `src/tree_update_batch.circom`, excluding circomlib, appears in
its tables, with stated exceptions. This script verifies that claim. An uncited
constraint may be absent from the model; omissions are sound for `transact_sound`, so
they are recorded rather than forbidden.

## Coverage classes

A constraint line is **transcribed** when a citation of at most `NARROW` (20) lines
contains it. Citations of that width name one constraint or one contiguous wiring
block abstracted by a single model field (e.g. `:176-187`, the `pe.<x> <== …` lines
behind `TransactSat.compress`). Wider citations name a template
(`merkle.circom:19-72`, `batch_append.circom:107-249`) and are not evidence for any
individual line.

The **residue** is every uncited line plus every line reached only by a template-wide
citation. It is pinned in `expected/coverage.txt` and diffed, so a new untranscribed
constraint appears in review to be cited or accepted.

`EmptySubtreeHashes` is intentionally not covered: it is a free parameter in Lean. The
expectation file records it.

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

# Top-level circuits whose transitive closure is the circuit under proof.
ROOTS = ["src/4x6.circom", "src/tree_update_batch.circom"]

# circomlib includes resolve outside the repo. Poseidon is an opaque function in Lean,
# and `Num2Bits`, `IsZero`, `IsEqual` and `LessThan` are transcribed from circomlib by
# hand (`Model/Bits.lean`, `Gadgets/Comparators.lean`); none is in this closure.
INCLUDE = re.compile(r'^\s*include\s+"(?P<path>[^"]+)"')

# circom's constraint-emitting operators. `<--` assigns without constraining (as does
# its mirror `-->`) and is not counted.
CONSTRAINT = re.compile(r"===|<==")

# A citation wider than this names a template, not a constraint.
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
    """The tagged residue lines and per-file (transcribed, total) counts.

    `POINTER` marks a constraint reached only by a template-wide citation; `UNCITED`
    marks one no citation in `lean/` reaches.
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
