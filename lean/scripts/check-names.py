#!/usr/bin/env python3
"""Resolve every Lean name the doc comments and markdown reference.

`check-citations.py` checks the circom a doc comment cites; this checks the
`Lelantos` declarations the prose names. The build does not inspect identifiers in
comments, so a renamed or unwritten theorem would otherwise go undetected.

## What counts as a claim

A backticked token is checked when it is unambiguously a Lean name:

  * `Lelantos.foo`: explicitly qualified;
  * `Upper.lower`: a dotted name with a capitalised head, i.e. a structure field or
    a namespaced theorem (`PISlot.auxDigest`, `InsertsTo.unique`);
  * a bare `snake_case` token that appears nowhere in the circom sources. Circom
    signal names (`is_deposit`, `old_root`, `actual_count`) are excluded by
    cross-referencing `src/` rather than by a hand-maintained list.

Other tokens are not checked. A bare `lowerCamel` word may be a signal or a
definition, and a dotted name under a head this development does not declare
(`Or.inr`, `ValueCommitPair.cv`) belongs to Lean or to circom. Broader rules would
produce many false positives.

`IGNORE` lists tactic and tool names the rules cannot classify.

Run:  python3 lean/scripts/check-names.py            # check, from lean/
      python3 lean/scripts/check-names.py --list     # also print every name checked
"""

from __future__ import annotations

import argparse
import itertools
import json
import os
import re
import subprocess
import sys
import tempfile
from typing import Iterator, NamedTuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from checks import LEAN, REPO, SKIPPED_DIRS, SRC, report, scanned_files

# Tactics, tools and Mathlib helpers: Lean-shaped, but not names this development owns.
IGNORE = {
    "norm_num", "push_cast", "split_ifs", "push_neg", "field_simp", "linear_combination",
    "interval_cases", "ring_nf", "simp_all", "omega", "positivity", "decide", "linarith",
    "circom_tester", "lake", "snarkjs", "run_cmd", "sorryAx", "collectAxioms",
    "node_modules", "toolchain", "check_asset_ids", "layout_parity", "pubsignal_order",
    "batch_layout_parity", "multi_asset", "tree_update_batch", "snark_compression",
    "just_picus", "picus_all",
}

# `Assumptions` is a report run by `check-axioms.sh` via `lake env lean`; `lake build`
# produces no olean for it, so it cannot be imported. It declares nothing, and its
# prose is still scanned.
NOT_BUILT = {"Lelantos.Meta.Assumptions"}

# The Lean side of the model-to-circuit signal map: each key must name a Lean field.
# `test/formal/signal_parity.test.ts` checks the circom side, that each value names a
# signal in the compiled `.sym`. Both sides are checked so neither can drift.
SIGNAL_MAP = "expected/signal-map.json"
# A backticked token that could be a Lean name. Backticks keep prose out.
TOKEN = re.compile(r"`([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)`")
CAPITALISED = re.compile(r"^[A-Z]")
FILE_SUFFIXES = (".lean", ".md", ".sol", ".ts", ".py", ".sh", ".circom", ".json", ".txt")


class Claim(NamedTuple):
    """One name, and where it was written."""

    source: str
    line: int
    name: str

    def describe(self) -> str:
        where = f"{self.source}:{self.line}" if self.line else self.source
        return f"{where}: `{self.name}`"


def declared_names() -> set[str]:
    """Every constant the built environment holds under `Lelantos`.

    Read from the environment rather than parsed from `theorem`/`def` headers, so
    structure fields, projections and namespaced results are included.
    """
    modules = sorted(lean_modules())
    source = (
        "".join(f"import {m}\n" for m in modules)
        + "open Lean in\n"
        "run_cmd do\n"
        "  let env ← Elab.Command.liftCoreM getEnv\n"
        "  let mut out : Array Name := #[]\n"
        "  for (name, _) in env.constants.toList do\n"
        "    if name.components.contains `Lelantos &&\n"
        "       (!name.isInternal || (`_private).isPrefixOf name) then\n"
        "      out := out.push name\n"
        "  for name in out do\n"
        "    IO.println name\n"
    )
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir="/tmp", delete=False) as handle:
        handle.write(source)
        path = handle.name
    try:
        result = subprocess.run(
            ["lake", "env", "lean", path],
            cwd=LEAN, capture_output=True, text=True,
        )
    finally:
        os.unlink(path)
    if result.returncode != 0 or not result.stdout.strip():
        print("FAIL: could not enumerate declarations. `lake env lean` said:")
        print(result.stderr.strip() or "(no output)")
        sys.exit(1)

    names: set[str] = set()
    for line in result.stdout.splitlines():
        if line.strip():
            add_citable(names, line.strip())

    # Module names (`Lelantos.Model.Poseidon`) are citable but are not constants, so
    # they are added separately.
    for module in all_modules():
        add_citable(names, module)
    return names


def add_citable(names: set[str], full: str) -> None:
    """Record a dotted name under every suffix it can be cited by.

    `Lelantos.PISlot.auxDigest` also matches `PISlot.auxDigest` and `auxDigest`,
    since prose may cite any suffix.
    """
    names.add(full)
    parts = full.split(".")
    for i in range(1, len(parts)):
        names.add(".".join(parts[i:]))


def all_modules() -> list[str]:
    """Every module under `Lelantos/`, importable or not.

    Non-importable modules are still citable, so the name set uses this list and
    only the imports are filtered.
    """
    modules: list[str] = []
    for dirpath, dirnames, filenames in os.walk(os.path.join(LEAN, "Lelantos")):
        dirnames[:] = [d for d in dirnames if d not in SKIPPED_DIRS]
        for name in sorted(filenames):
            if name.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dirpath, name), LEAN)
                modules.append(rel[: -len(".lean")].replace(os.sep, "."))
    return modules


def lean_modules() -> list[str]:
    """The modules the enumerator imports.

    Includes every built module, not only the `Lelantos` root, because
    `Meta.AxiomGuard` is not imported by it and its declarations are also cited.
    """
    return [m for m in all_modules() if m not in NOT_BUILT]


def circom_vocabulary() -> set[str]:
    """Every identifier appearing in the circom sources.

    A bare snake_case token found here is a quoted signal or template name, not a Lean
    name.
    """
    words: set[str] = set()
    for dirpath, dirnames, filenames in os.walk(SRC):
        dirnames[:] = [d for d in dirnames if d not in SKIPPED_DIRS]
        for name in filenames:
            if not name.endswith(".circom"):
                continue
            with open(os.path.join(dirpath, name), encoding="utf-8", errors="replace") as f:
                for line in f:
                    words.update(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", line))
    return words


def is_claim(token: str, names: set[str], circom: set[str]) -> bool:
    """Whether this backticked token asserts that a Lean declaration exists."""
    if token in IGNORE or token.endswith(FILE_SUFFIXES):
        return False
    if token.startswith("Lelantos."):
        return True
    head, _, rest = token.partition(".")
    if rest:
        # `Upper.lower`: a field or namespaced result, only under a head this development
        # declares. `Or.inr` belongs to Lean and `ValueCommitPair.cv` to circom.
        return head in names and not CAPITALISED.match(rest)
    if CAPITALISED.match(token) or "_" not in token:
        # A bare capitalised token may be a circom template or a Lean structure, and a
        # bare lowerCamel word may be a signal. Only snake_case, the form of theorem
        # names here, is classified.
        return False
    return token not in circom


def signal_map_claims() -> Iterator[Claim]:
    """Every Lean field name the signal map claims exists."""
    path = os.path.join(LEAN, SIGNAL_MAP)
    if not os.path.exists(path):
        return
    with open(path, encoding="utf-8") as handle:
        data = json.load(handle)
    source = os.path.relpath(path, REPO)
    for circuit, entry in data.items():
        if circuit.startswith("_"):
            continue
        for section in ("present", "absent", "aliases"):
            for field in entry.get(section, {}):
                yield Claim(f"{source} [{circuit}.{section}]", 0, field)


def prose_claims(names: set[str], circom: set[str]) -> Iterator[Claim]:
    """Every backticked token in `lean/` that asserts a Lean declaration exists."""
    for path in scanned_files():
        source = os.path.relpath(path, REPO)
        with open(path, encoding="utf-8", errors="replace") as handle:
            for lineno, text in enumerate(handle, 1):
                for match in TOKEN.finditer(text):
                    token = match.group(1)
                    if is_claim(token, names, circom):
                        yield Claim(source, lineno, token)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="print every name checked")
    args = parser.parse_args()

    names = declared_names()
    circom = circom_vocabulary()

    failures: list[str] = []
    total = 0

    # Signal-map keys and backticked prose names are checked in a single pass.
    for claim in itertools.chain(signal_map_claims(), prose_claims(names, circom)):
        total += 1
        if args.list:
            print(f"  {claim.describe()}")
        if claim.name not in names:
            failures.append(f"{claim.describe()} — no such declaration")

    return report(failures, total, "names", hint=(
        "Either the declaration was renamed or removed, or the prose describes a",
        "result nobody wrote. Fix the prose or write the theorem; do not add the",
        "name to IGNORE.",
    ))


if __name__ == "__main__":
    sys.exit(main())
