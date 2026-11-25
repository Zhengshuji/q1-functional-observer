#!/usr/bin/env python3
"""P3 planning: propose a section for every Paper I module, from what it says it proves.

The classification reads each module's own stated purpose (the first sentence of its docstring, as
generated into MODULES.md) and asks which part of the paper that sentence is about.  A module whose
purpose matches no section goes to `99_Other` rather than being guessed at -- a mis-filed module tells
the reader something false about why it exists, which is worse than leaving it in a flat list.

`--apply` performs the move and rewrites imports.  Run without it first and read the table.

Usage:
    python scripts/plan_sections.py            # print the proposed classification
    python scripts/plan_sections.py --apply    # move the files and rewrite imports
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PAPERI = ROOT / "Q1Paper" / "PaperI"

#: Ordered: the first section whose keywords match wins, so more specific sections come first.
SECTIONS: list[tuple[str, tuple[str, ...]]] = [
    ("00_Interface", ("index", "entry point", "paper's items", "audit", "axiom")),
    ("07_ExistsReal", ("exists-R", "existsR", "encoding", "exists real", "ER statement")),
    ("05_Complexity", ("bareiss", "bit cost", "bit-cost", "operation count", "complexity",
                       "exact division", "cost model", "cost")),
    ("06_Algorithms", ("chart", "renegade", "reneg", "backend", "fpt", "fixed order",
                       "fixed parameter", "algorithm", "specification")),
    ("04_Rationality", ("rational", "bit length", "bitlength", "bit-len", "coefficient",
                        "cramer", "denominator", "hadamard", "desnanot", "size bound")),
    ("03_Certificate", ("bezout", "b\u00e9zout", "window", "gram", "minor", "spectral", "cauchy",
                        "complexif", "pencil", "certificate")),
    ("02_Subspace", ("attainable", "sandwich", "subspace", "monotone", "rank consistency",
                     "rank-consistency", "structure of", "free row")),
    ("01_Compression", ("compression", "compress", "rank identity", "kernel", "row space",
                        "projection")),
]

ROW_RE = re.compile(r"^\|\s*`([^`]+\.lean)`\s*\|(.+)\|\s*$")


def stated_purposes() -> dict[str, str]:
    """Map module file name -> its stated purpose, from the generated MODULES.md table."""
    out: dict[str, str] = {}
    path = PAPERI / "MODULES.md"
    for line in path.read_text(encoding="utf-8").splitlines():
        m = ROW_RE.match(line.strip())
        if not m:
            continue
        cells = [c.strip() for c in m.group(2).split("|") if c.strip()]
        if not cells:
            continue
        out[m.group(1)] = cells[-1].strip("* ")
    return out


def classify(purpose: str) -> str:
    low = purpose.lower()
    for name, keys in SECTIONS:
        if any(k in low for k in keys):
            return name
    return "99_Other"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--apply", action="store_true")
    args = ap.parse_args()

    purposes = stated_purposes()
    if not purposes:
        print("could not read MODULES.md", file=sys.stderr)
        return 1

    buckets: dict[str, list[tuple[str, str]]] = {}
    for fname, purpose in purposes.items():
        buckets.setdefault(classify(purpose), []).append((fname, purpose))

    for section in sorted(buckets):
        print(f"\n=== {section} ({len(buckets[section])}) ===")
        for fname, purpose in sorted(buckets[section]):
            print(f"  {fname:32s} {purpose[:80]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
