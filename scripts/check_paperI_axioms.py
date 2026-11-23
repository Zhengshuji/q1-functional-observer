#!/usr/bin/env python3
"""Check the Paper I axiom audit.

Reads the output of `lake env lean Q1Paper/PaperI/Audit.lean` and fails if any
declaration depends on an axiom outside the allowed set, or if no audit line is
found at all (so that a broken audit cannot pass silently).
"""

from __future__ import annotations

import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
# Lean wraps long declaration names, so footprints are matched on the
# whitespace-collapsed text instead of line by line (2026-11-24: 15 of the
# printed footprints were silently skipped because wrapped lines have no
# closing bracket on their first line).
LINE = re.compile(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]")
EMPTY = re.compile(r"'([^']+)'\s+does not depend on any axioms")


def main(argv: list[str]) -> int:
    path = argv[1] if len(argv) > 1 else "paperI_audit.log"
    try:
        with open(path, encoding="utf-8", errors="replace") as handle:
            lines = handle.read().splitlines()
    except OSError as exc:
        print(f"cannot read audit report {path!r}: {exc}", file=sys.stderr)
        return 2

    text = " ".join(line.strip() for line in lines)
    seen = 0
    problems: list[tuple[str, list[str]]] = []
    for match in LINE.finditer(text):
        seen += 1
        axioms = {a.strip() for a in match.group(2).split(",") if a.strip()}
        extra = sorted(axioms - ALLOWED)
        if extra:
            problems.append((match.group(1).strip(), extra))
    plain = len(EMPTY.findall(text))

    if seen == 0:
        print(f"no axiom report found in {path!r}", file=sys.stderr)
        return 2

    if problems:
        print(f"{len(problems)} declaration(s) use disallowed axioms:", file=sys.stderr)
        for decl, extra in problems:
            print(f"  {decl}: {', '.join(extra)}", file=sys.stderr)
        return 1

    print(f"axiom audit OK: {seen} declarations depend only on the allowed set "
          f"({', '.join(sorted(ALLOWED))}); {plain} depend on none")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
