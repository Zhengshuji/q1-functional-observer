#!/usr/bin/env python3
"""Paper V's declaration count has one source of truth: `Q1Paper/PaperV/Audit.lean`.

The count used to drift between `Audit.lean`, `ClaimsCheck.lean`, `Claims.lean`, the
guide and the README (52 / 54 / 40 all appeared at once).  This check makes the drift a
build failure:

1. every `#check` of `ClaimsCheck.lean` is a `#print axioms` of `Audit.lean` and conversely
   (same set, so a rename cannot leave one table behind);
2. every sentence of the form `<n> declarations` in the Paper V documentation carries the
   same `n` as `Audit.lean`, and the word forms are not used.

    python scripts/check_paperV_counts.py
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PAPERV = ROOT / "Q1Paper" / "PaperV"
AUDIT = PAPERV / "Audit.lean"
CLAIMS_CHECK = PAPERV / "ClaimsCheck.lean"

AUDIT_RE = re.compile(r"^#print axioms\s+(\S+)\s*$", re.M)
CHECK_RE = re.compile(r"^#check\s+@?(\S+)\s*$", re.M)
COUNT_RE = re.compile(r"(\d+)\s+(?:kernel-checked\s+)?declarations")
LINES_RE = re.compile(r"(\d+)\s+lines")
WORD_RE = re.compile(r"\b(?:fifty|forty|thirty)(?:-\w+)?\b")

DOC_FILES = [
    AUDIT,
    CLAIMS_CHECK,
    PAPERV / "Claims.lean",
    ROOT / "README.md",
    ROOT / "docs" / "PAPER_V_GUIDE.md",
    ROOT / "docs" / "LEAN_MAP.md",
]

# Some files also quote Paper I/II counts; only Paper V's own sentences are policed.
CONTEXT = {
    "README.md": ("PaperV",),
    "LEAN_MAP.md": ("Axiom audit",),
}


def paper_v_text(path: pathlib.Path, text: str) -> str:
    keys = CONTEXT.get(path.name)
    if keys is None:
        return text
    return "\n".join(line for line in text.splitlines() if any(k in line for k in keys))


def main() -> int:
    audited = AUDIT_RE.findall(AUDIT.read_text(encoding="utf-8"))
    checked = CHECK_RE.findall(CLAIMS_CHECK.read_text(encoding="utf-8"))
    n = len(audited)
    problems: list[str] = []

    if sorted(audited) != sorted(checked):
        only_a = sorted(set(audited) - set(checked))
        only_c = sorted(set(checked) - set(audited))
        problems.append("Audit.lean and ClaimsCheck.lean disagree")
        for name in only_a:
            problems.append(f"  only in Audit.lean: {name}")
        for name in only_c:
            problems.append(f"  only in ClaimsCheck.lean: {name}")
    if len(set(audited)) != n:
        problems.append("duplicate declaration in Audit.lean")

    for path in DOC_FILES:
        if not path.exists():
            problems.append(f"missing file: {path.relative_to(ROOT)}")
            continue
        text = path.read_text(encoding="utf-8")
        rel = path.relative_to(ROOT)
        scoped = paper_v_text(path, text)
        for value in COUNT_RE.findall(scoped):
            if int(value) != n:
                problems.append(f"{rel}: says '{value} declarations', Audit.lean has {n}")
        for value in LINES_RE.findall(scoped):
            if int(value) != n:
                problems.append(f"{rel}: says '{value} lines', Audit.lean has {n}")
        for word in WORD_RE.findall(scoped):
            problems.append(f"{rel}: spells the count as '{word}'; use digits ({n})")

    if problems:
        print(f"Paper V count check failed (Audit.lean: {n} declarations):", file=sys.stderr)
        for p in problems:
            print("  " + p, file=sys.stderr)
        return 1

    print(f"Paper V counts: {n} declarations, Audit.lean = ClaimsCheck.lean, docs in step")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
