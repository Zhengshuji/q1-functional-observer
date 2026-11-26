#!/usr/bin/env python3
"""Every declaration named in the paper's evidence table must be axiom-audited.

The paper states that every declaration named in Table 5 is checked by the kernel against only
`propext`, `Classical.choice` and `Quot.sound`.  That sentence is only true if each such declaration has a
`#print axioms` line in `Audit.lean`; a row added to the table without one would make the paper claim more
than the audit does.

This check closes that loop: the table is generated from `CLAIMS.md`, and the audit is checked against it.

    python scripts/check_audit_coverage.py
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
CLAIMS = ROOT / "Q1Paper" / "PaperI" / "S00_Interface" / "CLAIMS.md"
AUDIT = ROOT / "Q1Paper" / "PaperI" / "S00_Interface" / "Audit.lean"
ROW_RE = re.compile(r"\|\s*\*\*[^*]+\*\*\s*\(`([^`]+)`\)[^|]*\|\s*`([^`]+)`")
AUDIT_RE = re.compile(r"^#print axioms\s+(\S+)", re.M)


def main() -> int:
    if not CLAIMS.exists() or not AUDIT.exists():
        print("CLAIMS.md or Audit.lean is missing", file=sys.stderr)
        return 1

    audited = {a.rsplit(".", 1)[-1] for a in AUDIT_RE.findall(AUDIT.read_text(encoding="utf-8"))}
    rows = ROW_RE.findall(CLAIMS.read_text(encoding="utf-8"))

    checked, missing = 0, []
    for label, decl in rows:
        decl = decl.strip()
        if decl == "--":          # a paper-level row has no declaration to audit
            continue
        checked += 1
        if decl.rsplit(".", 1)[-1] not in audited:
            missing.append(f"{label}: {decl}")

    if missing:
        print(f"{len(missing)} of {checked} table declarations are not in Audit.lean:", file=sys.stderr)
        for m in missing:
            print("  " + m + "  (add '#print axioms <name>' to Audit.lean)", file=sys.stderr)
        return 1

    print(f"audit coverage: all {checked} declarations named in the table are in Audit.lean")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
