"""generate_audit.py -- the axiom-footprint module of Paper II, generated from the sources.

`Q1Paper/PaperII/Audit.lean` is one `#print axioms` line per declaration of the Paper II tree.
Maintaining that list by hand rots silently when a declaration is renamed, so it is generated:

    python scripts/generate_audit.py           # regenerate
    python scripts/generate_audit.py --check   # fail if stale (CI)

The script reads only declaration names (`theorem`/`def`/`abbrev`, with or without
`noncomputable`), in file order, and skips the four entry points that would be circular
(`MainTheorems`, `Audit`, `Claims`, `ClaimsCheck`).
"""

from __future__ import annotations

import io
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DIR = os.path.join(REPO, "Q1Paper", "PaperII")
OUT = os.path.join(DIR, "Audit.lean")

SKIP = {"MainTheorems.lean", "Audit.lean", "Claims.lean", "ClaimsCheck.lean"}
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s+)?(?:noncomputable\s+)?(?:theorem|def|abbrev)\s+"
    r"([A-Za-z_\u00c0-\uffff][A-Za-z0-9_'\u00c0-\uffff]*)"
)

HEADER = """/-
Q1Paper/PaperII/Audit.lean

The axiom footprint of every declaration of Paper II's Lean development.

Generated from the `PaperII/` sources (declaration names only) by
`scripts/generate_audit.py`; do not edit by hand.  Every audited declaration must
depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

import Q1Paper.PaperII.Interface
import Q1Paper.PaperII.Sandwich
import Q1Paper.PaperII.Monotone
import Q1Paper.PaperII.LowerBound
import Q1Paper.PaperII.Converse
import Q1Paper.PaperII.Saturate
import Q1Paper.PaperII.MinOrder
import Q1Paper.PaperII.GraphExtension
import Q1Paper.PaperII.GraphExtract
import Q1Paper.PaperII.Realification
import Q1Paper.PaperII.Tightness
import Q1Paper.PaperII.RealGraph
import Q1Paper.PaperII.Complexity
import Q1Paper.PaperII.Appendix

"""


def collect() -> dict[str, list[str]]:
    per_file: dict[str, list[str]] = {}
    for name in sorted(os.listdir(DIR)):
        if not name.endswith(".lean") or name in SKIP:
            continue
        got = []
        for line in io.open(os.path.join(DIR, name), encoding="utf-8"):
            m = DECL.match(line)
            if m:
                got.append(m.group(1))
        per_file[name] = got
    return per_file


def render() -> str:
    per_file = collect()
    lines = [HEADER]
    for name in sorted(per_file):
        lines.append(f"-- {name}\n")
        for d in per_file[name]:
            lines.append(f"#print axioms Q1Paper.PaperII.{d}\n")
        lines.append("\n")
    return "".join(lines)


def main() -> int:
    rendered = render()
    n = rendered.count("#print axioms")
    if "--check" in sys.argv:
        if not os.path.exists(OUT):
            print("missing", OUT)
            return 1
        if io.open(OUT, encoding="utf-8").read() != rendered:
            print("stale:", OUT)
            return 1
        print(f"Paper II audit up to date ({n} declarations)")
        return 0
    io.open(OUT, "w", encoding="utf-8", newline="\n").write(rendered)
    print(f"wrote {OUT} ({n} declarations)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
