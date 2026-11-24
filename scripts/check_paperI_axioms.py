#!/usr/bin/env python3
"""Check the Paper I axiom audit.

Reads the output of `lake env lean Q1Paper/PaperI/Audit.lean` and fails if

  * any declaration depends on an axiom outside the allowed set;
  * any audit line cannot be parsed (a silently skipped line is a silently unchecked one);
  * the number of parsed footprints differs from the number of `#print axioms` commands in
    `Audit.lean`, when that file is given as the second argument.

Both extra checks exist because of a real defect: the older version matched
`'([^']+)' depends on axioms:` line by line, which (a) skipped footprints whose axiom list was
wrapped onto the next line, and (b) never matched names containing an apostrophe, such as
`rank_vstack_add_rank_mul'`.  Those two declarations were printed but never checked.  The audit
therefore reported "412 declarations" while `Audit.lean` contains 416 `#print axioms` commands.

Usage:
    python scripts/check_paperI_axioms.py <log> [Audit.lean]
"""

from __future__ import annotations

import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

# `.+?` (not `[^']+`) so that names ending in an apostrophe are captured whole; the log is joined
# into one line first, so a wrapped axiom list is matched as well.
LINE = re.compile(r"'(?P<decl>\S+?)'\s+depends on axioms:\s*\[(?P<axioms>[^\]]*)\]")
EMPTY = re.compile(r"'(?P<decl>\S+?)'\s+does not depend on any axioms")
PRINT = re.compile(r"^#print axioms\s+(\S+)\s*$", re.M)


def main(argv: list[str]) -> int:
    path = argv[1] if len(argv) > 1 else "paperI_audit.log"
    try:
        with open(path, encoding="utf-8", errors="replace") as handle:
            lines = handle.read().splitlines()
    except OSError as exc:
        print(f"cannot read audit report {path!r}: {exc}", file=sys.stderr)
        return 2

    # Collapse the wrapped output into one string: Lean wraps long declaration names and long
    # axiom lists, and matching line by line silently lost both.
    text = " ".join(line.strip() for line in lines)

    seen = 0
    problems: list[tuple[str, list[str]]] = []
    for match in LINE.finditer(text):
        seen += 1
        axioms = {a.strip() for a in match.group("axioms").split(",") if a.strip()}
        extra = sorted(axioms - ALLOWED)
        if extra:
            problems.append((match.group("decl").strip(), extra))
    plain = {m.group("decl").strip() for m in EMPTY.finditer(text)}

    if seen == 0:
        print(f"no axiom report found in {path!r}", file=sys.stderr)
        return 2

    # every printed footprint must have been parsed
    if len(argv) > 2:
        audit_lean = argv[2]
        try:
            with open(audit_lean, encoding="utf-8") as handle:
                commands = PRINT.findall(handle.read())
        except OSError as exc:
            print(f"cannot read {audit_lean!r}: {exc}", file=sys.stderr)
            return 2
        names = {m.group("decl").strip() for m in LINE.finditer(text)}
        n_plain = text.count("does not depend on any axioms")
        # a command is accounted for if it was parsed with an axiom list, OR if the log says
        # explicitly that it depends on none (matched by name, not by the shape of the sentence)
        missing = [c for c in commands
                   if c not in names and f"'{c}' does not depend" not in text]
        if missing:
            print(f"{len(missing)} of {len(commands)} #print axioms commands were NOT parsed:",
                  file=sys.stderr)
            for name in missing[:20]:
                print(f"  {name}", file=sys.stderr)
            return 1
        if len(commands) != seen + n_plain:
            print(f"count mismatch: {len(commands)} commands, {seen} with axioms, "
                  f"{n_plain} without", file=sys.stderr)
            return 1
        total = len(commands)
    else:
        total = seen + len(plain)

    if problems:
        print(f"{len(problems)} declaration(s) use disallowed axioms:", file=sys.stderr)
        for decl, extra in problems:
            print(f"  {decl}: {', '.join(extra)}", file=sys.stderr)
        return 1

    print(f"axiom audit OK: {total} declarations audited ({seen} depend only on the allowed set, "
          f"{len(plain)} on none)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
