#!/usr/bin/env python3
"""Make every module's leading comment a real Lean module docstring.

Two facts about this tree, both learned by building rather than by reading:

* nearly every file opens with a `/- ... -/` comment explaining what it proves;
* in 94 of them that comment sits **before** the `import` lines, and Lean requires imports to come
  first, so the comment cannot simply be turned into `/-!` where it stands.

So the fix is to move the block after the last import and spell it `/-!`.  That is comment text
only -- no declaration moves, so semantics cannot change -- and the build plus the axiom audit are
the check.

Usage:
    python scripts/module_docstrings.py --dry-run
    python scripts/module_docstrings.py
"""

from __future__ import annotations

import argparse
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parent.parent
DECL_RE = re.compile(r"^\s*(?:noncomputable\s+)?(?:theorem|def|abbrev|structure|lemma|instance|class)\s+")


def rewrite(text: str) -> tuple[str, str] | None:
    """Return (new_text, action) or None if the file needs nothing."""
    lines = text.splitlines(keepends=True)

    # locate the leading block comment
    start = None
    for i, line in enumerate(lines):
        s = line.strip()
        if not s or s.startswith("import "):
            continue
        if s.startswith("/-!"):
            return None  # already a module docstring
        if s.startswith("/-"):
            start = i
        break
    if start is None:
        return None

    # find its end
    end = None
    for j in range(start, len(lines)):
        if "-/" in lines[j] and not (j == start and lines[j].strip().endswith("/-!")):
            end = j
            break
    if end is None:
        return None

    block = lines[start : end + 1]
    indent = block[0][: len(block[0]) - len(block[0].lstrip())]
    first = block[0].lstrip()
    if not first.startswith("/-"):
        return None
    block[0] = indent + "/-!" + first[2:]

    imports = [i for i, l in enumerate(lines) if l.strip().startswith("import ")]
    if not imports or imports[-1] < end:
        return "".join(lines[:start] + block + lines[end + 1 :]), "converted"

    # the comment precedes the imports: move it after the last one
    rest = lines[:start] + lines[end + 1 :]
    last = max(i for i, l in enumerate(rest) if l.strip().startswith("import "))
    moved = rest[: last + 1] + ["\n"] + block + ["\n"] + rest[last + 1 :]
    return "".join(moved), "moved"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    converted, moved = 0, 0
    for path in sorted(ROOT.glob("Q1Paper/**/*.lean")):
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        res = rewrite(text)
        if res is None:
            continue
        new_text, action = res
        if action == "converted":
            converted += 1
        else:
            moved += 1
        if not args.dry_run:
            path.write_text(new_text, encoding="utf-8", newline="\n")

    verb = "would" if args.dry_run else "did"
    print(f"{verb}: {converted} converted in place, {moved} moved after the imports")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
