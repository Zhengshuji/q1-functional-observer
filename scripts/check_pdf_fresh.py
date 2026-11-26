#!/usr/bin/env python3
"""Fail if a committed PDF is older than the .tex files it is built from.

The PDF is a committed deliverable, and nothing used to check that it corresponded to its source.  It
drifted twice in two days, both times because a PDF viewer held the file write-locked while the .tex
changed -- a failure that is invisible in review, since the diff of a binary looks the same either way.

The check is cheap on purpose: it compares the commit that last touched each file, so it needs no TeX
installation and no byte comparison of two builds (which is not reproducible anyway).

Dependencies follow `\\input{...}`, so `paper/table_evidence.tex` counts only for the paper that
includes it, not for every PDF in the directory.

    python scripts/check_pdf_fresh.py
"""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper"
INPUT_RE = re.compile(r"\\input\{([^}]+)\}")


def last_commit_time(path: pathlib.Path) -> int | None:
    """Unix time of the commit that last touched the file, or None if git does not track it."""
    out = subprocess.run(["git", "log", "-1", "--format=%ct", "--", path.relative_to(ROOT).as_posix()],
                         cwd=ROOT, capture_output=True, text=True)
    text = out.stdout.strip()
    return int(text) if text.isdigit() else None


def dependencies(tex: pathlib.Path) -> list[pathlib.Path]:
    """The .tex file itself plus everything it pulls in with \\input, transitively."""
    seen: list[pathlib.Path] = []
    stack = [tex]
    while stack:
        cur = stack.pop()
        if cur in seen or not cur.exists():
            continue
        seen.append(cur)
        for name in INPUT_RE.findall(cur.read_text(encoding="utf-8")):
            rel = name if name.endswith(".tex") else name + ".tex"
            stack.append(PAPER / rel)
    return seen


def main() -> int:
    pdfs = sorted(PAPER.glob("*.pdf"))
    if not pdfs:
        print("no PDFs to check")
        return 0

    problems: list[str] = []
    for pdf in pdfs:
        source = PAPER / (pdf.stem + ".tex")
        if not source.exists():
            problems.append(f"{pdf.name}: no {source.name} to build it from")
            continue
        pdf_time = last_commit_time(pdf)
        if pdf_time is None:
            problems.append(f"{pdf.name}: not tracked by git")
            continue
        stale_against = []
        for dep in dependencies(source):
            dep_time = last_commit_time(dep)
            if dep_time is not None and dep_time > pdf_time:
                stale_against.append(dep.name)
        if stale_against:
            problems.append(f"{pdf.name}: older than " + ", ".join(stale_against))
        else:
            print(f"{pdf.name}: up to date with {', '.join(d.name for d in dependencies(source))}")

    if problems:
        print("\nSTALE PDFs -- rebuild with two pdflatex passes:", file=sys.stderr)
        for p in problems:
            print("  " + p, file=sys.stderr)
        return 1
    print(f"all {len(pdfs)} PDFs are at least as new as their sources")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
