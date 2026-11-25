#!/usr/bin/env python3
"""Consistency check for the Lean tree and the documents that describe it.

Three things can drift independently after a rename, and all three have drifted at least once during
the P0-P2 work:

1. a module's docstring opens with its own path, which goes stale when the file moves;
2. a document mentions a module that no longer exists;
3. a document mentions a fully-qualified declaration name that no longer exists.

This script reports all three and exits non-zero if any is found, so CI can hold the line.

Usage:
    python scripts/check_consistency.py
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
DECL_RE = re.compile(r"^\s*(?:noncomputable\s+)?(?:theorem|def|abbrev|structure|lemma|instance)\s+([\w'!?]+)")
NS_OPEN_RE = re.compile(r"^\s*namespace\s+(\S+)\s*$")
NS_CLOSE_RE = re.compile(r"^\s*end\s+(\S+)\s*$")
PATH_RE = re.compile(r"^Q1Paper/\S+\.lean$")
DOC_REF_RE = re.compile(r"`([A-Za-z][\w'.]*)`")
MODULE_REF_RE = re.compile(r"\b([A-Za-z][\w]*)\.lean\b")


def tracked() -> set[str]:
    """Paths git knows about, so the check ignores local-only files (they are gitignored)."""
    import subprocess
    out = subprocess.run(["git", "ls-files"], cwd=ROOT, capture_output=True, text=True)
    return {line.strip() for line in out.stdout.splitlines() if line.strip()}


def scan() -> tuple[dict[str, pathlib.Path], set[str], dict[str, str]]:
    """Return (modules by dotted name, declared fully-qualified names, docstring path problems)."""
    modules: dict[str, pathlib.Path] = {}
    declared: set[str] = set()
    path_problems: dict[str, str] = {}
    for path in sorted(list(ROOT.glob("Q1Paper/**/*.lean")) + list(ROOT.glob("*.lean"))):
        rel = path.relative_to(ROOT).as_posix()
        modules[rel.removesuffix(".lean").replace("/", ".")] = path

        text = path.read_text(encoding="utf-8")
        # 1. the docstring's self-reference
        for line in text.splitlines()[:20]:
            stripped = line.strip()
            if PATH_RE.match(stripped):
                if stripped != rel:
                    path_problems[rel] = stripped
                break

        # 2. fully-qualified declaration names, by tracking namespace nesting
        stack: list[str] = []
        for line in text.splitlines():
            m = NS_OPEN_RE.match(line)
            if m:
                stack.append(m.group(1))
                continue
            m = NS_CLOSE_RE.match(line)
            if m and stack and stack[-1] == m.group(1):
                stack.pop()
                continue
            m = DECL_RE.match(line)
            if m:
                declared.add(".".join(stack + [m.group(1)]))
    return modules, declared, path_problems


def main() -> int:
    modules, declared, path_problems = scan()
    module_basename = {}
    for dotted in modules:
        module_basename[dotted.rsplit(".", 1)[-1]] = dotted

    issues: list[str] = []
    for rel, stale in sorted(path_problems.items()):
        issues.append(f"docstring self-path: {rel} says {stale}")

    keep = tracked()
    docs = [ROOT / "README.md"] + sorted((ROOT / "docs").glob("*.md")) + sorted(ROOT.glob("*.lean"))
    for doc in docs:
        if doc.relative_to(ROOT).as_posix() not in keep:
            continue  # gitignored: a local record, not something the repository promises
        text = doc.read_text(encoding="utf-8")
        for name in sorted(set(MODULE_REF_RE.findall(text))):
            if name not in module_basename:
                issues.append(f"{doc.relative_to(ROOT).as_posix()}: mentions module {name}.lean, "
                              f"which does not exist")
        for ref in sorted(set(DOC_REF_RE.findall(text))):
            # only judge things that look like a fully-qualified Lean name in this project
            if ref.endswith(".lean"):
                continue  # a module path in a code span, not a declaration
            if not ref.startswith(("Q1Paper.", "Q1Subspace.", "Thm5.")):
                continue
            if ref not in declared and not any(d.startswith(ref + ".") for d in declared):
                issues.append(f"{doc.relative_to(ROOT).as_posix()}: names {ref}, "
                              f"which is not a declared name")

    print(f"modules: {len(modules)}, declared names: {len(declared)}")
    if issues:
        print(f"INCONSISTENCIES: {len(issues)}")
        for i in issues:
            print("  " + i)
        return 1
    print("consistent: every docstring self-path, module mention and declaration reference resolves")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
