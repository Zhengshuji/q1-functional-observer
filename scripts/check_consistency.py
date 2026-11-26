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
TEX_TT_RE = re.compile(r"\\texttt\{((?:[^{}]|\{[^{}]*\})*)\}")
TEX_REF_RE = re.compile(r"\\(?:eq)?ref\{([^}]*)\}")
TEX_LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
TEX_CLAIM_LABEL_RE = re.compile(r"\\label\{((?:lem|prop|clm|thm|cor):[\w-]+)\}")


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
    module_names = set(modules)

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
            if ref in module_names:
                continue  # a module name (e.g. Q1Paper.PaperII.Read.All), not a declaration
            if not ref.startswith(("Q1Paper.", "Q1Subspace.", "Thm5.")):
                continue
            if ref not in declared and not any(d.startswith(ref + ".") for d in declared):
                issues.append(f"{doc.relative_to(ROOT).as_posix()}: names {ref}, "
                              f"which is not a declared name")

    # The paper is the other half of the promise: a declaration name or a \ref in the .tex has to
    # resolve, or the paper has drifted from the formalisation.  Only names containing an underscore
    # are judged, because that is this project's naming convention and it keeps Mathlib names
    # (propext, Classical.choice, Quot.sound) and ordinary words out of the check.
    tex_files = sorted((ROOT / "paper").glob("*.tex"))
    tex_labels: set[str] = set()
    for tex in tex_files:
        tex_labels |= set(TEX_LABEL_RE.findall(tex.read_text(encoding="utf-8")))
    short_declared = {d.rsplit(".", 1)[-1] for d in declared}
    for tex in tex_files:
        if tex.relative_to(ROOT).as_posix() not in keep:
            continue
        text = tex.read_text(encoding="utf-8")
        for raw in sorted(set(TEX_TT_RE.findall(text))):
            name = (raw.replace(r"\_", "_").replace(r"\allowbreak{}", "")
                       .replace("$", "").replace(r"\mathbb{C}", "\u2102").strip())
            if "_" not in name:
                continue
            if "/" in name or name.endswith(".py") or name.endswith(".lean"):
                continue  # a script or module path in a code span, not a declaration
            if name not in short_declared:
                issues.append(f"{tex.relative_to(ROOT).as_posix()}: names {name}, "
                              f"which is not a declared name")
        for label in sorted(set(TEX_REF_RE.findall(text))):
            if label not in tex_labels:
                issues.append(f"{tex.relative_to(ROOT).as_posix()}: refers to {label}, "
                              f"which no .tex labels")

    # Table 5's caption says every numbered statement appears.  That is a claim about coverage, and
    # it is checkable: every claim-like \label in the paper must be listed in the generated index.
    claims_md = ROOT / "Q1Paper" / "PaperI" / "S00_Interface" / "CLAIMS.md"
    indexed: set[str] = set()
    if claims_md.exists():
        indexed = set(re.findall(r"`((?:lem|prop|clm|thm|cor):[\w-]+)`",
                                 claims_md.read_text(encoding="utf-8")))
    claim_labels: set[str] = set()
    for tex in tex_files:
        # only Paper I: CLAIMS.md indexes Paper I, and Paper II has its own index.
        # (prefix-matching "paper_I" would also match "paper_II_...", hence the exact name)
        if tex.name != "paper_I_dec.tex":
            continue
        claim_labels |= set(TEX_CLAIM_LABEL_RE.findall(tex.read_text(encoding="utf-8")))
    for label in sorted(claim_labels - indexed):
        issues.append(f"paper: statement {label} is numbered but not in the claim index, "
                      f"so Table 5 omits it")

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
