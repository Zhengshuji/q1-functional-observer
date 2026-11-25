#!/usr/bin/env python3
"""P2: rename a Lean module and fix every reference to it.

Lean identifies a module by its path, so renaming a file changes its module name, and every `import`
of it, and any tool that stores module paths.  It does *not* change declaration names: those are
qualified by namespace, and the modules renamed here use the flat `Q1Paper.PaperI` namespace.  So the
edit is confined to file names and `import` lines — which is why the axiom audit is unaffected.

Rename in small groups and run the full verification after each: build, audit, the four generated
indexes.  A group that fails is reverted with `git checkout -- Q1Paper` before trying the next.

Usage:
    python scripts/rename_module.py --dry-run Old1 New1 [Old2 New2 ...]
    python scripts/rename_module.py Old1 New1 [Old2 New2 ...]
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
IMPORT_RE = re.compile(r"^(\s*import\s+)(\S+)\s*$", re.M)


def find_module(name: str) -> pathlib.Path | None:
    """Locate `Q1Paper/PaperI/<name>.lean` or `Q1Paper/<name>.lean`."""
    for rel in (f"Q1Paper/PaperI/{name}.lean", f"Q1Paper/{name}.lean"):
        p = ROOT / rel
        if p.exists():
            return p
    return None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--namespace", action="store_true",
                    help="also rename Q1Paper.PaperI.<Old> to Q1Paper.PaperI.<New>: needed when the "
                         "module has its own namespace (P0 gave 15 of them one), because that changes "
                         "fully-qualified declaration names and therefore Audit.lean and CLAIMS.md")
    ap.add_argument("pairs", nargs="+", help="Old New [Old New ...] (bare module names)")
    args = ap.parse_args()

    if len(args.pairs) % 2:
        print("need an even number of names (Old New pairs)", file=sys.stderr)
        return 2
    pairs = [(args.pairs[i], args.pairs[i + 1]) for i in range(0, len(args.pairs), 2)]

    plans = []
    for old, new in pairs:
        src = find_module(old)
        if src is None:
            print(f"not found: {old}", file=sys.stderr)
            return 1
        dst = src.with_name(new + ".lean")
        if dst.exists():
            print(f"target exists: {dst.relative_to(ROOT)}", file=sys.stderr)
            return 1
        prefix = "Q1Paper.PaperI." if "PaperI" in src.parts else "Q1Paper."
        plans.append((src, dst, prefix + old, prefix + new))
        print(f"  {prefix}{old}  ->  {prefix}{new}")

    touched: list[str] = []

    def fix(m: re.Match[str], old_mod: str, new_mod: str) -> str:
        # return the match verbatim unless it is the module being renamed, so that no other line is
        # rewritten (a blanket substitution would strip trailing spaces across the whole tree)
        return m.group(1) + new_mod if m.group(2) == old_mod else m.group(0)

    for path in sorted(list(ROOT.glob("Q1Paper/**/*.lean")) + [ROOT / "Q1Paper" / "PaperI" / "CLAIMS.md"]
                       + sorted((ROOT / "scripts").glob("*.py"))):
        text = path.read_text(encoding="utf-8")
        original = text
        for _src, _dst, old_mod, new_mod in plans:
            text = IMPORT_RE.sub(lambda m, o=old_mod, n=new_mod: fix(m, o, n), text)
            if args.namespace:
                # covers `namespace`, `end`, `open`, fully-qualified names in Audit.lean, and the
                # declaration names in the claims generator's table.
                # The lookahead matters: Reindex is a prefix of Reindex2, so a plain replace would
                # corrupt the longer name.
                text = re.sub(re.escape(old_mod) + r"(?![\w'])", new_mod.replace("\\", r"\\"), text)
        if text != original:
            touched.append(path.relative_to(ROOT).as_posix())
            if not args.dry_run:
                path.write_text(text, encoding="utf-8", newline="\n")

    if not args.dry_run:
        for src, dst, _o, _n in plans:
            # the module docstring normally opens with its own path; that line goes stale on rename
            text = src.read_text(encoding="utf-8")
            text = text.replace(src.relative_to(ROOT).as_posix(), dst.relative_to(ROOT).as_posix())
            dst.write_text(text, encoding="utf-8", newline="\n")
            src.unlink()

    verb = "would rewrite" if args.dry_run else "rewrote"
    print(f"{verb} {len(touched)} files; " + ("no files moved (dry run)" if args.dry_run else f"{len(plans)} files moved"))
    for name in touched:
        print(f"  {name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
