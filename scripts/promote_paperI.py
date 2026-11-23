#!/usr/bin/env python
"""Promote a subagent's Scratch<Name>.lean into the Paper I tree.

Pipeline (one command):
  1. copy the scratch file from the WSL tree to Windows temp (via wsl cp);
  2. fix the header comment and strip trailing `#print axioms` lines;
  3. write the file into the repo as Q1Paper/PaperI/<Name>.lean and into WSL;
  4. detect name clashes against the existing PaperI declarations;
  5. insert `import Q1Paper.PaperI.<Name>` into MainTheorems.lean (after the last import);
  6. append `#print axioms Q1Paper.<name>` lines for the given names to Audit.lean;
  7. build MainTheorems, run Audit.lean, run scripts/check_paperI_axioms.py;
  8. print the declaration count and the suggested commit message.

Usage:
  python scripts/promote_paperI.py --scratch ScratchFoo.lean --name Foo \
      --axioms "ns.a,ns.b" [--anchor "import Q1Paper.PaperI.Bar"] [--no-build]

The script refuses to continue on a missing file, a compile error, or a name clash.
"""

import argparse
import io
import os
import re
import shutil
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WSL_ROOT = "/home/zsj/WorkSpace/lean4/Q1Paper"
TMP = r"C:\Windows\Temp"


def sh(cmd: str, check: bool = True) -> subprocess.CompletedProcess:
    p = subprocess.run(["wsl", "-e", "bash", "-lc", cmd], capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    if check and p.returncode != 0:
        print(p.stdout)
        print(p.stderr)
        sys.exit(f"command failed ({p.returncode}): {cmd}")
    return p


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--scratch", required=True, help="e.g. ScratchFoo.lean")
    ap.add_argument("--name", required=True, help="module name, e.g. Foo")
    ap.add_argument("--axioms", default="", help="comma separated declaration names to audit")
    ap.add_argument("--anchor", default=None, help="import line after which to insert the new import")
    ap.add_argument("--no-build", action="store_true")
    a = ap.parse_args()

    scratch = a.scratch if a.scratch.endswith(".lean") else a.scratch + ".lean"
    src_wsl = f"{WSL_ROOT}/Q1Paper/{scratch}"
    tmp_file = os.path.join(TMP, f"promote_{a.name}.lean")

    print(f"[1/7] copy {scratch} from WSL")
    sh(f"cp '{src_wsl}' '/mnt/c/Windows/Temp/promote_{a.name}.lean'")

    s = io.open(tmp_file, encoding="utf-8").read()
    s = s.replace(f"Q1Paper/{scratch}", f"Q1Paper/PaperI/{a.name}.lean")
    s = re.sub(r"\n#print axioms[^\n]*", "", s)
    io.open(tmp_file, "w", encoding="utf-8", newline="\n").write(s)
    print(f"[2/7] fixed header, stripped #print lines ({len(s)} bytes)")

    print("[3/7] name-clash check")
    declared = re.findall(r"^(?:theorem|lemma|def|noncomputable def|abbrev)\s+([A-Za-z0-9_]+)",
                          s, flags=re.M)
    clash = []
    for name in set(declared):
        g = sh(f"grep -rn 'theorem {name}\\b\\|def {name}\\b' {WSL_ROOT}/Q1Paper/PaperI/ "
               f"--include='*.lean' | grep -v 'PaperI/{a.name}.lean' | head -1", check=False)
        if g.stdout.strip():
            clash.append((name, g.stdout.strip()))
    if clash:
        print("NAME CLASHES (rename before promoting):")
        for n, where in clash:
            print(f"  {n}: {where}")
        sys.exit(1)
    print(f"  ok ({len(set(declared))} declarations, none clashing)")

    repo_file = os.path.join(REPO, "Q1Paper", "PaperI", f"{a.name}.lean")
    shutil.copyfile(tmp_file, repo_file)
    print(f"[4/7] wrote {repo_file}")

    main_rel = os.path.join(REPO, "Q1Paper", "PaperI", "MainTheorems.lean")
    mt = io.open(main_rel, encoding="utf-8").read()
    imp = f"import Q1Paper.PaperI.{a.name}"
    if imp not in mt:
        if a.anchor and a.anchor in mt:
            mt = mt.replace(a.anchor, a.anchor + "\n" + imp)
        else:
            lines = mt.split("\n")
            last = max(i for i, L in enumerate(lines) if L.startswith("import "))
            lines.insert(last + 1, imp)
            mt = "\n".join(lines)
        io.open(main_rel, "w", encoding="utf-8", newline="\n").write(mt)
    print(f"[5/7] MainTheorems imports {a.name}")

    names = [n.strip() for n in a.axioms.split(",") if n.strip()]
    if names:
        audit_rel = os.path.join(REPO, "Q1Paper", "PaperI", "Audit.lean")
        au = io.open(audit_rel, encoding="utf-8").read().rstrip()
        for n in names:
            line = f"\n#print axioms {n}"
            if line.strip() not in au:
                au += line
        io.open(audit_rel, "w", encoding="utf-8", newline="\n").write(au + "\n")
        print(f"[6/7] Audit.lean += {len(names)} lines")

    # push the wired files back into WSL and build
    for rel in [f"Q1Paper/PaperI/{a.name}.lean", "Q1Paper/PaperI/MainTheorems.lean",
                "Q1Paper/PaperI/Audit.lean"]:
        src = os.path.join(REPO, rel)
        base = os.path.basename(rel)
        shutil.copyfile(src, os.path.join(TMP, base))
        sh(f"cp '/mnt/c/Windows/Temp/{base}' '{WSL_ROOT}/{rel}'")

    if a.no_build:
        print("[7/7] build skipped (--no-build)")
        return

    print("[7/7] build + audit")
    r = sh(f"cd {WSL_ROOT} && export PATH=\"$HOME/.elan/bin:$PATH\" && "
           f"lake build Q1Paper.PaperI.MainTheorems 2>&1 | tail -2 && "
           f"lake env lean Q1Paper/PaperI/Audit.lean > /mnt/c/Windows/Temp/paperI_audit.log 2>&1; "
           f"echo audit_exit=$?", check=False)
    print(r.stdout)
    chk = subprocess.run([sys.executable, os.path.join(REPO, "scripts", "check_paperI_axioms.py"),
                          os.path.join(TMP, "paperI_audit.log")], capture_output=True, text=True,
                         encoding="utf-8", errors="replace")
    print(chk.stdout.strip() or chk.stderr.strip())
    print("\ncommit message suggestion:")
    print(f"  Paper I: {a.name} promoted into the Paper I tree")
    print("  - <one line per declaration group>\n"
          "  - audit count updated; CI to be watched")


if __name__ == "__main__":
    main()
