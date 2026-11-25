#!/usr/bin/env python3
"""P3: file each Paper I module under the section of the paper it belongs to.

Every assignment below was made from the module's own stated purpose, not from its name.  The paper's
sections are the organising principle:

  00_Interface     entry points, the claim index, the statement layer
  01_Compression   §3.1 -- reduce to the compressed pair (H, H_A)
  02_Subspace      §3.2-3.3 -- attainable subspaces and the subspace reduction
  03_Certificate   §3.4 -- Bezout, window matrix, Gram, and the chart/complex machinery that supports it
  04_Rationality   §4.1 -- rational bases, coefficients, bit lengths
  05_Complexity    appendix -- Bareiss, exact division, cost
  06_Algorithms    §4.1-4.2 -- charts, backend parameters, the two theorems
  07_ExistsReal    §4.4 -- Theorem 5 and the encoding

`Read/` stays where it is: it is a set of reading entries, not a section.

Usage:
    python scripts/move_to_sections.py --dry-run
    python scripts/move_to_sections.py
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PAPERI = ROOT / "Q1Paper" / "PaperI"

SECTIONS: dict[str, list[str]] = {
    "00_Interface": ["Audit", "Claims", "ClaimsCheck", "MainTheorems", "Interface"],
    "01_Compression": ["CompressionMatrix", "KernelBasis"],
    "02_Subspace": ["Claims38", "Claim4Converse", "Claim8_SumSquares", "Claim8_ElemSymm",
                    "Claim8_Disjunction", "Claim14", "Claim14_Bases", "BoundLower",
                    "RankFactorization", "SolveCriterion"],
    "03_Certificate": ["Claim11_Window", "Claim11_MinorsGram", "Claim12", "SpectralMinor",
                       "MinorRank", "BezoutBounded", "GramSystem", "GramSubspace",
                       "GramCoefficients", "GramKernel", "GramCompression", "GramFamilyBridge",
                       "GramBitLength", "CompressedGram", "MinorFamilyBridge", "RowSpanBridge",
                       "WindowSign", "FibreCard", "FibreSum", "CauchyBinet", "BasisExtraction",
                       "Claim16_Gcd"],
    "08_ChartEquivalence": ["ChartComplete", "ChartComplex", "Complexify", "ComplexSoundness",
                             "ComplexCompleteness", "ComplexCompression", "DecComplex",
                             "FromRowsMap", "ReindexAlgebraic", "ReindexSpectral", "KernelLift",
                             "Soundness"],
    "04_Rationality": ["RationalBasis", "RatDescent", "MinorCoeff", "Claim15", "Claim15_Arithmetic",
                       "BitLen", "BitLenAdd", "BitLenMatMul", "ColsConcat", "InputLen", "TauMConst",
                       "DenOne", "Claim16"],
    "05_Complexity": ["BareissBase", "BareissTableau", "BareissAssemble", "ComplexityCounts",
                      "CostCore", "CostBareiss", "TotalCost", "ExactDiv", "Hadamard",
                      "DesnanotJacobi"],
    "06_Algorithms": ["Prop4", "RenegarParams", "Thm1Cond", "Thm1Bite", "FptCore", "FptSpec",
                      "ChartCount", "DecR0Iface", "FinReindex"],
    "07_ExistsReal": ["T5DecC", "T5Complete", "T5Auto", "Theorem5"],
}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    on_disk = {p.stem for p in PAPERI.glob("*.lean")}
    assigned: dict[str, str] = {}
    for section, names in SECTIONS.items():
        for name in names:
            if name in assigned:
                print(f"assigned twice: {name}", file=sys.stderr)
                return 1
            assigned[name] = section

    missing = sorted(on_disk - set(assigned))
    # some names in the tables live in the root `Q1Paper/` project layer, which stays flat
    extra = sorted(set(assigned) - on_disk)
    if extra:
        print(f"left in the flat project layer (not under PaperI/): {extra}")
        for name in extra:
            assigned.pop(name)
    if missing:
        print(f"NOT ASSIGNED ({len(missing)}): {missing}", file=sys.stderr)
        return 1

    # rename modules: Q1Paper.PaperI.X -> Q1Paper.PaperI.<Section>.X
    moves = [(PAPERI / f"{n}.lean", PAPERI / s / f"{n}.lean") for n, s in assigned.items()]
    print(f"{len(moves)} modules in {len(SECTIONS)} sections")
    for s in SECTIONS:
        print(f"  {s}: {len(SECTIONS[s])}")

    if args.dry_run:
        return 0

    for src, dst in moves:
        dst.parent.mkdir(exist_ok=True)
        src.rename(dst)

    # rewrite every import of a moved module
    for path in list(ROOT.glob("Q1Paper/**/*.lean")) + [ROOT / "PaperI.lean", ROOT / "Q1Paper.lean"]:
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8")
        original = text
        for name, section in assigned.items():
            text = re.sub(rf"import Q1Paper\.PaperI\.{re.escape(name)}(?![\w'])",
                          f"import Q1Paper.PaperI.{section}.{name}", text)
        if text != original:
            path.write_text(text, encoding="utf-8", newline="\n")

    # the module index generator scans a fixed list of directories
    gen = ROOT / "scripts" / "generate_paperI_modules.py"
    text = gen.read_text(encoding="utf-8")
    old = '("Q1Paper/PaperI", "Paper I modules (`namespace Q1Paper.PaperI.*`)"),'
    if old in text:
        new = "\n".join(
            f'    ("Q1Paper/PaperI/{s}", "{s}"),' for s in SECTIONS
        )
        text = text.replace(old, new)
        gen.write_text(text, encoding="utf-8", newline="\n")
        print("generator directory list updated")
    else:
        print("WARNING: generator directory list not found; update it by hand", file=sys.stderr)

    print("moved and rewired; now regenerate the indexes and rebuild")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
