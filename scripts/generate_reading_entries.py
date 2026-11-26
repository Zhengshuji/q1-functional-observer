#!/usr/bin/env python3
"""Generate the per-section reading entries for Paper I.

The four existing indexes answer "where is this paper item".  None of them answers "in what order do I
read the proof, and what is each step".  These files do, and they are generated so they cannot drift:
every step is a `#check`, so renaming a declaration turns the entry into a compile error.

Layout: one file per section of the paper, under `Q1Paper/PaperI/Read/`, plus `All.lean` which imports
them so that a single `lean` invocation checks the whole set.

Usage:
    python scripts/generate_reading_entries.py           # regenerate
    python scripts/generate_reading_entries.py --check    # fail if stale (CI)
"""

from __future__ import annotations

import argparse
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "Q1Paper" / "PaperI" / "Read"

# section -> (file, title, paper anchor, problem, prior, [(step title, declaration)], next)
SECTIONS = [
    (
        "S01_Compression.lean",
        "§3.1 Compression and the pencil criterion",
        "sec:compression",
        "Reduce the two conditions on the free block $\\mathcal L$ to conditions on the small compressed\n"
        "pair $(H, H_A) = (\\mathcal L N, LA\\,N)$, where $N$ is a basis of $\\ker[C; CA]$.",
        "Nothing; this is the entry point.",
        [
            ("the rank identity that makes the dimension bookkeeping exact",
             "Q1Paper.rank_vstack_add_rank_mul"),
            ("stacking does not change the row space it spans",
             "Q1Subspace.rowSpace_fromRows"),
            ("$(5a)$ is a row-space inclusion, not merely a rank test",
             "Q1Paper.PaperI.rawAlgebraic_iff_rowSpace"),
            ("so the raw conditions are equivalent to the compressed ones", 
             "Q1Paper.PaperI.DEC_iff_compressed"),
        ],
        "§3.2 now asks which pairs $(H, H_A)$ are attainable at all.",
    ),
    (
        "S02_Attainable.lean",
        "§3.2 The space of attainable row pairs",
        "sec:free",
        "Describe the set of subspaces $W$ that some free block $R$ can produce, and count the degrees of\n"
        "freedom.  Without this, a search over subspaces would not be justified.",
        "The compressed pair from §3.1.",
        [
            ("the attainable pairs have dimension $d_0$, giving $\\kappa_{\\text{obs}} = r d_0$",
             "Q1Paper.claim3_attainable"),
            ("every attainable $W$ sits between $W_0$ and $T$", "Q1Paper.claim4_sandwich"),
            ("and conversely every such $W$ is attained by some $R$",
             "Q1Paper.claim4_converse"),
        ],
        "§3.3 may therefore quantify over subspaces $W$ instead of over matrices $R$.",
    ),
    (
        "S03_Subspace.lean",
        "§3.3 The subspace reduction",
        "sec:subspace",
        "Show that $(5a)$ and $(5b)$ depend only on $W$, so that one test per subspace suffices, and\n"
        "record the structural constraints on a feasible $W$.",
        "The subspace picture from §3.2.",
        [
            ("the conditions depend only on $W$, never on which $R$ produced it",
             "Q1Paper.claim5_conditions_depend_on_W"),
            ("a feasible $W$ satisfies $\\omega + 1 \\le \\dim W \\le 2\\omega$", "Q1Paper.claim6_struct"),
            ("the problem is monotone in the order", "Q1Paper.claim7_DEC_succ"),
            ("the rank-consistency criterion, which eliminates the intermediate $B$",
             "Q1Paper.claim8_rank_consistency"),
            ("its combinatorial form, as a disjunction over the elementary symmetric functions",
             "Q1Paper.PaperI.Claim8_ElemSymm.claim8_disjunction"),
        ],
        "§3.4 turns the spectral condition on a fixed $W$ into a finite algebraic certificate.",
    ),
    (
        "S04_Certificate.lean",
        "§3.4 The finite certificate",
        "sec:certificate",
        "Replace `rank $(\\lambda H - H_A) = \\omega$ for every complex $\\lambda$' — a quantifier over\n"
        "$\\lambda$ — by a finite system that a real-algebraic solver can decide.",
        "The subspace reduction from §3.3.",
        [
            ("real Bézout multipliers exist, so the certificate can stay real",
             "Q1Paper.exists_bezout_family_real"),
            ("the window matrix's row space is the window set", 
             "Q1Paper.rowSpace_windowMatrix_eq_windowSet"),
            ("$(5b)$ is equivalent to solvability of the Gram system $Z^{\\mathsf T} Z x = e_0$",
             "Q1Paper.PaperI.claim11_iff_gram"),
            ("the same for a full-column-rank pencil $\\lambda X - G$, the chart coordinates",
             "Q1Paper.PaperI.claim12_iff_gram"),
            ("those two are stated for the injective-indexed minors; every subset pair has "
             "$(\\omega!)^2$ preimages, so no subset row is missed",
             "Q1Paper.PaperI.imagePair_surjective"),
            ("hence the two window matrices span the same rows, and the certificate transfers "
             "to the subset family the paper's Cauchy--Binet argument uses",
             "Q1Paper.PaperI.rowSpace_windowInj_eq_windowSub"),
            ("which is Claim 11 for the subset-indexed Gram matrix",
             "Q1Paper.PaperI.claim11_iff_gram_subset"),
            ("and Claim 12 in the same form",
             "Q1Paper.PaperI.claim12_iff_gram_subset"),
        ],
        "§4 needs the certificate to be rational and small; that is §4.1.",
    ),
    (
        "S05_FixedOrder.lean",
        "§4.1 Fixed order: rationality, size, and the bound",
        "sec:fixedq",
        "Make the certificate rational and bound every coefficient, then feed it to a decision procedure\n"
        "whose cost is known.",
        "The certificate from §3.4.",
        [
            ("rational bases with explicit size bounds", "Q1Paper.PaperI.exists_rational_bases_bounded"),
            ("the chart data, including bases of $T$, $S$ and $W_0$", "Q1Paper.PaperI.Chart14.exists_chart_bases"),
            ("every coefficient of every maximal minor is bounded",
             "Q1Paper.MinorCoeff.pencilMinor_coeff_bitLen_le"),
            ("the compressed Gram entries are bounded too",
             "Q1Paper.PaperI.compressedGram_entry_bitLen_le"),
            ("the degenerate $r = 0$ branch reduces to the system (R0)", "Q1Paper.prop4_r0_iff_spectral"),
            ("and the resulting bound is $\\mathcal L^{O(q^2)}$",
             "Q1Paper.theorem1_conditional_params_fixedDeg"),
        ],
        "§4.2 re-does the count with $\\ell = \\operatorname{rank}(AN)$ as the parameter.",
    ),
    (
        "S06_FixedParameter.lean",
        "§4.2 Fixed parameter",
        "sec:fpt",
        "Replace the order $q$ by the parameter $\\ell$, and obtain a bound that is fixed-parameter\n"
        "tractable rather than merely polynomial for fixed order.",
        "The chart enumeration and cost model of §4.1.",
        [
            ("the FPT bound, conditional on the declared backend",
             "Q1Paper.theorem2_fpt_conditional"),
        ],
        "§4.3 and §4.4 handle the degenerate branch and the $\\exists\\mathbb R$ statement.",
    ),
    (
        "S07_ZeroFreeRow.lean",
        "§4.3 The zero-free-row case",
        "sec:zero",
        "The general chart machinery is vacuous when there are no free rows; this branch is handled\n"
        "separately, and the paper's claim is a chain of equivalences.",
        "Nothing from §4.1–4.2; this is a separate branch.",
        [
            ("the spectral condition, the absence of a common root, and a constant gcd agree",
             "Q1Paper.claim16_i_iff_iii"),
            ("a constant gcd yields a rational left inverse of the required degree",
             "Q1Paper.claim16_iii_implies_iv_of_gcd_isConst"),
        ],
        "§4.4 packages the whole decision problem as an $\\exists\\mathbb R$ statement.",
    ),
    (
        "S08_ExistsReal.lean",
        "§4.4 Membership in the existential theory of the reals",
        "sec:existsr",
        "State the decision problem as the existence of an encoding witness, with no abstract hypothesis\n"
        "left over.",
        "The certificate of §3.4 and the bounds of §4.1.",
        [
            ("the decision problem is equivalent to the existence of an encoding witness",
             "Q1Paper.Thm5.DECℂ_iff_exists_encodes_auto"),
        ],
        "The appendix accounts for the bit cost of the exact-arithmetic layer.",
    ),
    (
        "S09_BitCost.lean",
        "Appendix: explicit size bounds and bit cost",
        "app:size",
        "Account for the cost of the exact-arithmetic layer: the Bareiss tableau and its bit-length\n"
        "behaviour, which is what makes the bounds in §4 concrete rather than asymptotic.",
        "The size bounds of §4.1.",
        [
            ("the $r = 0$ system's quadratic cost, with exact integer division",
             "Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_quadratic"),
            ("the paper's $O(n^{21} L^2)$ bit-cost bound",
             "Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_n21_L2"),
        ],
        "Nothing; this closes the paper.",
    ),
    (
        "S10_ChartEquivalence.lean",
        "The chart equivalence: from the certificate to the decision problem",
        "sec:algorithms",
        "The paper's condition (5b) quantifies over the **complex** numbers, and the chart argument\n"
        "returns a witness — a point of `eq:phi` — rather than a truth value.  This section states the\n"
        "specification those two facts require, and proves that a chart point and the specification\n"
        "imply each other.  It is the bridge between the certificate of §3.4 and the algorithms of §4.",
        "The compressed conditions of §3.4 and the chart data of §3.4.",
        [
            ("the real-to-complex spectral bridge, so the paper's data can meet the certificate",
             "Q1Paper.PaperI.ChartComplex.complex_spectral_implies_real"),
            ("the specification itself: `(5b)` over the complex numbers", 
             "Q1Paper.PaperI.DecComplex.complexDEC"),
            ("complex implies real, and that is the only direction that holds",
             "Q1Paper.PaperI.DecComplex.dec_of_complexDEC"),
            ("a chart point witnesses the (real-lambda) decision problem",
             "Q1Paper.PaperI.Soundness.dec_of_phiPoint"),
            ("a chart point witnesses the paper's own specification",
             "Q1Paper.PaperI.ComplexSoundness.decComplex_of_phiPoint"),
            ("the complex condition compresses, so the two levels can be compared",
             "Q1Paper.PaperI.ComplexCompression.compressed_of_spectralComplexRaw"),
            ("and conversely the specification yields a chart point (for `omega >= 1`)",
             "Q1Paper.PaperI.ComplexCompleteness.phiPoint_of_complexDEC"),
            ("the chart point built from the two compressed conditions",
             "Q1Paper.PaperI.ChartComplete.phiPoint_of_conditions"),
            ("the complexified kernel basis spans the complex kernel",
             "Q1Paper.PaperI.KernelLift.range_mulVecLin_eq_ker_map_complex"),
            ("row reindexing, which lets the chart speak about `[L0; R]`", 
             "Q1Paper.PaperI.ReindexAlgebraic.rawAlgebraic_submatrix"),
            ("the same for the spectral condition",
             "Q1Paper.PaperI.ReindexSpectral.rawSpectral_submatrix"),
            ("and `fromRows` commuting with the entrywise map, which makes the reindexing work",
             "Q1Paper.PaperI.FromRowsMap.fromRows_map"),
        ],
        "Nothing: this closes the formalisation.  The cost of acting on the witness is §4.1's subject.",
    ),
]


#: What each declaration *is*, so a reader can tell the result from the scaffolding.  Three roles:
#: a **tool** is general linear algebra that could be stated without this problem; a **bridge** moves
#: between two formulations of the same thing; a **core** lemma is mathematical content specific to
#: this paper.  A declaration absent from this table renders without a tag.
ROLES: dict[str, str] = {
    "Q1Paper.rank_vstack_add_rank_mul": "tool",
    "Q1Subspace.rowSpace_fromRows": "tool",
    "Q1Paper.PaperI.rawAlgebraic_iff_rowSpace": "bridge",
    "Q1Paper.PaperI.DEC_iff_compressed": "core",
    "Q1Paper.claim3_attainable": "core",
    "Q1Paper.claim4_sandwich": "core",
    "Q1Paper.claim4_converse": "core",
    "Q1Paper.claim5_conditions_depend_on_W": "core",
    "Q1Paper.claim6_struct": "core",
    "Q1Paper.claim7_DEC_succ": "core",
    "Q1Paper.claim8_rank_consistency": "core",
    "Q1Paper.PaperI.Claim8_ElemSymm.claim8_disjunction": "bridge",
    "Q1Paper.exists_bezout_family_real": "core",
    "Q1Paper.rowSpace_windowMatrix_eq_windowSet": "bridge",
    "Q1Paper.PaperI.claim11_iff_gram": "core",
    "Q1Paper.PaperI.claim12_iff_gram": "core",
    "Q1Paper.PaperI.imagePair_surjective": "bridge",
    "Q1Paper.PaperI.rowSpace_windowInj_eq_windowSub": "bridge",
    "Q1Paper.PaperI.claim11_iff_gram_subset": "core",
    "Q1Paper.PaperI.claim12_iff_gram_subset": "core",
    "Q1Paper.PaperI.exists_rational_bases_bounded": "bridge",
    "Q1Paper.PaperI.Chart14.exists_chart_bases": "core",
    "Q1Paper.MinorCoeff.pencilMinor_coeff_bitLen_le": "core",
    "Q1Paper.PaperI.compressedGram_entry_bitLen_le": "core",
    "Q1Paper.prop4_r0_iff_spectral": "core",
    "Q1Paper.theorem1_conditional_params_fixedDeg": "core",
    "Q1Paper.theorem2_fpt_conditional": "core",
    "Q1Paper.claim16_i_iff_iii": "core",
    "Q1Paper.claim16_iii_implies_iv_of_gcd_isConst": "core",
    "Q1Paper.Thm5.DECℂ_iff_exists_encodes_auto": "core",
    "Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_quadratic": "core",
    "Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_n21_L2": "core",
    "Q1Paper.PaperI.ChartComplex.complex_spectral_implies_real": "bridge",
    "Q1Paper.PaperI.DecComplex.complexDEC": "core",
    "Q1Paper.PaperI.DecComplex.dec_of_complexDEC": "bridge",
    "Q1Paper.PaperI.Soundness.dec_of_phiPoint": "core",
    "Q1Paper.PaperI.ComplexSoundness.decComplex_of_phiPoint": "core",
    "Q1Paper.PaperI.ComplexCompression.compressed_of_spectralComplexRaw": "bridge",
    "Q1Paper.PaperI.ComplexCompleteness.phiPoint_of_complexDEC": "core",
    "Q1Paper.PaperI.ChartComplete.phiPoint_of_conditions": "bridge",
    "Q1Paper.PaperI.KernelLift.range_mulVecLin_eq_ker_map_complex": "bridge",
    "Q1Paper.PaperI.ReindexAlgebraic.rawAlgebraic_submatrix": "bridge",
    "Q1Paper.PaperI.ReindexSpectral.rawSpectral_submatrix": "bridge",
    "Q1Paper.PaperI.FromRowsMap.fromRows_map": "tool",
}

#: The declaration(s) that *are* the section's result, i.e. what the paper states as its claim there.
RESULTS: dict[str, list[str]] = {
    "S01_Compression.lean": ["Q1Paper.PaperI.DEC_iff_compressed"],
    "S02_Attainable.lean": ["Q1Paper.claim3_attainable", "Q1Paper.claim4_sandwich",
                            "Q1Paper.claim4_converse"],
    "S03_Subspace.lean": ["Q1Paper.claim5_conditions_depend_on_W", "Q1Paper.claim6_struct",
                          "Q1Paper.claim7_DEC_succ", "Q1Paper.claim8_rank_consistency"],
    "S04_Certificate.lean": ["Q1Paper.PaperI.claim11_iff_gram", "Q1Paper.PaperI.claim12_iff_gram"],
    "S05_FixedOrder.lean": ["Q1Paper.prop4_r0_iff_spectral",
                            "Q1Paper.theorem1_conditional_params_fixedDeg"],
    "S06_FixedParameter.lean": ["Q1Paper.theorem2_fpt_conditional"],
    "S07_ZeroFreeRow.lean": ["Q1Paper.claim16_i_iff_iii",
                             "Q1Paper.claim16_iii_implies_iv_of_gcd_isConst"],
    "S08_ExistsReal.lean": ["Q1Paper.Thm5.DECℂ_iff_exists_encodes_auto"],
    "S09_BitCost.lean": ["Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_quadratic",
                         "Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_n21_L2"],
    "S10_ChartEquivalence.lean": ["Q1Paper.PaperI.ComplexSoundness.decComplex_of_phiPoint",
                                   "Q1Paper.PaperI.ComplexCompleteness.phiPoint_of_complexDEC"],
}


def render(file_name: str, title: str, anchor: str, problem: str, prior: str,
           steps, nxt: str) -> str:
    lines = [
        "import Q1Paper.PaperI.S00_Interface.MainTheorems",
        "",
        "/-!",
        f"# {title}",
        "",
        f"Paper I, label `{anchor}`.  This file contains **no proofs**: it is a reading entry that lists the",
        "section's steps in proof order, each with the declaration that carries it.  Every step is a",
        "`#check`, so if a declaration is renamed this file stops compiling — that is what keeps it honest.",
        "",
        "## The problem",
        "",
        problem,
        "",
        "## What it consumes",
        "",
        prior,
        "",
        "## The result",
        "",
    ]
    for decl in RESULTS.get(file_name, []):
        lines.append(f"- `{decl}`")
    lines += [
        "",
        "Everything else below is scaffolding for those: **tool** = general linear algebra that does not",
        "mention this problem; **bridge** = a translation between two formulations of the same fact;",
        "**core** = mathematical content specific to this paper.",
        "",
        "## Steps, in proof order",
        "",
    ]
    for i, item in enumerate(steps, start=1):
        note, decl = item[0], item[1]
        role = ROLES.get(decl)
        tag = f"**[{role}]** " if role else ""
        lines.append(f"{i}. {tag}{note} — `{decl}`")
    lines += [
        "",
        "## What the next section does with it",
        "",
        nxt,
        "-/",
        "",
        "-- Each step below is the machine-checked part of the list above.",
    ]
    for item in steps:
        lines.append(f"#check {item[1]}")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()

    OUT.mkdir(parents=True, exist_ok=True)
    stale: list[str] = []
    for spec in SECTIONS:
        path = OUT / spec[0]
        text = render(*spec)
        current = path.read_text(encoding="utf-8") if path.exists() else None
        if current != text:
            stale.append(spec[0])
            if not args.check:
                path.write_text(text, encoding="utf-8", newline="\n")

    all_path = OUT / "All.lean"
    all_text = "\n".join([f"import Q1Paper.PaperI.Read.{s[0].removesuffix('.lean')}" for s in SECTIONS]) + "\n"
    if (all_path.read_text(encoding="utf-8") if all_path.exists() else None) != all_text:
        stale.append("All.lean")
        if not args.check:
            all_path.write_text(all_text, encoding="utf-8", newline="\n")

    if args.check:
        if stale:
            print("reading entries stale: " + ", ".join(stale))
            return 1
        print(f"reading entries up to date ({len(SECTIONS)} sections)")
        return 0
    print(f"wrote {len(SECTIONS)} reading entries" + (f" (changed: {', '.join(stale)})" if stale else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
