"""generate_paperII_claims.py -- the Paper II claim table, in one place.

The paper-to-Lean map is defined ONCE below (`PAPER_ITEMS`).  From it this script generates

  Q1Paper/PaperII/CLAIMS.md      the table for readers who do not know Lean

and, with `--check`, also verifies two things:

  * the file on disk is what the table renders (so the table cannot drift), and
  * every declaration named in the table appears in `ClaimsCheck.lean` (so a rename that slipped
    through the table still breaks the build).

`Claims.lean` (the narrative) and `ClaimsCheck.lean` (the `#check`s) are hand-written: the prose
carries the argument and the checks carry the names, and this table ties them together.

    python scripts/generate_paperII_claims.py           # regenerate
    python scripts/generate_paperII_claims.py --check   # fail if stale (CI)
"""

from __future__ import annotations

import io
import os
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DIR = os.path.join(REPO, "Q1Paper", "PaperII")
OUT = os.path.join(DIR, "CLAIMS.md")
CHECK = os.path.join(DIR, "ClaimsCheck.lean")

# (paper label, paper item, statement in words, declarations, grade)
#   grade: "literal"        the Lean statement is the statement of the paper
#          "abstract core"  linear-map / submodule version, translation paper-level
#          "ingredient"     one step of the proof, not the statement
PAPER_ITEMS = [
    ("claim:sandwich", "Claim 4 (forward)",
     "a design of r rows gives W0 <= W <= T with t <= r",
     ["Q1Paper.claim4_sandwich", "Q1Paper.PaperII.decC_to_feasible"], "literal"),
    ("claim:sandwich", "Claim 4 (converse, complex designs)",
     "every feasible W of the sandwich at t = dim(W/W0) is realised by a design",
     ["Q1Paper.PaperII.feasible_to_DEC"], "literal"),
    ("claim:sandwich", "Claim 4 (converse, real designs)",
     "the same for DEC_c: real_compress followed by the compressed criterion",
     ["Q1Paper.PaperII.real_compress", "Q1Paper.PaperII.feasible_to_decC"], "literal"),
    ("claim:rows", "Claim 3 (attainable row pairs, reused)",
     "the attainable row pairs have dimension d_0",
     ["Q1Paper.claim3_attainable"], "abstract core"),
    ("claim:struct", "Claim 6 (structural bound, reused)",
     "omega + 1 <= dim W <= 2 omega",
     ["Q1Paper.claim6_struct"], "literal"),
    ("claim:compress", "Claim 2 (pencil form, reused)",
     "the pencil criterion is equivalent to the compressed criterion",
     ["Q1Paper.PaperI.DEC_iff_compressed"], "literal"),
    ("lem:monotone", "Claim 5 (monotonicity, real designs)",
     "DEC_c(r) implies DEC_c(r') for r <= r'",
     ["Q1Paper.PaperII.decC_mono"], "literal"),
    ("lem:monotone", "Claim 5 (saturation, complex designs)",
     "DEC(r) implies DEC(m) with m = dim(T/W0)",
     ["Q1Paper.PaperII.dec_saturates"], "literal"),
    ("lem:monotone", "Claim 5 (saturation, real designs)",
     "DEC_c(r) implies DEC_c(m) with m = dim(T/W0)",
     ["Q1Paper.PaperII.decC_saturates"], "literal"),
    ("prop:minorder", "Proposition 1 (complex designs)",
     "q_min = r0 + t_min, i.e. t_min <= r iff DEC(r0 + r)",
     ["Q1Paper.PaperII.tMin_le_iff_dec"], "literal"),
    ("prop:minorder", "Proposition 1 (real designs)",
     "t_min^R <= r iff DEC_c(r), with t_min^R the least quotient dimension over real designs",
     ["Q1Paper.PaperII.tMinC_le_iff_decC"], "literal"),
    ("prop:minorder", "Proposition 1 (least order is attained)",
     "the least feasible order is itself feasible",
     ["Q1Paper.PaperII.dec_sInf_tMinSet", "Q1Paper.PaperII.decC_sInf_tMinCSet"], "literal"),
    ("prop:minorder", "Proposition 1 (a priori bound)",
     "t_min <= 2 ell, and t_min^R <= 2 ell for real designs",
     ["Q1Paper.PaperII.tMin_le_two_ell", "Q1Paper.PaperII.tMinC_le_two_ell"], "literal"),
    ("prop:lowerbound", "Proposition 2 (spectral lower bound)",
     "rank[U0;V0] <= omega <= s0 + t - 1",
     ["Q1Paper.PaperII.lowerBound_core", "Q1Paper.PaperII.lowerBound_sub"], "literal"),
    ("eq:qmin-lb", "the consequence qmin-lb",
     "a + 1 - s0 <= t_min (no side condition), and the same for t_min^R",
     ["Q1Paper.PaperII.le_tMin_of_lowerBound_max", "Q1Paper.PaperII.le_tMinC_of_lowerBound"],
     "literal"),
    ("prop:tight", "Proposition 3 (the numerical half)",
     "dim W = dim pi_1 W + 1 forces t = a - s0 + 1",
     ["Q1Paper.PaperII.t_eq_of_finrank"], "literal"),
    ("prop:tight", "Proposition 3 (the (G,b) direction)",
     "pi_lambda W(G,b) = (lambda I - G)U + span{b}; the rank condition makes it feasible; t = a - s0 + 1",
     ["Q1Paper.PaperII.graphExt_piLam", "Q1Paper.PaperII.graphExt_feasible",
      "Q1Paper.PaperII.t_eq_of_graph"], "literal"),
    ("prop:tight", "Proposition 3 (the converse)",
     "a feasible W with dim W = dim pi_1 W + 1 is W(G,b)",
     ["Q1Paper.PaperII.exists_graph_representation"], "literal"),
    ("prop:tight", "Proposition 3 (pi_1 W = U0 + V0 at an attaining W)",
     "the identification that closes the composition",
     ["Q1Paper.PaperII.pi1_eq_sup_of_finrank"], "literal"),
    ("prop:tight", "Proposition 3 (composition, from the data)",
     "a (G,b) pair with the sandwich and rank condition forces t_min = a + 1 - s0",
     ["Q1Paper.PaperII.tMin_eq_of_graph"], "literal"),
    ("prop:tight", "Proposition 3 (composition, from saturation)",
     "a saturating t_min produces the data",
     ["Q1Paper.PaperII.exists_graph_of_tMin_eq"], "literal"),
    ("prop:tight", "Proposition 3 (packaged, complex designs)",
     "t_min = a + 1 - s0 iff the tightness data exist on U0 + V0",
     ["Q1Paper.PaperII.tMin_eq_iff_graph"], "literal"),
    ("prop:tight", "Proposition 3 (packaged, real designs)",
     "t_min^R = a + 1 - s0 iff a real design realises a real graph W(G,b) in the sandwich whose "
     "complexification is feasible",
     ["Q1Paper.PaperII.tMinC_eq_iff_real_graph"], "literal"),
    ("prop:tight", "Proposition 3 (real designs, the two halves)",
     "the (G,b) direction with purely real hypotheses, and the extraction of real data from a "
     "saturating order",
     ["Q1Paper.PaperII.tMinC_le_of_graph_real_pure", "Q1Paper.PaperII.tMinC_eq_of_real_graph",
      "Q1Paper.PaperII.exists_real_graph_of_tMinC_eq"], "literal"),
    ("prop:tight", "Proposition 3 (the real <-> complex bridges)",
     "the complexification of a design's W and of W0, T, the real points of a complex span, the "
     "descent of feasibility, and the real sandwich converse",
     ["Q1Paper.PaperII.WR_eq_span_phiPair_WRreal", "Q1Paper.PaperII.W0_eq_span_phiPair_W0real",
      "Q1Paper.PaperII.TR_eq_span_phiPair_TRreal", "Q1Paper.PaperII.graphExt_span_phiPair",
      "Q1Paper.PaperII.mem_of_phiPair_mem_span",
      "Q1Paper.PaperII.isFeasible_real_of_span_phiPair",
      "Q1Paper.PaperII.exists_design_of_pairRowSpace"], "literal"),
    ("thm:interface", "Theorem 4 (ordering half)",
     "the decision problem is monotone, so the order is a threshold of t_min",
     ["Q1Paper.PaperII.exists_least_of_monotone"], "literal"),
    ("thm:interface", "Theorem 4 (the arithmetic of the call count)",
     "log2 N + 1 halvings empty an interval of N candidates, so bisection over min(r, 2 ell) "
     "candidates makes O(log(ell+2)) calls",
     ["Q1Paper.PaperII.lt_two_pow_log2_succ", "Q1Paper.PaperII.div_two_pow_log2_succ_eq_zero",
      "Q1Paper.PaperII.bisect_steps_le", "Q1Paper.PaperII.log2_mono_le",
      "Q1Paper.PaperII.half_width", "Q1Paper.PaperII.bisectGo",
      "Q1Paper.PaperII.bisectGo_spec", "Q1Paper.PaperII.bisectGo_collapses",
      "Q1Paper.PaperII.bisectGo_invariant", "Q1Paper.PaperII.bisectGo_finds"], "literal"),
    ("cor:opt", "Corollary 5 (OPT), computationally",
     "bisection on the DEC predicate over [0, 2 ell] returns t_min: log2(2 ell) + 1 calls",
     ["Q1Paper.PaperII.tMin_eq_bisectGo"], "literal"),
    ("cor:opt", "Corollary 5 (OPT) for real designs",
     "bisection on the DecOrder predicate over [0, 2 ell] returns t_min^R",
     ["Q1Paper.PaperII.tMinC_eq_bisectGo"], "literal"),
]

NOT_FORMALISED = [
    ("thm:interface", "the search algorithm itself",
     "the arithmetic of the call count is formalised; the bisection procedure is paper-level"),
    ("cor:find", "the chart parametrisation in Psi_{t,omega} and the sampling step",
     "items (iii)-(v) of Psi (sandwich + pencil) are formalised as isFeasible_pairRowSpace_iff / "
     "claim5_conditions_depend_on_W; the chart parametrisation W = row[XB GB] and the "
     "sampling-point algorithm are citations to the companion paper"),
    ("app:example", "the appendix instance (q_min = 4)",
     "the full certificate is the Python layer (scripts/verify_paperII_example.py); "
     "PaperII/Appendix.lean re-checks in Lean that the pencil at lambda = 0 is singular "
     "(appendix_pencil_kernel)"),
]


def render() -> str:
    lines = [
        "# Paper II: claim -> Lean index (generated)",
        "",
        "Generated by `scripts/generate_paperII_claims.py`; do not edit by hand.",
        "`Q1Paper/PaperII/ClaimsCheck.lean` machine-checks that every name below resolves, and",
        "`scripts/generate_paperII_claims.py --check` fails if this table drifts from it.",
        "",
        "Grades: *literal* = the Lean statement is the statement of the paper; *abstract core* =",
        "the linear-map/submodule version; *ingredient* = one step of a proof.",
        "",
        "| paper item | statement | Lean declaration | grade |",
        "|---|---|---|---|",
    ]
    for label, item, statement, decls, grade in PAPER_ITEMS:
        names = ", ".join("`" + d + "`" for d in decls)
        lines.append(f"| **{item}** (`{label}`) | {statement} | {names} | {grade} |")
    lines += [
        "",
        "## Not formalised",
        "",
        "| paper item | what is missing |",
        "|---|---|",
    ]
    for label, item, why in NOT_FORMALISED:
        lines.append(f"| **{item}** (`{label}`) | {why} |")
    lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    rendered = render()
    if "--check" in sys.argv:
        ok = True
        if not os.path.exists(OUT):
            print("missing", OUT)
            ok = False
        elif io.open(OUT, encoding="utf-8").read() != rendered:
            print("stale:", OUT)
            ok = False
        check_text = io.open(CHECK, encoding="utf-8").read()
        for _, item, _, decls, _ in PAPER_ITEMS:
            for d in decls:
                if "#check @" + d not in check_text:
                    print(f"table names {d} ({item}) but ClaimsCheck.lean does not check it")
                    ok = False
        if ok:
            print("paper II claim table up to date, all names checked")
        return 0 if ok else 1
    io.open(OUT, "w", encoding="utf-8", newline="\n").write(rendered)
    print("wrote", OUT)
    return 0


if __name__ == "__main__":
    sys.exit(main())
