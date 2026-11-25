"""generate_paperI_claims.py -- one table, three artefacts.

The paper-to-Lean map is defined ONCE below (PAPER_ITEMS).  From it this script generates

  Q1Paper/PaperI/Claims.lean       documentation module, in the paper's order
  Q1Paper/PaperI/ClaimsCheck.lean  one `#check @name` per item: a renamed declaration breaks
                                   the build instead of silently rotting the map
  Q1Paper/PaperI/CLAIMS.md         the same table for readers who do not know Lean

Run from the repository root:

    python scripts/generate_paperI_claims.py          # regenerate
    python scripts/generate_paperI_claims.py --check  # fail if the files are stale (CI)

The --check mode is what keeps the three artefacts honest: it writes nothing and compares.
"""

from __future__ import annotations

import io
import os
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO, "Q1Paper", "PaperI")

# (paper label, short title, statement in words, Lean name, status)
#   status: "Lean"             proved with no hypothesis beyond the paper's
#           "Lean-conditional" proved relative to an explicitly declared external backend
#           "Paper"            paper-level algorithmic/complexity clause, not formalised
PAPER_ITEMS = [
    ("lem:rankid", "Claim 1", "rank[P; M] = rank P + rank(M N_P)",
     "Q1Paper.rank_vstack_add_rank_mul", "Lean"),
    ("lem:compression", "Claim 2",
     "the pencil criterion is equivalent to the compressed criterion (real design, complex ranks)",
     "Q1Paper.PaperI.DEC_iff_compressed", "Lean"),
    ("lem:attainable", "Claim 3", "the attainable row pairs have dimension d_0 and kappa_obs = r d_0",
     "Q1Paper.claim3_attainable", "Lean"),
    ("lem:sandwich", "Claim 4 (forward)", "W_0 <= W <= T and dim W <= dim W_0 + r",
     "Q1Paper.claim4_sandwich", "Lean"),
    ("lem:sandwich", "Claim 4 (converse)",
     "every subspace of the sandwich with dim W <= dim W_0 + r is realised by some R",
     "Q1Paper.claim4_converse", "Lean"),
    ("lem:W-conditions", "Claim 5", "(5a) and (5b) depend only on W (via pi_1, pi_2, pi_lambda)",
     "Q1Paper.claim5_conditions_depend_on_W", "Lean"),
    ("lem:struct", "Claim 6", "omega + 1 <= dim W <= 2 omega",
     "Q1Paper.claim6_struct", "Lean"),
    ("lem:monotone", "Claim 7", "DEC(q) implies DEC(q+1)",
     "Q1Paper.claim7_DEC_succ", "Lean"),
    ("lem:rankcons", "Claim 8 (rank form)", "the rank-consistency criterion via the Gram matrices",
     "Q1Paper.claim8_rank_consistency", "Lean"),
    ("lem:rankcons", "Claim 8 (disjunction)",
     "(exists b, M b = c) iff exists t, e_t(Gamma) > 0, e_{t+1}(Gamma) = 0, e_{t+1}(Gamma') = 0",
     "Q1Paper.PaperI.Claim8Literal.claim8_disjunction", "Lean"),
    ("lem:bezout", "Claim 9", "the degree-bounded Bezout family over R (deg < omega)",
     "Q1Paper.exists_bezout_family_real", "Lean"),
    ("lem:window", "Claim 10", "the window matrix's row space is the window set",
     "Q1Paper.rowSpace_windowMatrix_eq_windowSet", "Lean"),
    ("prop:gram", "Claim 11", "(5b) iff e_0 in row Z iff exists x, Z^T Z x = e_0",
     "Q1Paper.PaperI.claim11_iff_gram", "Lean"),
    ("clm:gramQ", "Claim 12", "the full-column-rank pencil certificate in Gram form",
     "Q1Paper.PaperI.claim12_iff_gram", "Lean"),
    ("lem:rationalbasis", "Claim 13",
     "rational bases of ker M and row M and an annihilator D, with the paper's constant tau_M",
     "Q1Paper.PaperI.exists_rational_bases_bounded", "Lean"),
    ("clm:chartdata", "Claim 14",
     "the chart data: bases of N, T, S, W_0 with the tau_M bounds",
     "Q1Paper.PaperI.Chart14.exists_chart_bases", "Lean"),
    ("lem:coeff", "Claim 15 (coefficients)",
     "every coefficient of every maximal minor of lambda X - G has bit length "
     "<= omega*b + bitLen(C(omega,d)) + bitLen(omega!)",
     "Q1Paper.MinorCoeff.pencilMinor_coeff_bitLen_le", "Lean"),
    ("lem:coeff", "Claim 15 (Gram entries)",
     "the Z^T Z entries through the compressed Gram, with the sharp b + omega.size bound",
     "Q1Paper.PaperI.compressedGram_entry_bitLen_le", "Lean"),
    ("lem:zero", "Claim 16 (i)-(iii)", "(i) iff (ii) iff (iii): spectral, no common root, constant gcd",
     "Q1Paper.claim16_i_iff_iii", "Lean"),
    ("lem:zero", "Claim 16 (iii)=>(iv)",
     "a left inverse of degree <= 2 omega - 2 exists over Q (rational descent)",
     "Q1Paper.claim16_iii_implies_iv_of_gcd_isConst", "Lean"),
    ("app:zero", "Claim 19", "the r = 0 system: exact integer division gives the quadratic cost",
     "Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_quadratic", "Lean"),
    ("app:r0", "Claim 21", "the paper's O(n^21 L^2) bit-cost bound",
     "Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_n21_L2", "Lean"),
    ("prop:zero", "Proposition 4", "for r = 0 the two conditions reduce to the system (R0)",
     "Q1Paper.prop4_r0_iff_spectral", "Lean"),
    ("thm:fixedq", "Theorem 1",
     "conditional on the declared real-algebraic backend: C (L+1)^(d (q+1)^2)",
     "Q1Paper.theorem1_conditional_params_fixedDeg", "Lean-conditional"),
    ("thm:fpt", "Theorem 2",
     "the FPT bound C (ell+2)^(C (ell+1)^2) (beta+1)^d, same backend",
     "Q1Paper.theorem2_fpt_conditional", "Lean-conditional"),
    ("thm:existsr", "Theorem 5",
     "DEC_C is equivalent to the existence of an encoding witness, with no abstract hypothesis",
     "Q1Paper.Thm5.DECℂ_iff_exists_encodes_auto", "Lean"),
]

HEADER = """\
/-
Q1Paper/PaperI/Claims.lean

The paper interface of the formalisation: the paper's items in the paper's order, each with the
Lean declaration that proves it.  This file contains no mathematics and no declarations -- it is
generated by `scripts/generate_paperI_claims.py` from a single table, and `ClaimsCheck.lean`
verifies that every name below still resolves, so the map cannot rot silently.

Roles are separated on purpose:

* `MainTheorems.lean`  -- what Lean must load (the implementation);
* `Claims.lean` (this) -- what the paper claims and where it is proved;
* `ClaimsCheck.lean`   -- the `#check` that keeps this file honest;
* `Audit.lean`         -- what those theorems depend on (axiom audit);
* `CLAIMS.md`          -- the same table for readers who do not know Lean.

Status labels: `[Lean]` proved with no hypothesis beyond the paper's; `[Lean-conditional]`
proved relative to an explicitly declared external backend; `[Paper]` the algorithmic /
complexity clause that is deliberately not formalised.
-/
"""


def lean_doc() -> str:
    lines = [HEADER]
    for label, title, statement, name, status in PAPER_ITEMS:
        lines.append(f"\n/-- **{title}** (`{label}`). `[{status}]`\n\n{statement}.\n\n"
                     f"Proved by `{name}`. -/")
    lines.append("\n-- (no declarations: see ClaimsCheck.lean for the machine-checked index)\n")
    return "".join(lines)


def check_lean() -> str:
    lines = [
        "/-",
        "Q1Paper/PaperI/ClaimsCheck.lean",
        "",
        "Machine-checked index: one `#check` per paper item, generated by",
        "`scripts/generate_paperI_claims.py`.  A renamed or deleted declaration makes this file",
        "fail to elaborate, which is what keeps `Claims.lean` and `CLAIMS.md` from rotting.",
        "-/",
        "import Q1Paper.PaperI.MainTheorems",
        "",
    ]
    for label, title, statement, name, status in PAPER_ITEMS:
        lines.append(f"-- {title} ({label}) [{status}]")
        lines.append(f"#check @{name}")
        lines.append("")
    return "\n".join(lines)


def markdown() -> str:
    rows = [
        "| paper | Lean declaration | status |",
        "|---|---|---|",
    ]
    for label, title, statement, name, status in PAPER_ITEMS:
        rows.append(f"| **{title}** (`{label}`) — {statement} | `{name}` | `[{status}]` |")
    return ("# Paper I: claim ↔ Lean index\n\n"
            "Generated by `scripts/generate_paperI_claims.py`; do not edit by hand.\n"
            "`Q1Paper/PaperI/ClaimsCheck.lean` machine-checks that every name below resolves.\n\n"
            + "\n".join(rows) + "\n\n"
            "`[Lean]` = no hypothesis beyond the paper's; `[Lean-conditional]` = relative to the\n"
            "explicitly declared real-algebraic backend (spec structures are proved inhabited);\n"
            "`[Paper]` = algorithmic/complexity clause deliberately not formalised.\n")


def main(argv):
    check = "--check" in argv
    targets = {
        os.path.join(OUT, "Claims.lean"): lean_doc(),
        os.path.join(OUT, "ClaimsCheck.lean"): check_lean(),
        os.path.join(OUT, "CLAIMS.md"): markdown(),
    }
    stale = []
    for path, content in targets.items():
        if check:
            current = io.open(path, encoding="utf-8").read() if os.path.exists(path) else ""
            if current != content:
                stale.append(os.path.relpath(path, REPO))
        else:
            io.open(path, "w", encoding="utf-8", newline="\n").write(content)
            print("wrote", os.path.relpath(path, REPO))
    if check:
        if stale:
            print("stale (regenerate with scripts/generate_paperI_claims.py):", file=sys.stderr)
            for s in stale:
                print("  " + s, file=sys.stderr)
            return 1
        print(f"claims artefacts up to date ({len(PAPER_ITEMS)} items)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
