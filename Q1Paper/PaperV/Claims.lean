/-
Q1Paper/PaperV/Claims.lean

The paper interface of Paper V's formalisation: the paper's items in the paper's order, each with
the declarations that carry it, and a three-tier label.

This file is narration only — it declares nothing.  `ClaimsCheck.lean` machine-checks that every
name below resolves, so a rename breaks the build instead of silently invalidating this table.

The three tiers, used for every item below and mirrored in `docs/PAPER_V_GUIDE.md`:

* **complete** — the paper's statement of the item is formalised as stated (modulo the paper's
  standing hypotheses), 39 declarations in total, audited in `Audit.lean`;
* **partial** — the mathematical core of the item is formalised but the full statement is not
  (typically because assembling it needs multivariate gcds, Grassmannians, or probability);
* **paper only** — not formalised, with the reason.

Nothing is silently omitted; every "paper only" item says why.
-/

/-! ## §II  The fibre (Theorem 2) — complete

* **The per-row fibre** `{x ∈ T | x + y ∈ U}` — `Q1Paper.PaperV.fibre`, with its membership
  unfolding `Q1Paper.PaperV.mem_fibre`.
* **Nonemptiness** `T ∩ (U - y) ≠ ∅ ⟺ y ∈ U + T` — `Q1Paper.PaperV.fibre_nonempty_iff`.
* **Coset form**: any point of the fibre generates it as a coset of `T ⊓ U`, so the fibre is affine
  with direction `T ⊓ U` — `Q1Paper.PaperV.fibre_eq_coset`.
* **Product over the rows** — `Q1Paper.PaperV.fibre_prod_nonempty_iff`.
* **The dimension `q·a`**: a product of `q` copies of a subspace has finrank `q · finrank` —
  `Q1Paper.PaperV.mem_pi_const`, `Q1Paper.PaperV.finrank_pi_const`,
  `Q1Paper.PaperV.finrank_iInf_comap_proj`; and `t = 1` with a nonzero intersection forces
  `T ≤ U` — `Q1Paper.PaperV.le_of_finrank_eq_one`.
-/

/-! ## §III  The criterion (Theorem 4) — partial (engines complete, assembly partial)

* **Lemma 5 (specialisation)**: a nonzero constant λ-leading coefficient survives specialisation, so
  the λ-degree cannot drop — `Q1Paper.PaperV.natDegree_map_eval_of_leadingCoeff_const`; divisibility
  is preserved — `Q1Paper.PaperV.map_dvd_of_dvd`; Corollary 10 —
  `Q1Paper.PaperV.specialized_common_factor`.
* **Leading-coefficient step**: the λ^d coefficient of `det (λ•H − B)` is `det H`, for every `B` —
  `Q1Paper.PaperV.coeff_det_smul_sub_X`, nonzero form
  `Q1Paper.PaperV.coeff_det_smul_sub_X_ne_zero`.
* **Bezout / unit ideal**: a finite family with unit gcd admits a Bezout identity and generates the
  unit ideal — `Q1Paper.PaperV.exists_combination_eq_one_of_gcd_eq_one`,
  `Q1Paper.PaperV.ideal_span_eq_top_of_gcd_eq_one`,
  `Q1Paper.PaperV.exists_combination_eq_one`.
* **Algebraic core (binary)**: gcd and common roots — `Q1Paper.PaperV.gcd_ne_zero`,
  `Q1Paper.PaperV.exists_root_of_not_isUnit`,
  `Q1Paper.PaperV.isCoprime_iff_no_common_root`,
  `Q1Paper.PaperV.gcd_eq_one_iff_no_common_root`,
  `Q1Paper.PaperV.exists_common_root_of_not_isUnit`.
* **Algebraic core (finite family)**: `Q1Paper.PaperV.isUnit_gcd_iff_no_common_root`, and its
  pointwise consequence `Q1Paper.PaperV.exists_eval_ne_zero_of_isUnit_gcd`.
* **Minors, evaluation, rank**: `Q1Paper.PaperV.eval_det_submatrix` (evaluating a minor is taking
  the minor of the evaluation), and both directions of "rank ≥ d ⟺ some d-minor is nonzero" —
  `Q1Paper.PaperV.exists_submatrix_det_ne_zero_of_le_rank`,
  `Q1Paper.PaperV.le_rank_of_det_submatrix_ne_zero`.
* **Sufficiency, assembled**: if the family of `d`-minors has unit gcd then every evaluation has
  rank at least `d` — `Q1Paper.PaperV.le_rank_map_of_isUnit_gcd_minor` (with `minor`).

*Paper only*: the necessity direction over the function field `ℂ(t)[λ]` (which needs a
multivariate-gcd development), the "rank ≤ d' automatically" step that the paper's standing
hypothesis `rank H = d'` supplies, and the intrinsic form (Theorem 6).
-/

/-! ## §IV  The bad set

* **Complete — Proposition 11 (coefficient form)**: `Q1Paper.PaperV.evalRingHom_apply`,
  `Q1Paper.PaperV.eval_zero_iff_coeff_eval_zero`,
  `Q1Paper.PaperV.forall_eval_zero_iff_forall_coeff`,
  `Q1Paper.PaperV.exists_forall_eval_zero_iff_exists_forall_coeff`.

* **Complete — Proposition 16 (column drop)**: the vanishing column
  `Q1Paper.PaperV.column_zero_of_mem`, the rank bound
  `Q1Paper.PaperV.rank_le_card_compl_of_cols_zero`, and the conclusion
  `Q1Paper.PaperV.rank_lt_of_cols_zero`.

* **Complete — Proposition 17 (column dependence)**: `Q1Paper.PaperV.rank_lt_of_le_ker`,
  `Q1Paper.PaperV.matrix_rank_lt_of_le_ker`.

*Paper only*: Theorem 13 (fixed spectral factor — an incidence-variety dimension count),
Corollary 12 and Theorem 14 (closedness — proved stratum by stratum, global case open, §VI(E)),
Theorem 15 (infeasibility, a logical consequence of the closedness statement).
-/

/-! ## §V  Algorithms

* **Complete — Theorem 22, structure step**: `T ≤ U` turns compatibility into invariance —
  `Q1Paper.PaperV.map_mem_of_le_sup`, `Q1Paper.PaperV.invariant_iff_compat_of_le`, together with the
  dimension step `Q1Paper.PaperV.le_of_finrank_eq_one` used to get `T ≤ U` when `t = 1`.

*Paper only*: Theorem 7 (rational witness and its height), Theorem 8 (the two-grid probability
bound and the resultant degree estimate), Theorem 19 (the regime: one-sided acceptance inside the
generic stratum, no outer probability bound), and the enumeration half of Theorem 22. The examples
of §V are decided by exact rational arithmetic in `verification/`, not in Lean.
-/
