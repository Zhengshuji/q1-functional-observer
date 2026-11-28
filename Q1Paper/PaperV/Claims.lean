/-
Q1Paper/PaperV/Claims.lean

The paper interface of Paper V's formalisation: the paper's items in the paper's order, each with
the declarations that carry it, and a three-tier label.

This file is narration only — it declares nothing.  `ClaimsCheck.lean` machine-checks that every
name below resolves, so a rename breaks the build instead of silently invalidating this table.

The three tiers, used for every item below and mirrored in `docs/PAPER_V_GUIDE.md`:

* **complete** — the paper's statement of the item is formalised as stated (modulo the paper's
  standing hypotheses), 71 declarations in total, audited in `Audit.lean`;
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

/-! ## §III  The criterion (Theorem 4) — complete (matrix form)

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
* **Corollary 10, root step (Necessity.lean)**: over `ℂ` a polynomial of positive `natDegree`
  has a root (`Q1Paper.PaperV.exists_root_of_natDegree_pos`), so a positive-degree divisor with
  constant nonzero leading coefficient produces a common root at *every* specialisation —
  `Q1Paper.PaperV.exists_common_root_of_divisor`.  This is the step "positive generic degree ⇒
  the fibre point is bad".
* **Corollary 10, Gauss step (Gauss.lean)**: a monic `g` over `ℂ(t)[λ]` of positive degree that
  divides the image of a monic `F ∈ ℂ[t][λ]` lifts to a primitive `h ∈ ℂ[t][λ]` with
  `h.leadingCoeff = 1`, positive degree, dividing every member —
  `Q1Paper.PaperV.exists_primitive_divisor_of_monic_dvd`; consequently every specialisation has a
  common root — `Q1Paper.PaperV.exists_common_root_of_gcd` and its usable form
  `Q1Paper.PaperV.exists_common_root_of_gcd_family`.  This closes the Gauss step that had been
  paper-side in the first version of the formalisation.
* **Theorem 4, necessity in matrix form (CriterionNecessity.lean)**:
  `Q1Paper.PaperV.rank_lt_of_gcd_pos` bundles the root and Gauss steps with the matrix minors:
  a positive-degree monic common divisor of the `d`-minors over `ℂ(t)[λ]`, plus one minor with
  nonzero constant leading coefficient, forces `rank < d` at some `λ` for every specialisation.
* **Minors, evaluation, rank**: `Q1Paper.PaperV.eval_det_submatrix` (evaluating a minor is taking
  the minor of the evaluation), and both directions of "rank ≥ d ⟺ some d-minor is nonzero" —
  `Q1Paper.PaperV.exists_submatrix_det_ne_zero_of_le_rank`,
  `Q1Paper.PaperV.le_rank_of_det_submatrix_ne_zero`.
* **Sufficiency, assembled**: if the family of `d`-minors has unit gcd then every evaluation has
  rank at least `d` — `Q1Paper.PaperV.le_rank_map_of_isUnit_gcd_minor` (with `minor`).

*Paper only*: the "rank ≤ d' automatically" step that the paper's standing
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

* **Complete — Theorem 13's covering step**: a finite union of proper zero sets of polynomials is
  proper, so if finitely many closed conditions cover the parameter space one of them is everything —
  `Q1Paper.PaperV.eq_zero_of_forall_eval_eq_zero`,
  `Q1Paper.PaperV.exists_forall_eval_ne_zero`,
  `Q1Paper.PaperV.exists_eq_zero_of_forall_exists_eval_eq_zero`.

* **Complete — the spectral form's linear algebra**: at a non-eigenvalue of `Z''` the pencil
  `λ H - H Z''` keeps the rank of `H`, so no `d'`-minor can vanish there —
  `Q1Paper.PaperV.rank_mul_of_det_ne_zero`,
  `Q1Paper.PaperV.rank_smul_sub_mul_of_det_ne_zero`,
  `Q1Paper.PaperV.exists_minor_ne_zero_of_det_ne_zero`.

*Paper only*: Theorem 13 (fixed spectral factor — an incidence-variety dimension count),
Corollary 12 and Theorem 14 (closedness — proved stratum by stratum; the global statement is
false, Example 27 in §VI(E)),
Theorem 15 (infeasibility, a logical consequence of the closedness statement).
-/

/-! ## §V  Algorithms

* **Partial — the probabilistic counting core of Theorem 8 / Theorem 19** (`Probability.lean`):
  Schwartz–Zippel for a constant grid in `ℂ` (`schwartz_zippel_zero_count`, a wrapper around
  Mathlib's `MvPolynomial.schwartz_zippel_totalDegree`), the two-grid union bound for finite
  grids (`card_badPairs_le`, `two_grid_bad_bound`, `two_grid_bad_bound_univ`,
  `two_grid_good_bound`), and the composition with Schwartz–Zippel
  (`two_grid_failure_bound_of_schwartz_zippel`).  Not formalised: the resultant `D_c`, its
  bidegree bounds `deg_c D_c ≤ d'` and `deg_t D_c ≤ 2d'²`, the height bound, and the
  one-sidedness step (bad fibre ⇒ `D_c ≡ 0`).

* **Complete — Theorem 22, enumerative skeleton** (`Enumeration.lean`): if a finite list is
  complete for a predicate, the unbounded existential is the existential over the list, hence
  decidable — `Q1Paper.PaperV.exists_iff_exists_mem_finset`,
  `Q1Paper.PaperV.decidable_exists_of_complete_finset`.  The construction of the list itself
  (the invariant subspaces) stays paper-side, as stated in the paper.

* **Complete — Theorem 22, structure step**: `T ≤ U` turns compatibility into invariance —
  `Q1Paper.PaperV.map_mem_of_le_sup`, `Q1Paper.PaperV.invariant_iff_compat_of_le`, together with the
  dimension step `Q1Paper.PaperV.le_of_finrank_eq_one` used to get `T ≤ U` when `t = 1`.

* **Complete — Theorem 8's counting step**: a nonzero polynomial has at most `deg` roots in any
  finite grid, so a grid larger than the degree cannot consist entirely of bad points —
  `Q1Paper.PaperV.card_roots_le_natDegree`, `Q1Paper.PaperV.exists_ne_root_of_card`.

*Paper only*: Theorem 7 (rational witness and its height), Theorem 8 (the two-grid probability
bound and the resultant degree estimate), Theorem 19 (the regime: one-sided acceptance inside the
generic stratum, no outer probability bound), and the *construction* of the finite list in
Theorem 22 (its logical skeleton is Lean, its enumeration of invariant subspaces is paper). The
examples of §V are decided by exact rational arithmetic in `verification/`, not in Lean.
-/
