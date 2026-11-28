# Paper V 鈥?the free-row fibre: reading guide

Paper V is `paper/paper_V_fibre.tex` (PDF alongside).  This guide says what the paper
proves, which part of it is machine-checked, and where every claim can be verified.

## What the paper is about

Fix the compressed row space `U` of a functional-observer candidate and let the free rows
vary.  The admissible values of `H_A` form the **fibre**, and the paper asks when every
point of the fibre fails the spectral condition `(5b)`.

The paper proves three things about that question:

1. **The fibre is an affine space** (Theorem 2): it is empty or a coset of `T 鈯?U`, of
   dimension `q路a` with `a = dim(U 鈭?T)`, and it is nonempty exactly when
   `U Z'' 鈯?U + T`.
2. **On the fibre the spectral condition is a degree condition** (Theorem 4): some point
   of the fibre satisfies `(5b)` exactly when the gcd of the `d'`-minors of
   `位 H - H Z'' - G'`, taken over the fibre's function field, has degree zero.  The only
   non-trivial step is that a positive-degree divisor with constant `位`-leading
   coefficient survives every specialisation (Lemma 5).
3. **Failure of the whole fibre is a fixed spectral factor** when `q > d'`
   (Theorem 13): the common divisor does not depend on the fibre parameters.  Hence the
   bad set is closed on each stratum of constant a (Corollary 12; closedness on the whole
Grassmannian is open, see VI(E)), the feasible set is relatively open there, and infeasibility
   is exactly the containment of the compatibility stratum in the bad set (Theorem 15).

Section V turns this into procedures: a one-sided randomised decision procedure on the
region where compatibility is automatic (Theorem 19), and an enumeration for `t = 1`
(Theorem 22).  Section VI lists what is open 鈥?in particular the thin stratum where
compatibility is a genuine constraint.

## What is machine-checked

| Paper item | Lean declaration | File |
|---|---|---|
| Theorem 2 (fibre as a coset; nonemptiness) | `Q1Paper.PaperV.fibre`, `mem_fibre`, `fibre_nonempty_iff`, `fibre_eq_coset`, `fibre_prod_nonempty_iff` | `Q1Paper/PaperV/Fibre.lean` (the assembled `q`-fold product and its dimension `q路a` are paper) |
| Theorem 4's leading-coefficient step | `coeff_det_smul_sub_X`, `coeff_det_smul_sub_X_ne_zero` | `Q1Paper/PaperV/LeadingCoeff.lean` |
| Lemma 5 (specialisation) | `natDegree_map_eval_of_leadingCoeff_const`, `map_dvd_of_dvd` | `Q1Paper/PaperV/Specialize.lean` |
| Corollary 10 (shape) | `specialized_common_factor` | `Q1Paper/PaperV/Specialize.lean` |

The axiom audit is `Q1Paper/PaperV/Audit.lean` (40 declarations, all on
`propext`, `Classical.choice`, `Quot.sound`); `scripts/check.sh` runs it.  The claims
table is `Q1Paper/PaperV/Claims.lean` and its machine check is
`Q1Paper/PaperV/ClaimsCheck.lean` (the same forty declarations).

## What is *not* machine-checked, and why

* **Theorem 4's gcd criterion** 鈥?a statement about gcds of matrix minors over `K(t)[位]`;
  the formalisation needs multivariate polynomial gcds and matrix minors at once.  The
  paper proof is complete and its only hard step (Lemma 5) *is* checked.
* **Theorem 13 (fixed spectral factor)** 鈥?an incidence-variety dimension count.
* **Corollary 12 / Theorem 14 (closedness of the bad set)** 鈥?quantifier elimination over the
  coefficient space of the coefficient test.
* **Theorems 15 and 16** 鈥?a probabilistic argument (Schwartz鈥揨ippel) and an enumeration.

`Q1Paper/PaperV/MainTheorems.lean` records this split; `Q1Paper/PaperV/Claims.lean` says it
item by item.  Nothing is silently omitted.

## What is certified exactly

`verification/fibre.py` decides the three examples of 搂V in exact rational arithmetic:
the feasible fibre (gcd 1), the bad point (gcd `位 + 3`, parameter independent), and the
thin-region instance.  It asserts the ranks and the nonemptiness of the fibre *before*
deciding, so a wrong model fails loudly.  `verification/ci/c773_paperV_fibre.py` runs it in
CI.

## How to read the paper alongside the artifact

1. 搂II (the fibre) 鈥?read with `Fibre.lean` open; every step of Theorem 2m 1 is a named
   declaration.
2. Section III (the criterion): Lemma 5 is `Specialize.lean`; the rest of the criterion is the
   paper's argument.
3. 搂IV (the bad set) 鈥?the paper's Theorem 13 is the structural heart; the coefficient test
   behind Corollary 12 is `verification/fibre.py`'s `inner_deg`.
4. 搂V (examples) 鈥?run `python verification/fibre.py`.


## Coverage at a glance (40 kernel-checked declarations)

| Paper item | Lean declarations | Module |
|---|---|---|
| Thm 1 (fibre): per-row coset, nonemptiness | `fibre`, `mem_fibre`, `fibre_nonempty_iff`, `fibre_eq_coset`, `fibre_prod_nonempty_iff` | `Fibre.lean` |
| Thm 1 (product dimension `q·a`) | `piConstEquiv`, `mem_pi_const`, `finrank_pi_const`, `finrank_iInf_comap_proj` | `FibreDim.lean` |
| Lemma 5 (specialisation), Cone 10 | `natDegree_map_eval_of_leadingCoeff_const`, `map_dvd_of_dvd`, `specialized_common_factor` | `Specialize.lean` |
| Thm 4's leading-coefficient step | `coeff_one_C_mul_X_sub_C`, `natDegree_C_mul_X_sub_C_le`, `coeff_det_smul_sub_X`, `coeff_det_smul_sub_X_ne_zero` | `LeadingCoeff.lean` |
| Thm 4's algebraic core (gcd ↔ no common root) | `gcd_ne_zero`, `exists_root_of_not_isUnit`, `isCoprime_iff_no_common_root`, `gcd_eq_one_iff_no_common_root`, `exists_common_root_of_not_isUnit` | `GcdRoot.lean` |
| Thm 4, finite-family form | `isUnit_gcd_iff_no_common_root` | `FamilyGcd.lean` |
| Thm 4, sufficiency assembled | `le_rank_map_of_isUnit_gcd_minor`, `minor` | `Criterion.lean` |
| minors and pointwise evaluation | `eval_det_submatrix` | `MinorEval.lean` |
| rank vs nonzero minor (both directions) | `exists_submatrix_det_ne_zero_of_le_rank`, `le_rank_of_det_submatrix_ne_zero` | `RankMinor.lean` |
| Bezout / unit ideal (gcd = 1 ⇒ ∑ Aᵢfᵢ = 1) | `exists_combination_eq_one_of_gcd_eq_one`, `ideal_span_eq_top_of_gcd_eq_one`, `exists_combination_eq_one` | `UnitIdeal.lean` |
| Prop 11 (coefficient test) | `evalRingHom_apply`, `eval_zero_iff_coeff_eval_zero`, `forall_eval_zero_iff_forall_coeff`, `exists_forall_eval_zero_iff_exists_forall_coeff` | `CoeffTest.lean` |
| Prop 16 (column drop) | `column_zero_of_mem`, `rank_le_card_compl_of_cols_zero`, `rank_lt_of_cols_zero` | `ColumnDrop.lean` |
| Prop 17 (column dependence) | `rank_lt_of_le_ker`, `matrix_rank_lt_of_le_ker` | `KerRank.lean` |
| Thm 22 structure step (`T ≤ U` ⟹ compat = invariance) | `map_mem_of_le_sup`, `invariant_iff_compat_of_le` | `Invariant.lean` |

Each row above is **complete** in the sense that the paper's statement of that item is formalised;
`Claims.lean` carries the same three-tier labels.

**Partial** (core formalised, full statement not): Theorem 4 — the sufficiency direction is
assembled (`Criterion.lean`), the necessity direction over `ℂ(t)[λ]` is not.

**Paper only, with the reason stated in `Claims.lean`:** Theorem 7 (rational witness and its
height), Theorem 8 (two-grid probability bound), Theorem 13 (incidence dimension), Corollary 12 /
Theorem 14 (closedness — proved stratum by stratum, global case open, §VI(E)), Theorem 15
(infeasibility), Theorem 19 (regime), and the enumeration half of Theorem 22.

## Status

The paper contains no claim that its proof does not support: every assertion is either proved in
the text, cited, machine-checked (the table above), or listed as an open problem. The single
unresolved structural item is §VI(E), closedness of the bad set on the whole Grassmannian; the
paper states the stratum-wise version instead.
