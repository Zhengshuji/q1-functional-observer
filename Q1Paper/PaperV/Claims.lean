/-
Q1Paper/PaperV/Claims.lean

The paper interface of Paper V's formalisation: the paper's items in the paper's
order, each with the declarations that carry it.

This file is narration only — it declares nothing.  `ClaimsCheck.lean` machine-checks
that every name below resolves, so a rename breaks the build instead of silently
invalidating this table.

Scope.  Three groups of items:

* **formalised** (eleven declarations, audited in `Audit.lean`);
* **partial**: the item's mathematical core is formalised, the rest is paper;
* **paper only**: not formalised, with the reason.

Nothing is silently omitted; every "paper only" item says why.
-/

/-! ## §II  The fibre (Theorem 1) — formalised

* **The per-row fibre** `{x ∈ T | x + y ∈ U}` — `Q1Paper.PaperV.fibre`, with its membership
  unfolding `Q1Paper.PaperV.mem_fibre`.
* **Nonemptiness** `T ∩ (U - y) ≠ ∅ ⟺ y ∈ U + T` — `Q1Paper.PaperV.fibre_nonempty_iff`.
* **Coset form**: any point of the fibre generates it as a coset of `T ⊓ U`, so the fibre is
  affine with direction `T ⊓ U` and dimension `finrank (T ⊓ U)` —
  `Q1Paper.PaperV.fibre_eq_coset`.
* **Product over the rows**: the fibre is nonempty exactly when every row's translate lies in
  `U + T` (the row-wise reading of `U Z'' ⊆ U + T`) —
  `Q1Paper.PaperV.fibre_prod_nonempty_iff`.

*Not formalised*: the assembled matrix-level statement that the whole fibre, as a product over
`q` rows, has dimension `q·a`.  It follows from the per-row coset description, but the product
construction is not written out in Lean.
-/

/-! ## §III  The criterion (Theorem 4) — engines formalised, main equivalence paper

* **Lemma 2, degree**: a nonzero constant λ-leading coefficient survives specialisation, so the
  λ-degree cannot drop — `Q1Paper.PaperV.natDegree_map_eval_of_leadingCoeff_const`.
* **Lemma 2, divisibility**: `h ∣ f` is preserved by specialisation —
  `Q1Paper.PaperV.map_dvd_of_dvd`.
* **Corollary 8**: a divisor of positive degree with constant nonzero λ-leading coefficient keeps
  positive degree after every specialisation — `Q1Paper.PaperV.specialized_common_factor`.
* **Leading coefficient step of Theorem 4**: the λ^d coefficient of `det (λ•H − B)` is `det H`,
  for every `B` — `Q1Paper.PaperV.coeff_det_smul_sub_X`, with the nonzero form
  `Q1Paper.PaperV.coeff_det_smul_sub_X_ne_zero`.  This supplies the constant leading
  coefficient that Lemma 2 consumes.

*Paper only*: the equivalence "constant rank `d'` for all λ ⟺ the gcd of the `d'`-minors is a
unit" for a matrix pencil over `K(t)[λ]`, and the intrinsic form (Theorem 6).
-/

/-! ## §IV  The bad set

* **Partial — Proposition 14 (column drop)**: its rank step, `rank M ≤ card n - card J` when the
  columns in `J` vanish, is `Q1Paper.PaperV.rank_le_card_compl_of_cols_zero`.  The evaluation at
  `λ₀` (the columns of `P(λ₀)` vanish because `G'` vanishes on `supp(T)`) is bookkeeping and is
  not formalised.

*Paper only*: Theorem 11 (fixed spectral factor, an incidence-variety dimension count on the open
set `Mv ≠ 0`), Theorem 12 (the bad set is closed: quantifier elimination over the coefficient
space of the coefficient test), Theorem 13 (infeasibility ⟺ the stratum is contained in the bad
set, a logical consequence of Theorem 12), and Proposition 15 (the coefficient test).
-/

/-! ## §V  Algorithms

*Paper only*: Theorem 16 (the region with automatic compatibility: one-sided acceptance only, no
outer probability bound) and Theorem 17 (the stratum `t = 1`: "feasible ⟹ `U` is `Z''`-invariant"
is linear algebra given `a ≥ 1`, and the enumeration is combinatorial).  The examples of §V are
decided by exact rational arithmetic in `verification/`, not in Lean.
-/
