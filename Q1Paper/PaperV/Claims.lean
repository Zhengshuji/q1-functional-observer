/-!
Q1Paper/PaperV/Claims.lean

The paper interface of Paper V's formalisation: the paper's items in the paper's
order, each with the declarations that carry it.

This file is narration only 闁?it declares nothing.  `ClaimsCheck.lean` machine-checks
that every name below resolves, so a rename breaks the build instead of silently
invalidating this table.

Scope.  Two items are formalised: Theorem 1 (the fibre) and Lemma 2 (specialisation),
plus the corollary that a positive-degree divisor with constant leading coefficient
stays positive after specialisation.  The remaining items are marked *paper only* with
the reason, in the spirit of Paper II's scope notes: they are not silently omitted, and
they are not claimed as Lean.
-/

/-! ## 閹间痉I  The fibre (Theorem 1)

* **The per-row fibre** `{x 闁?T | x + y 闁?U}` 闁?`Q1Paper.PaperV.fibre`.
* **Nonemptiness** `T 闁?(U - y) 闁?闁?闁?y 闁?U + T` 闁?`Q1Paper.PaperV.fibre_nonempty_iff`.
* **Coset form**: any point of the fibre generates it as a coset of `T 闁?U`, so the
  fibre is affine with direction `T 闁?U` and dimension `finrank (T 闁?U)` 闁?  `Q1Paper.PaperV.fibre_eq_coset`.
* **Product over the rows**: the fibre of the paper is nonempty exactly when every
  row's translate lies in `U + T` (the row-wise reading of `U Z'' 闁?U + T`) 闁?  `Q1Paper.PaperV.fibre_prod_nonempty_iff`.
-/

/-! ## 閹间痉II  The criterion (Theorem 4) and its engine

* **Lemma 2, degree**: a nonzero constant 娴?leading coefficient survives
  specialisation, so the 娴?degree cannot drop 闁?  `Q1Paper.PaperV.natDegree_map_eval_of_leadingCoeff_const`.
* **Lemma 2, divisibility**: `h 闁?f` is preserved by specialisation 闁?  `Q1Paper.PaperV.map_dvd_of_dvd`.
* **Corollary 8**: a divisor of positive degree with constant nonzero 娴?leading
  coefficient keeps positive degree after every specialisation, i.e. a bad generic
  fibre is bad at every point 闁?`Q1Paper.PaperV.specialized_common_factor`.

* **Leading coefficient step of Theorem 4**: the $\lambda^d$ coefficient of det (λ•H − B) is det H, for every B — Q1Paper.PaperV.coeff_det_smul_sub_X, and its nonzero form coeff_det_smul_sub_X_ne_zero. This is what supplies the constant leading coefficient that Lemma 2 consumes.

*Paper only*: the equivalence "constant rank `d'` for all 娴?闁?gcd of the `d'`-minors is
a unit" for a matrix pencil over `K(t)[娴ｅ硶`, and the intrinsic form (Theorem 6).  The
first is a statement about gcds of matrix minors in a rational function field; both are
proved in the paper (閹间痉II, 閹间痉II-B).
-/

/-! ## 閹间痉V  The bad set

*Paper only*: Theorem 11 (fixed spectral factor, an incidence-variety dimension count),
Theorem 12 (the bad set is closed: quantifier elimination over the coefficient space of
the coefficient test), Theorem 13 (infeasibility 闁?the stratum is contained in the bad
set, a logical consequence of Theorem 12), Proposition 14 (column drop, a rank bound at
a single 娴?.  The examples of 閹间繄 are decided by exact rational arithmetic in
`verification/`, not in Lean.
-/

/-! ## 閹间繄  Algorithms

*Paper only*: Theorem 15 (the region with automatic compatibility: the argument is
probabilistic, Schwartz闁炽儲褰ppel plus the closedness of 閹间痉V) and Theorem 16 (the stratum
`t = 1`: the implication "feasible 闁?`U` is `Z''`-invariant" is linear algebra, the
enumeration is combinatorial).  Neither is claimed as Lean.
-/
