/-!
Q1Paper/PaperV/Claims.lean

The paper interface of Paper V's formalisation: the paper's items in the paper's
order, each with the declarations that carry it.

This file is narration only 鈥?it declares nothing.  `ClaimsCheck.lean` machine-checks
that every name below resolves, so a rename breaks the build instead of silently
invalidating this table.

Scope.  Two items are formalised: Theorem 1 (the fibre) and Lemma 2 (specialisation),
plus the corollary that a positive-degree divisor with constant leading coefficient
stays positive after specialisation.  The remaining items are marked *paper only* with
the reason, in the spirit of Paper II's scope notes: they are not silently omitted, and
they are not claimed as Lean.
-/

/-! ## 搂II  The fibre (Theorem 1)

* **The per-row fibre** `{x 鈭?T | x + y 鈭?U}` 鈥?`Q1Paper.PaperV.fibre`.
* **Nonemptiness** `T 鈭?(U - y) 鈮?鈭?鉄?y 鈭?U + T` 鈥?`Q1Paper.PaperV.fibre_nonempty_iff`.
* **Coset form**: any point of the fibre generates it as a coset of `T 鈯?U`, so the
  fibre is affine with direction `T 鈯?U` and dimension `finrank (T 鈯?U)` 鈥?  `Q1Paper.PaperV.fibre_eq_coset`.
* **Product over the rows**: the fibre of the paper is nonempty exactly when every
  row's translate lies in `U + T` (the row-wise reading of `U Z'' 鈯?U + T`) 鈥?  `Q1Paper.PaperV.fibre_prod_nonempty_iff`.
-/

/-! ## 搂III  The criterion (Theorem 4) and its engine

* **Lemma 2, degree**: a nonzero constant 位-leading coefficient survives
  specialisation, so the 位-degree cannot drop 鈥?  `Q1Paper.PaperV.natDegree_map_eval_of_leadingCoeff_const`.
* **Lemma 2, divisibility**: `h 鈭?f` is preserved by specialisation 鈥?  `Q1Paper.PaperV.map_dvd_of_dvd`.
* **Corollary 8**: a divisor of positive degree with constant nonzero 位-leading
  coefficient keeps positive degree after every specialisation, i.e. a bad generic
  fibre is bad at every point 鈥?`Q1Paper.PaperV.specialized_common_factor`.

*Paper only*: the equivalence "constant rank `d'` for all 位 鉄?gcd of the `d'`-minors is
a unit" for a matrix pencil over `K(t)[位]`, and the intrinsic form (Theorem 6).  The
first is a statement about gcds of matrix minors in a rational function field; both are
proved in the paper (搂III, 搂III-B).
-/

/-! ## 搂IV  The bad set

*Paper only*: Theorem 11 (fixed spectral factor, an incidence-variety dimension count),
Theorem 12 (the bad set is closed: quantifier elimination over the coefficient space of
the coefficient test), Theorem 13 (infeasibility 鉄?the stratum is contained in the bad
set, a logical consequence of Theorem 12), Proposition 14 (column drop, a rank bound at
a single 位).  The examples of 搂V are decided by exact rational arithmetic in
`verification/`, not in Lean.
-/

/-! ## 搂V  Algorithms

*Paper only*: Theorem 15 (the region with automatic compatibility: the argument is
probabilistic, Schwartz鈥揨ippel plus the closedness of 搂IV) and Theorem 16 (the stratum
`t = 1`: the implication "feasible 鉄?`U` is `Z''`-invariant" is linear algebra, the
enumeration is combinatorial).  Neither is claimed as Lean.
-/
