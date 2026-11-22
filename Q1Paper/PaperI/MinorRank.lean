/-
Q1Paper/PaperI/MinorRank.lean

The rank/minors bridge needed by Claim 11 (and by Claim 2(iii)): for a matrix
`M` over a field and `ω ≤ min (#rows, #cols)`,

  `rank M ≥ ω  ↔  some ω × ω minor of `M` is nonzero`,

together with the polynomial-matrix version: the minors of `P(X)` are
polynomials, and evaluating them at `z` is the same as taking the minor of
`P(z)`.

What is proved here:

* `maximalMinor` : the `ω × ω` minor of a polynomial matrix selected by
  embeddings `Fin ω → m` and `Fin ω → n`, as a polynomial;
* `eval_maximalMinor` : evaluation of a minor is the minor of the evaluated
  matrix;
* `rank_le_of_det_maximalMinor_ne_zero` : a nonzero `ω × ω` minor forces
  `ω ≤ rank M` (the *easy* direction, via `rank_submatrix_le`);
* `exists_det_submatrix_ne_zero_of_rank_pos` : the converse for `ω = 1`
  (`rank M ≥ 1` gives a nonzero entry, i.e. a nonzero `1 × 1` minor).

The general converse `rank M ≥ ω → ∃ nonzero ω × ω minor` is *not* proved here.
It is the classical "rank = size of the largest nonzero minor"; Mathlib does not
have it (searched `Matrix/Rank.lean` and the determinant files).  The two
standard routes are
* row reduction (Mathlib's `Matrix.Pivot` transvection machinery), or
* the Cauchy–Binet formula, which Mathlib also lacks (external Lean
  formalizations exist; see the survey in the project notes).
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace Q1Paper.PaperI

open Matrix Polynomial

variable {K : Type*} [Field K]

/-- The `ω × ω` minor of a polynomial matrix selected by the row embedding `r`
and the column embedding `c`, as a polynomial. -/
noncomputable def maximalMinor {m n : Type*} (P : Matrix m n K[X]) {ω : ℕ}
    (r : Fin ω → m) (c : Fin ω → n) : K[X] :=
  (P.submatrix r c).det

/-- Evaluating a minor at `z` is the same as taking the minor of `P(z)`. -/
theorem eval_maximalMinor {m n : Type*} (P : Matrix m n K[X]) {ω : ℕ}
    (r : Fin ω → m) (c : Fin ω → n) (z : K) :
    (maximalMinor P r c).eval z = ((P.map (Polynomial.eval z)).submatrix r c).det := by
  have hM1 : (P.submatrix r c).map (Polynomial.eval z)
      = (Polynomial.evalRingHom z).mapMatrix (P.submatrix r c) := by
    ext i j
    rfl
  have hM2 : (P.map (Polynomial.eval z)).submatrix r c
      = (P.submatrix r c).map (Polynomial.eval z) := by
    ext i j
    rfl
  have hdet : Matrix.det ((Polynomial.evalRingHom z).mapMatrix (P.submatrix r c))
      = ((P.submatrix r c).det).eval z := by
    rw [← RingHom.map_det]
    rfl
  rw [maximalMinor, hM2, hM1, hdet]

/-- A nonzero `ω × ω` minor forces `rank M ≥ ω`. -/
theorem rank_le_of_det_maximalMinor_ne_zero {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n K) {ω : ℕ} (r : Fin ω → m) (c : Fin ω → n)
    (h : (M.submatrix r c).det ≠ 0) : ω ≤ M.rank := by
  have hrank : (M.submatrix r c).rank = ω := by
    rw [Matrix.rank_of_det_ne_zero h]
    simp
  rw [← hrank]
  exact Matrix.rank_submatrix_le M r c

/-- The `ω = 1` converse: a matrix of positive rank has a nonzero entry, i.e. a
nonzero `1 × 1` minor. -/
theorem exists_det_submatrix_ne_zero_of_rank_pos {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n K) (h : 1 ≤ M.rank) :
    ∃ (r : Fin 1 → m) (c : Fin 1 → n), (M.submatrix r c).det ≠ 0 := by
  have hne : M ≠ 0 := by
    intro h0
    rw [h0, Matrix.rank_zero] at h
    omega
  have hex : ∃ i j, M i j ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (by ext i j; exact hall i j)
  obtain ⟨i, j, hij⟩ := hex
  refine ⟨fun _ => i, fun _ => j, ?_⟩
  simpa [Matrix.det_fin_one] using hij

end Q1Paper.PaperI
