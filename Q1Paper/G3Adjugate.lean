/-
Q1Paper/G3Adjugate.lean

The rectangular left inverse of the paper: for a `q × ω` matrix `Q` over a commutative
ring and a choice `e : Fin ω → Fin q` of `ω` rows, put

  `Q_I = Q.submatrix e id`,   `f_I = det Q_I`,   `S_I = adj(Q_I) * E_I`,

where `E_I` is the row-selection matrix.  Then `S_I * Q = f_I • 1`.

This is the first ingredient of the `r = 0` construction: combining these blocks with
Bezout coefficients `g_I` (see `G2Assembly`) gives a polynomial left inverse
`S = Σ g_I S_I` with `S * Q = 1` and `deg S ≤ 2ω - 2`.
-/

import Mathlib.LinearAlgebra.Matrix.Adjugate

open Matrix

namespace Q1Paper

variable {R : Type*} [CommRing R] {q ω : ℕ}

/-- The `ω × q` matrix selecting the rows indexed by `e`. -/
def rowSel (e : Fin ω → Fin q) : Matrix (Fin ω) (Fin q) R :=
  Matrix.of fun i k => if e i = k then 1 else 0

/-- Selecting rows then multiplying: `E_I * Q = Q_I`. -/
theorem rowSel_mul (e : Fin ω → Fin q) (Q : Matrix (Fin q) (Fin ω) R) :
    rowSel (R := R) e * Q = Q.submatrix e id := by
  ext i j
  simp only [Matrix.mul_apply, rowSel, Matrix.of_apply, Matrix.submatrix_apply, id]
  rw [Finset.sum_eq_single (e i)]
  · simp
  · intro b _ hb
    have hne : e i ≠ b := fun h => hb h.symm
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ (e i)) h

/-- The rectangular left inverse of `Q` associated with the row set `e`. -/
def adjRowInverse (e : Fin ω → Fin q) (Q : Matrix (Fin q) (Fin ω) R) :
    Matrix (Fin ω) (Fin q) R :=
  Matrix.adjugate (Q.submatrix e id) * rowSel (R := R) e

/-- It is a left inverse up to the determinant of the selected square block. -/
theorem adjRowInverse_mul (e : Fin ω → Fin q) (Q : Matrix (Fin q) (Fin ω) R) :
    adjRowInverse (R := R) e Q * Q =
      Matrix.det (Q.submatrix e id) • (1 : Matrix (Fin ω) (Fin ω) R) := by
  rw [adjRowInverse, Matrix.mul_assoc, rowSel_mul, Matrix.adjugate_mul]

end Q1Paper
