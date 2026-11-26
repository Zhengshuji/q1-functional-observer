import Q1Paper.PaperII.MainTheorems

/-!
Q1Paper/PaperII/Appendix.lean

The appendix instance (`app:example`) at one point of the pencil.

Paper II's appendix prints an explicit rational instance (`n = 8`, `p = 2`, four-row witness
`L = [L₀; R]`) and claims `q_min ≤ 4` for it.  The full certificate — (5a), the vanishing of the
pencil determinant, and the gcd of all 7×7 minors being a nonzero constant — is checked by exact
rational arithmetic in `scripts/verify_paperII_example.py`.

This file records the one piece of that certificate that is cheap to re-check in Lean: the pencil
at `λ = 0`, i.e. the matrix `[−LA; CA; C]`, has the nonzero kernel vector below, so its
determinant vanishes.
-/

namespace Q1Paper.PaperII

open Matrix

/-- The pencil at `λ = 0`: rows `−LA`, then `CA`, then `C`, for the appendix instance. -/
def appendixPencil0 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(-1 : ℚ), -2, -1, -2, -2, 8, 3, -4;
     3, -1, -1, 3, 0, 4, -1, -1;
     -1, -122369/32067, 65785/10689, 10852/32067, 0, 0, -1, -44407/10689;
     1, 1652/4581, -118/1527, 5879/4581, 0, 0, 0, 118/1527;
     4, 2, -4, 4, 2, -1, -3, 6;
     -1, -2, -1, -3, -4, -5, 4, 4;
     -2, -2, 2, -2, -1, 0, 1, -3;
     0, 0, 1, 2, 2, 3, -1, -2]

/-- The kernel vector of the appendix pencil at `λ = 0`. -/
def appendixKernel : Fin 8 → ℚ :=
  ![(-390 : ℚ), 97, -22, 272, -419, 58, -252, 55]

/-- The appendix pencil at `λ = 0` is singular: it kills a nonzero vector. -/
theorem appendix_pencil_kernel :
    appendixPencil0.mulVec appendixKernel = 0 ∧ appendixKernel ≠ 0 := by
  constructor
  · ext i
    fin_cases i <;>
      simp [appendixPencil0, appendixKernel, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] <;>
      norm_num
  · intro h
    have h0 := congrFun h 0
    simp [appendixKernel] at h0

end Q1Paper.PaperII
