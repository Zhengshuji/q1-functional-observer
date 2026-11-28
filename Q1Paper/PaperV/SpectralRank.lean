import Mathlib
import Q1Paper.PaperV.RankMinor

/-!
Q1Paper/PaperV/SpectralRank.lean

The linear-algebra core of the spectral form of the thin-stratum criterion.

Paper-side statement (research notes, `？？？/workspace/q1_false/feasibility_geometry/attempts/803`):
for `U = row H` with `rank H = d'` and `λ₀ ∉ spec Z''`, the matrix `λ₀ H − H Z'' = H (λ₀ I − Z'')`
has rank `d'`; hence some `d'`-minor does not vanish at `λ₀`, so `λ₀` cannot be a common root of all
the `d'`-minors.  Equivalently: only eigenvalues of `Z''` can be critical.

This module checks the rank statement: right multiplication by an invertible matrix preserves rank.
-/

set_option maxHeartbeats 800000

namespace Q1Paper.PaperV

/-- Right multiplication by a matrix with nonzero determinant preserves rank. -/
theorem rank_mul_of_det_ne_zero {K : Type*} [Field K] {q k : ℕ}
    (H : Matrix (Fin q) (Fin k) K) (M : Matrix (Fin k) (Fin k) K) (hM : M.det ≠ 0) :
    (H * M).rank = H.rank :=
  Matrix.rank_mul_eq_left_of_det_ne_zero M H hM

/-- **Spectral form, linear-algebra core.** If `λ₀ I − Z''` is invertible, then the pencil
`λ₀ H − H Z''` has the same rank as `H`; in particular, at a non-eigenvalue of `Z''` the rank does not
drop. -/
theorem rank_smul_sub_mul_of_det_ne_zero {K : Type*} [Field K] {q k : ℕ}
    (H : Matrix (Fin q) (Fin k) K) (Z : Matrix (Fin k) (Fin k) K) (lam : K)
    (h : (lam • (1 : Matrix (Fin k) (Fin k) K) - Z).det ≠ 0) :
    (lam • H - H * Z).rank = H.rank := by
  have hmul : lam • H - H * Z = H * (lam • (1 : Matrix (Fin k) (Fin k) K) - Z) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  rw [hmul, rank_mul_of_det_ne_zero H _ h]

/-- Consequently, at a non-eigenvalue the `d'`-minors cannot all vanish. -/
theorem exists_minor_ne_zero_of_det_ne_zero {K : Type*} [Field K] {q k d : ℕ}
    (H : Matrix (Fin q) (Fin k) K) (Z : Matrix (Fin k) (Fin k) K) (lam : K)
    (hd : H.rank = d) (h : (lam • (1 : Matrix (Fin k) (Fin k) K) - Z).det ≠ 0) :
    ∃ e : Fin d → Fin q, ∃ f : Fin d → Fin k, ((lam • H - H * Z).submatrix e f).det ≠ 0 := by
  have hrank : (lam • H - H * Z).rank = d := by
    rw [rank_smul_sub_mul_of_det_ne_zero H Z lam h, hd]
  exact exists_submatrix_det_ne_zero_of_le_rank _ (le_of_eq hrank.symm)

end Q1Paper.PaperV
