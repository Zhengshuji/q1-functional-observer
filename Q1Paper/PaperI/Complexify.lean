
import Q1Paper.PaperI.MinorRank
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
Q1Paper/PaperI/Complexify.lean

The real-to-complex bridge needed to connect the paper's real data with the
complex spectral condition:

* `map_submatrix_ofReal`, `det_map_ofReal`: complexifying commutes with taking
  submatrices and determinants;
* `rank_map_ofReal`: complexification does not change the rank.  Both
  inequalities are proved with the rank/minors criterion just established:
  a nonzero minor of `M_ℂ` is the complexification of a nonzero minor of `M`
  (and conversely, since `algebraMap ℝ ℂ` is injective).
-/


namespace Q1Paper.PaperI

open Matrix Polynomial

/-- Complexifying commutes with taking submatrices. -/
theorem map_submatrix_ofReal {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) {ω : ℕ}
    (ρ : Fin ω → Fin m) (κ : Fin ω → Fin n) :
    (M.map (algebraMap ℝ ℂ)).submatrix ρ κ = (M.submatrix ρ κ).map (algebraMap ℝ ℂ) := by
  ext i j
  rfl

/-- Complexifying commutes with the determinant. -/
theorem det_map_ofReal {ω : ℕ} (A : Matrix (Fin ω) (Fin ω) ℝ) :
    (A.map (algebraMap ℝ ℂ)).det = algebraMap ℝ ℂ A.det := by
  have h := RingHom.map_det (algebraMap ℝ ℂ) A
  rw [show (algebraMap ℝ ℂ).mapMatrix A = A.map (algebraMap ℝ ℂ) from rfl] at h
  exact h.symm

/-- `rank M_ℂ ≤ rank M`: a nonzero minor of `M_ℂ` comes from a nonzero minor
of `M`. -/
theorem rank_map_ofReal_le {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    (M.map (algebraMap ℝ ℂ)).rank ≤ M.rank := by
  obtain ⟨ρ, κ, _, _, hdet⟩ :=
    exists_det_submatrix_ne_zero_of_rank (M.map (algebraMap ℝ ℂ)) rfl
  have h1 : (M.submatrix ρ κ).det ≠ 0 := by
    intro h0
    apply hdet
    rw [map_submatrix_ofReal, det_map_ofReal, h0, map_zero]
  exact rank_le_of_det_maximalMinor_ne_zero M ρ κ h1

/-- `rank M ≤ rank M_ℂ`: complexifying a nonzero minor keeps it nonzero. -/
theorem rank_le_map_ofReal {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    M.rank ≤ (M.map (algebraMap ℝ ℂ)).rank := by
  obtain ⟨ρ, κ, _, _, hdet⟩ := exists_det_submatrix_ne_zero_of_rank M rfl
  have h1 : ((M.map (algebraMap ℝ ℂ)).submatrix ρ κ).det ≠ 0 := by
    rw [map_submatrix_ofReal, det_map_ofReal]
    intro h0
    exact hdet ((algebraMap ℝ ℂ).injective (by rw [h0, map_zero]))
  exact rank_le_of_det_maximalMinor_ne_zero (M.map (algebraMap ℝ ℂ)) ρ κ h1

/-- Complexification does not change the rank. -/
theorem rank_map_ofReal {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    (M.map (algebraMap ℝ ℂ)).rank = M.rank :=
  le_antisymm (rank_map_ofReal_le M) (rank_le_map_ofReal M)

end Q1Paper.PaperI
