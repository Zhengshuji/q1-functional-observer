
import Q1Paper.PaperI.Claim11Final
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
Q1Paper/PaperI/Claim12.lean

Claim 12 of Paper I: the Gram certificate for a full-column-rank pencil.
For `X, G : Matrix (Fin q) (Fin ω) ℝ` with `rank X = ω ≥ 1`, the pencil
`Q(λ) = λ X - G` has rank `ω` for every complex `λ` if and only if the Gram
system `Z_Qᵀ Z_Q x = e₀` is solvable, where `Z_Q` is the window matrix of the
maximal minors of `Q`.

The proof is the instantiation of Claim 11 (`claim11_iff_gram`) at
`(H, H_A) = (X, G)`: full column rank gives a left inverse `X_L` of `X`
(`exists_left_inverse_of_rank_eq`), and `G = (G X_L) X` supplies the factor `F`.
-/


namespace Q1Paper.PaperI

open Matrix Polynomial

/-- **Full column rank gives a left inverse.**  If `X` is `q × ω` of rank `ω`,
there is `X_L` of size `ω × q` with `X_L * X = 1`. -/
theorem exists_left_inverse_of_rank_eq {q ω : ℕ} (X : Matrix (Fin q) (Fin ω) ℝ)
    (h : X.rank = ω) : ∃ X_L : Matrix (Fin ω) (Fin q) ℝ, X_L * X = 1 := by
  have hker : Module.finrank ℝ ↥(LinearMap.ker X.mulVecLin) = 0 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (f := X.mulVecLin)
    have hran : Module.finrank ℝ ↥(LinearMap.range X.mulVecLin) = ω := by
      rw [← Matrix.rank]
      exact h
    have hdom : Module.finrank ℝ (Fin ω → ℝ) = ω := by simp
    rw [hran, hdom] at hrn
    omega
  have hbot : LinearMap.ker X.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hker
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective X.mulVecLin hbot
  refine ⟨(Matrix.toLin').symm g, ?_⟩
  have hto : Matrix.toLin' ((Matrix.toLin').symm g) = g := LinearEquiv.apply_symm_apply _ _
  have hXL : ((Matrix.toLin').symm g : Matrix (Fin ω) (Fin q) ℝ).mulVecLin = g := hto
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_apply', Matrix.toLin'_apply', Matrix.mulVecLin_mul, Matrix.mulVecLin_one, hXL]
  exact hg

/-- **Claim 12.**  The full-column-rank pencil `λ X - G` has rank `ω` at every
complex `λ` exactly when `Z_Qᵀ Z_Q x = e₀` is solvable. -/
theorem claim12_iff_gram {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℝ)
    (hω : 1 ≤ ω) (hrank : X.rank = ω) :
    (∀ z : ℂ, (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)).rank = ω) ↔
      ∃ x : Fin (2 * ω) → ℝ,
        (Matrix.transpose (windowMatrix (minorFamily (q := q) (k := ω) (ω := ω) X G) ω) *
          windowMatrix (minorFamily (q := q) (k := ω) (ω := ω) X G) ω) *ᵥ x
            = windowOne (K := ℝ) ω := by
  obtain ⟨X_L, hXL⟩ := exists_left_inverse_of_rank_eq X hrank
  have hF : ∃ F : Matrix (Fin q) (Fin q) ℝ, G = F * X :=
    ⟨G * X_L, by rw [Matrix.mul_assoc, hXL, Matrix.mul_one]⟩
  exact claim11_iff_gram X G hω hrank hF

end Q1Paper.PaperI
