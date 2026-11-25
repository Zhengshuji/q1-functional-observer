import Q1Paper.PaperI.ReindexSpectral
import Q1Paper.PaperI.ChartComplete

/-!
# Soundness of Algorithm 1 at the level of `DEC`

If the free block `R` admits a chart point `PhiPoint` for its compressed data, then
`DEC C A L0 r` holds.  This is the direction the Lean `DEC` supports: its spectral condition is the
real-λ one, and `feasible_of_phiPoint` supplies exactly that from the chart point (via the Gram
certificate, which characterises the complex-λ condition — complex implies real).

The bridge is the reindexing pair `rawAlgebraic_submatrix` / `rawSpectral_submatrix`: `PhiPoint` is
indexed by `Fin q`, while `DEC`'s `L = fromRows L0 R` has row type `Fin r0 ⊕ Fin r`.
-/

namespace Q1Paper.PaperI.Soundness

open Q1Paper Q1Subspace Q1Paper.PaperI Q1Paper.PaperI.ChartComplete

/-- Reindexing the rows of a product: `(X.submatrix e id) * A = (X * A).submatrix e id`. -/
theorem submatrix_mul_right {m m' n p : Type*} [Fintype m] [Fintype m'] [Fintype n] [Fintype p]
    [Mul K] [AddCommMonoid K]
    (X : Matrix m n K) (A : Matrix n p K) (e : m' → m) :
    X.submatrix e id * A = (X * A).submatrix e id := by
  ext i j
  simp [Matrix.mul_apply]

/-- **Soundness of Algorithm 1.**  A chart point for the compressed data of `[L₀; R]` implies
`DEC C A L0 r`. -/
theorem dec_of_phiPoint {p r0 r n k ω : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (R : Matrix (Fin r) (Fin n) ℝ)
    (N : Matrix (Fin n) (Fin k) ℝ) (hω : 1 ≤ ω)
    (hN : N.mulVecLin.range = (Matrix.fromRows (C * A) C).mulVecLin.ker)
    (hHr : ((Matrix.fromRows L0 R).submatrix finSumFinEquiv.symm id * N).rank = ω)
    (P : PhiPoint ((Matrix.fromRows L0 R).submatrix finSumFinEquiv.symm id * N)
      ((Matrix.fromRows L0 R).submatrix finSumFinEquiv.symm id * A * N) ω) :
    DEC C A L0 r := by
  have hP := feasible_of_phiPoint C A
    ((Matrix.fromRows L0 R).submatrix finSumFinEquiv.symm id) N hN hω hHr P
  obtain ⟨h1, h2⟩ := hP
  have hmul : (Matrix.fromRows L0 R).submatrix finSumFinEquiv.symm id * A =
      (Matrix.fromRows L0 R * A).submatrix finSumFinEquiv.symm id :=
    submatrix_mul_right (Matrix.fromRows L0 R) A finSumFinEquiv.symm
  refine ⟨R, ?_, ?_⟩
  · refine (Q1Paper.PaperI.ReindexAlgebraic.rawAlgebraic_submatrix C (C * A) (Matrix.fromRows L0 R)
      (Matrix.fromRows L0 R * A) finSumFinEquiv.symm).mp ?_
    rw [hmul] at h1
    exact h1
  · refine Q1Paper.PaperI.ReindexSpectral.rawSpectral_submatrix C (C * A) (Matrix.fromRows L0 R)
      (Matrix.fromRows L0 R * A) finSumFinEquiv.symm ?_
    rw [hmul] at h2
    exact h2

end Q1Paper.PaperI.Soundness
