import Q1Paper.PaperI.S08_ChartEquivalence.ComplexCompression
import Q1Paper.PaperI.S08_ChartEquivalence.ChartComplete

/-!
# Completeness: `complexDEC → PhiPoint`

The reverse of `decComplex_of_phiPoint`.  Given the free block `R` satisfying the paper's complex
conditions, the reindexed compressed pair carries a chart point.

Note the hypothesis `1 ≤ ω`: `PhiPoint`'s Gram certificate comes from `claim11_iff_gram`, which needs
`1 ≤ ω`.  The degenerate case `ω = 0` is a separate branch in the paper and is **not** covered here.
-/

namespace Q1Paper.PaperI.ComplexCompleteness

open Q1Paper Q1Subspace Q1Paper.PaperI Q1Paper.PaperI.ChartComplete
  Q1Paper.PaperI.DecComplex Q1Paper.PaperI.ReindexAlgebraic Q1Paper.PaperI.ReindexSpectral
  Q1Paper.PaperI.KernelLift Q1Paper.PaperI.FromRowsMap
  Q1Paper.PaperI.ComplexSoundness Q1Paper.PaperI.ComplexCompression Q1Paper.PaperI.Soundness

/-- **Completeness, nondegenerate case.** -/
theorem phiPoint_of_complexDEC {p r0 r n k ω : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (R : Matrix (Fin r) (Fin n) ℝ)
    (N : Matrix (Fin n) (Fin k) ℝ)
    (hN : N.mulVecLin.range = (Matrix.fromRows (C * A) C).mulVecLin.ker)
    (h1 : rawAlgebraic C (C * A) (Matrix.fromRows L0 R) (Matrix.fromRows L0 R * A))
    (h2 : spectralComplexRaw C (C * A) (Matrix.fromRows L0 R) (Matrix.fromRows L0 R * A))
    (hω : 1 ≤ ω)
    (hωr : ((Matrix.fromRows L0 R).submatrix finSumFinEquiv.symm id * N).rank = ω) :
    Nonempty (PhiPoint ((Matrix.fromRows L0 R).submatrix finSumFinEquiv.symm id * N)
      ((Matrix.fromRows L0 R).submatrix finSumFinEquiv.symm id * A * N) ω) := by
  set L : Matrix (Fin r0 ⊕ Fin r) (Fin n) ℝ := Matrix.fromRows L0 R with hL
  set e : Fin (r0 + r) ≃ Fin r0 ⊕ Fin r := finSumFinEquiv.symm with he
  set H : Matrix (Fin (r0 + r)) (Fin k) ℝ := L.submatrix e id * N with hHdef
  set HA : Matrix (Fin (r0 + r)) (Fin k) ℝ := L.submatrix e id * A * N with hHAdef
  change Nonempty (PhiPoint H HA ω)
  -- the complex raw condition compresses, and reindexes back to `H`, `HA`
  have hNC := range_mulVecLin_eq_ker_map_complex (Matrix.fromRows (C * A) C) N hN
  rw [fromRows_map] at hNC
  have hcomp := compressed_of_spectralComplexRaw C (C * A) L (L * A) N hNC h2
  have hmul : L.submatrix e id * A = (L * A).submatrix e id := submatrix_mul_right L A e
  have hsub : H.map (algebraMap ℝ ℂ) =
      ((L * N).map (algebraMap ℝ ℂ)).submatrix e id := by
    rw [hHdef, submatrix_mul_right]
    rfl
  have hsub2 : HA.map (algebraMap ℝ ℂ) =
      (((L * A) * N).map (algebraMap ℝ ℂ)).submatrix e id := by
    rw [hHAdef, hmul, submatrix_mul_right]
    rfl
  have hcompH : compressedSpectral (H.map (algebraMap ℝ ℂ)) (HA.map (algebraMap ℝ ℂ)) := by
    rw [hsub, hsub2]
    exact (compressedSpectral_submatrix ((L * N).map (algebraMap ℝ ℂ))
      (((L * A) * N).map (algebraMap ℝ ℂ)) e).mpr hcomp
  -- the algebraic half for the reindexed block, and the row inclusion
  have h1' : rawAlgebraic C (C * A) (L.submatrix e id) ((L * A).submatrix e id) :=
    (rawAlgebraic_submatrix C (C * A) L (L * A) e).mpr h1
  have hrow : Q1Subspace.rowSpace HA ≤ Q1Subspace.rowSpace H := by
    have hr := (Q1Paper.PaperI.rawAlgebraic_iff_rowSpace C (C * A) (L.submatrix e id)
      ((L * A).submatrix e id) N hN).mp h1'
    rw [hHdef, hHAdef, hmul]
    exact hr
  -- assemble
  obtain ⟨X, B, G, XL, hXBv, hGBv, hXLv, hXrankv⟩ :=
    exists_chart_factorization H HA hωr hrow
  have hcompZ : ∀ z : ℂ, (z • H.map (algebraMap ℝ ℂ) - HA.map (algebraMap ℝ ℂ)).rank = ω := by
    intro z
    have hz := hcompH z
    rwa [show (H.map (algebraMap ℝ ℂ)).rank = ω from by
      rw [rank_map_ofReal_any]
      exact hωr] at hz
  obtain ⟨F, hF⟩ := exists_factor_of_rowSpace_le H HA hrow
  obtain ⟨x, hx⟩ := (claim11_iff_gram H HA hω hωr ⟨F, hF⟩).mp hcompZ
  exact ⟨X, B, G, XL, x, hXrankv, hXBv, hGBv, hXLv, hx⟩

end Q1Paper.PaperI.ComplexCompleteness
