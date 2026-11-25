import Q1Paper.PaperI.KernelLift
import Q1Paper.PaperI.Soundness

/-!
# Soundness in the paper's own specification: `PhiPoint → complexDEC`

`dec_of_phiPoint` concludes the auxiliary real-λ `DEC`.  But the Gram certificate is a **complex**-λ
statement, so the paper's soundness is the one proved here:

    PhiPoint  =>  complexDEC

The two ingredients that were missing and are now available:

* `range_mulVecLin_eq_ker_map_complex` — the complexified kernel basis spans the complex kernel, which
  is the hypothesis `rawSpectral_iff_compressed` needs at `K = ℂ`;
* `compressedSpectral_submatrix` — the compressed spectral condition is invariant under a row
  bijection (below), which is what lets the chart's reindexed block speak about `fromRows L0 R`.
-/

namespace Q1Paper.PaperI.ComplexSoundness

open Q1Paper Q1Subspace Q1Paper.PaperI Q1Paper.PaperI.ChartComplete
  Q1Paper.PaperI.DecComplex Q1Paper.PaperI.Reindex Q1Paper.PaperI.Reindex2
  Q1Paper.PaperI.KernelLift Q1Paper.PaperI.Soundness Q1Paper.PaperI.FromRowsMap

variable {K : Type*} [Field K]

/-- **The compressed spectral condition is invariant under a row bijection.** -/
theorem compressedSpectral_submatrix {m m' k : Type*} [Fintype m] [Fintype m'] [Fintype k]
    (H HA : Matrix m k K) (e : m' ≃ m) :
    compressedSpectral (H.submatrix e (Equiv.refl k)) (HA.submatrix e (Equiv.refl k)) ↔
      compressedSpectral H HA := by
  have hstep : ∀ z : K, (z • H.submatrix e (Equiv.refl k) - HA.submatrix e (Equiv.refl k)) =
      (z • H - HA).submatrix e (Equiv.refl k) := by
    intro z
    ext i j
    simp [Matrix.sub_apply, Matrix.smul_apply]
  constructor
  · intro h z
    have hz := h z
    rw [hstep z] at hz
    simp only [Matrix.rank_submatrix] at hz
    exact hz
  · intro h z
    have hz := h z
    rw [hstep z]
    simp only [Matrix.rank_submatrix]
    exact hz

/-- **Soundness in the paper's specification.** -/
theorem decComplex_of_phiPoint {p r0 r n k ω : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (R : Matrix (Fin r) (Fin n) ℝ)
    (N : Matrix (Fin n) (Fin k) ℝ) (hω : 1 ≤ ω)
    (hN : N.mulVecLin.range = (Matrix.fromRows (C * A) C).mulVecLin.ker)
    (hHr : ((Matrix.fromRows L0 R).submatrix finSumFinEquiv.symm id * N).rank = ω)
    (P : PhiPoint ((Matrix.fromRows L0 R).submatrix finSumFinEquiv.symm id * N)
      ((Matrix.fromRows L0 R).submatrix finSumFinEquiv.symm id * A * N) ω) :
    complexDEC C A L0 r := by
  -- notation
  set L : Matrix (Fin r0 ⊕ Fin r) (Fin n) ℝ := Matrix.fromRows L0 R with hL
  set e : Fin (r0 + r) ≃ Fin r0 ⊕ Fin r := finSumFinEquiv.symm with he
  -- the algebraic half, from the already-proved real-λ soundness
  have hP := feasible_of_phiPoint C A (L.submatrix e id) N hN hω hHr P
  obtain ⟨h1, _⟩ := hP
  have hmul : L.submatrix e id * A = (L * A).submatrix e id :=
    submatrix_mul_right L A e
  have key1 : rawAlgebraic C (C * A) L (L * A) := by
    refine (rawAlgebraic_submatrix C (C * A) L (L * A) e).mp ?_
    rw [hmul] at h1
    exact h1
  -- the spectral half, over `ℂ`
  have hNC := range_mulVecLin_eq_ker_map_complex (Matrix.fromRows (C * A) C) N hN
  rw [fromRows_map] at hNC
  obtain ⟨F, hF⟩ := exists_factor_of_rowSpace_le (L.submatrix e id * N)
    (L.submatrix e id * A * N) (rowSpace_le_of_phiPoint P)
  have hgram := (claim11_iff_gram (L.submatrix e id * N) (L.submatrix e id * A * N)
    hω hHr ⟨F, hF⟩).mpr ⟨P.x, P.gram⟩
  -- the compressed complex condition for the reindexed block
  have hcomp : compressedSpectral ((L.submatrix e id * N).map (algebraMap ℝ ℂ))
      ((L.submatrix e id * A * N).map (algebraMap ℝ ℂ)) := by
    intro z
    rw [hgram z]
    rw [show ((L.submatrix e id * N).map (algebraMap ℝ ℂ)).rank =
      (L.submatrix e id * N).rank from rank_map_ofReal_any _]
    exact hHr.symm
  -- reindex it back to `L`
  have hcompL : compressedSpectral ((L * N).map (algebraMap ℝ ℂ))
      (((L * A) * N).map (algebraMap ℝ ℂ)) := by
    have hsub : (L.submatrix e id * N).map (algebraMap ℝ ℂ) =
        ((L * N).map (algebraMap ℝ ℂ)).submatrix e id := by
      rw [submatrix_mul_right]
      rfl
    have hsub2 : (L.submatrix e id * A * N).map (algebraMap ℝ ℂ) =
        (((L * A) * N).map (algebraMap ℝ ℂ)).submatrix e id := by
      rw [submatrix_mul_right]
      rfl
    rw [hsub, hsub2] at hcomp
    exact (compressedSpectral_submatrix ((L * N).map (algebraMap ℝ ℂ))
      (((L * A) * N).map (algebraMap ℝ ℂ)) e).mp hcomp
  -- lift to the raw stack over `ℂ`
  have key2 : spectralComplexRaw C (C * A) L (L * A) := by
    refine (Q1Paper.PaperI.rawSpectral_iff_compressed (C.map (algebraMap ℝ ℂ))
      ((C * A).map (algebraMap ℝ ℂ)) (L.map (algebraMap ℝ ℂ))
      ((L * A).map (algebraMap ℝ ℂ)) (N.map (algebraMap ℝ ℂ)) hNC).mpr ?_
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact hcompL
  exact ⟨R, key1, key2⟩

end Q1Paper.PaperI.ComplexSoundness
