import Q1Paper.PaperI.ComplexSoundness

/-!
# Towards completeness: compressing the complex condition

`decComplex_of_phiPoint` went `PhiPoint → complexDEC`.  The other direction needs the *compressed*
complex condition out of `complexDEC`'s spectral half, i.e. the `.mp` direction of
`rawSpectral_iff_compressed` at `K = ℂ`.  This file provides that step.
-/

namespace Q1Paper.PaperI.Completeness

open Q1Paper Q1Subspace Q1Paper.PaperI Q1Paper.PaperI.DecComplex
  Q1Paper.PaperI.KernelLift Q1Paper.PaperI.FromRowsMap Q1Paper.PaperI.ComplexSoundness

variable {p q n k : Type*} [Fintype p] [Fintype q] [Fintype n] [Fintype k]

/-- **The complex raw condition compresses.** -/
theorem compressed_of_spectralComplexRaw (C CA : Matrix p n ℝ) (L LA : Matrix q n ℝ)
    (N : Matrix n k ℝ)
    (hNC : (N.map (algebraMap ℝ ℂ)).mulVecLin.range =
      (Matrix.fromRows (CA.map (algebraMap ℝ ℂ)) (C.map (algebraMap ℝ ℂ))).mulVecLin.ker)
    (h : spectralComplexRaw C CA L LA) :
    compressedSpectral ((L * N).map (algebraMap ℝ ℂ)) ((LA * N).map (algebraMap ℝ ℂ)) := by
  have hstep := (Q1Paper.PaperI.rawSpectral_iff_compressed (C.map (algebraMap ℝ ℂ))
    (CA.map (algebraMap ℝ ℂ)) (L.map (algebraMap ℝ ℂ)) (LA.map (algebraMap ℝ ℂ))
    (N.map (algebraMap ℝ ℂ)) hNC).mp h
  rwa [← Matrix.map_mul, ← Matrix.map_mul] at hstep

end Q1Paper.PaperI.Completeness
