import Q1Paper.PaperI.DecComplex

/-!
# Lifting the kernel basis to `ℂ`

`rawSpectral_iff_compressed` at `K = ℂ` needs the complexified kernel basis to span the complex
kernel.  Over `ℝ` that is a hypothesis (`hN`); over `ℂ` it is a theorem, and this file proves it.

Route (inclusion + dimension), as recommended in review:

* **inclusion.**  `hN` gives `M * N = 0`; complexifying with `Matrix.map_mul` gives
  `M_ℂ * N_ℂ = 0`, hence `range N_ℂ ≤ ker M_ℂ`.
* **dimension.**  Both sides have complex dimension `card n - rank M`, using
  `rank_map_ofReal_any` and rank-nullity twice.

Then `Submodule.eq_of_le_of_finrank_eq` finishes.  No hypothesis of full column rank for `N` is
used — `hN` alone suffices, which is the point of the dimension route.
-/

namespace Q1Paper.PaperI.KernelLift

open Q1Paper Q1Subspace Q1Paper.PaperI Q1Paper.PaperI.DecComplex

variable {p n k : Type*} [Fintype p] [Fintype n] [Fintype k] [DecidableEq k]

/-- **The real hypothesis gives `M * N = 0`.** -/
theorem mul_eq_zero_of_range_le_ker (M : Matrix p n ℝ) (N : Matrix n k ℝ)
    (hN : N.mulVecLin.range = M.mulVecLin.ker) : M * N = 0 := by
  ext i j
  have hmem : N.mulVecLin (Pi.single j 1) ∈ M.mulVecLin.ker := by
    rw [← hN]
    exact LinearMap.mem_range_self _ _
  have h0 : (M * N).mulVecLin (Pi.single j (1 : ℝ)) = 0 := by
    rw [Matrix.mulVecLin_mul]
    exact hmem
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single] at h0
  simpa using congrFun h0 i

/-- **The complexified kernel basis spans the complex kernel.** -/
theorem range_mulVecLin_eq_ker_map_complex (M : Matrix p n ℝ) (N : Matrix n k ℝ)
    (hN : N.mulVecLin.range = M.mulVecLin.ker) :
    (N.map (algebraMap ℝ ℂ)).mulVecLin.range = (M.map (algebraMap ℝ ℂ)).mulVecLin.ker := by
  have hMN : M * N = 0 := mul_eq_zero_of_range_le_ker M N hN
  have hle : (N.map (algebraMap ℝ ℂ)).mulVecLin.range ≤
      (M.map (algebraMap ℝ ℂ)).mulVecLin.ker := by
    rintro v ⟨w, rfl⟩
    simp only [LinearMap.mem_ker]
    rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, ← Matrix.map_mul, hMN]
    simp
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have hnul := N.mulVecLin.finrank_range_add_finrank_ker
  have hnulM := M.mulVecLin.finrank_range_add_finrank_ker
  have hnulC := (N.map (algebraMap ℝ ℂ)).mulVecLin.finrank_range_add_finrank_ker
  have hnulMC := (M.map (algebraMap ℝ ℂ)).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hnul hnulM hnulC hnulMC
  have hrN : Module.finrank ℂ ((N.map (algebraMap ℝ ℂ)).mulVecLin.range) =
      Module.finrank ℝ (N.mulVecLin.range) := by
    simpa [Matrix.rank] using rank_map_ofReal_any N
  have hrM : Module.finrank ℂ ((M.map (algebraMap ℝ ℂ)).mulVecLin.range) =
      Module.finrank ℝ (M.mulVecLin.range) := by
    simpa [Matrix.rank] using rank_map_ofReal_any M
  have hkerM : Module.finrank ℂ ((M.map (algebraMap ℝ ℂ)).mulVecLin.ker) =
      Module.finrank ℝ (M.mulVecLin.ker) := by
    omega
  rw [hrN, hkerM, hN]

end Q1Paper.PaperI.KernelLift
