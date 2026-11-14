import Mathlib
import Q1Paper.Q1Pencil
import Q1Paper.Q1RowSpace
import Q1Paper.Q1Projection

/-!
# Step 3, matrix form: `row H_A = row H`

The algebraic condition gives `row H_A ⊆ row H` (file `Q1RowSpace`), and the
spectral condition at `z = 0` gives `rank H_A = rank H`.  Equal dimension plus
inclusion gives equality.

`H_A` is an **independent** matrix here: it is the block `L A N` of `[L A; L] N`,
and it is not `H * A` in general (see the header of `Q1Pencil`).
-/

namespace Q1Subspace

open Module

variable {K : Type*} [Field K]
  {m n : Type*} [Fintype m] [Fintype n]

/-- Negating a matrix does not change the range of its column map. -/
theorem mulVecLin_neg (M : Matrix m n K) :
    Matrix.mulVecLin (-M) = -Matrix.mulVecLin M := by
  ext v
  simp [Matrix.mulVecLin_apply, Matrix.neg_mulVec]

/-- Negating a matrix does not change its rank. -/
theorem matrixRank_neg (M : Matrix m n K) : matrixRank (-M) = matrixRank M := by
  unfold matrixRank
  rw [mulVecLin_neg, LinearMap.range_neg]

/-- At `z = 0` the spectral condition reads `rank H_A = rank H`. -/
theorem rank_of_spectralCondition (H H_A : Matrix m n K)
    (h : SpectralCondition H H_A) : Matrix.rank H_A = Matrix.rank H := by
  have h0 := h 0
  rw [spectralCondition_zero_eq_zero] at h0
  have hz : matrixRank (-H_A) = matrixRank H := h0
  rwa [matrixRank_neg] at hz

/-- **Step 3, matrix form**: the algebraic condition and the spectral condition
at zero force `row H_A = row H`. -/
theorem rowSpace_eq (H H_A : Matrix m n K)
    (halg : Matrix.rank (Matrix.fromRows H_A H) = Matrix.rank H)
    (hspec : SpectralCondition H H_A) : rowSpace H_A = rowSpace H := by
  have hle : rowSpace H_A ≤ rowSpace H :=
    (rank_fromRows_eq_rank_iff H_A H).mp halg
  have hrank : Matrix.rank H_A = Matrix.rank H :=
    rank_of_spectralCondition H H_A hspec
  rw [rank_eq_finrank_rowSpace, rank_eq_finrank_rowSpace] at hrank
  exact Submodule.eq_of_le_of_finrank_eq hle hrank

end Q1Subspace
