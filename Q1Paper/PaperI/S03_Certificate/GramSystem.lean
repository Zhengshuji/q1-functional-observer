
import Mathlib.LinearAlgebra.Matrix.Rank
import Q1Paper.Q1RowSpace
import Q1Paper.Q1Subspace

/-!
Q1Paper/PaperI/S03_Certificate/GramSystem.lean

The Gram step of Paper I, Claim 11: for a real matrix `Z` and a vector `e0`,

  `e0 ∈ row Z  ↔  ∃ x, (Zᵀ * Z) *ᵥ x = e0`.

This is the last equivalence of Claim 11.  The proof uses two lemmas that are
already in Mathlib (`LinearAlgebra/Matrix/Rank.lean`, section
`LinearOrderedField`):

* `Matrix.rank_transpose_mul_self : (Aᵀ * A).rank = A.rank`,
* `Matrix.ker_mulVecLin_transpose_mul_self`.

With them, `range (Zᵀ * Z) = range Zᵀ` follows from the inclusion
`range (Zᵀ * Z) ≤ range Zᵀ` and the equality of the dimensions.

The *first* equivalence of Claim 11, `(5b) ↔ e0 ∈ row Z`, is the Bezout/window
composition and is not part of this file.
-/


namespace Q1Paper.PaperI

open Matrix

/-- The row space of `Z` is the range of the transposed multiplication map:
the rows of `Z` are the columns of `Zᵀ`. -/
theorem rowSpace_eq_range_transpose {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
    (Z : Matrix m k ℝ) :
    Q1Subspace.rowSpace Z = LinearMap.range (Matrix.transpose Z).mulVecLin := by
  rw [show Q1Subspace.rowSpace Z = Q1Subspace.rowSpan Z from rfl]
  rw [← Q1Subspace.range_eq_rowSpan]
  have hmap : Matrix.vecMulLinear Z = (Matrix.transpose Z).mulVecLin := by
    ext v
    simpa using (Matrix.vecMul_transpose (A := Matrix.transpose Z) v)
  rw [hmap]

/-- `range (Zᵀ * Z) = range Zᵀ` for a real matrix: the Gram matrix has the
same range as the transpose. -/
theorem range_transpose_mul_self {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
    (Z : Matrix m k ℝ) :
    LinearMap.range ((Matrix.transpose Z * Z).mulVecLin) =
      LinearMap.range (Matrix.transpose Z).mulVecLin := by
  have hle : LinearMap.range ((Matrix.transpose Z * Z).mulVecLin) ≤
      LinearMap.range (Matrix.transpose Z).mulVecLin := by
    rintro _ ⟨x, rfl⟩
    refine ⟨Z.mulVecLin x, ?_⟩
    rw [Matrix.mulVecLin_mul]
    rfl
  have hdim : Module.finrank ℝ ↥(LinearMap.range ((Matrix.transpose Z * Z).mulVecLin)) =
      Module.finrank ℝ ↥(LinearMap.range (Matrix.transpose Z).mulVecLin) := by
    change (Matrix.transpose Z * Z).rank = (Matrix.transpose Z).rank
    rw [Matrix.rank_transpose_mul_self, Matrix.rank_transpose]
  exact Submodule.eq_of_le_of_finrank_eq hle hdim

/-- The Gram certificate, vector form: `e0` lies in the range of `Zᵀ` exactly
when `Zᵀ Z x = e0` is solvable. -/
theorem mem_range_transpose_iff_exists_gram {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
    (Z : Matrix m k ℝ) (e0 : k → ℝ) :
    e0 ∈ LinearMap.range (Matrix.transpose Z).mulVecLin ↔
      ∃ x : k → ℝ, (Matrix.transpose Z * Z) *ᵥ x = e0 := by
  rw [← range_transpose_mul_self Z]
  exact LinearMap.mem_range

/-- The Gram certificate, row-space form (Claim 11, last equivalence). -/
theorem gram_certificate {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
    (Z : Matrix m k ℝ) (e0 : k → ℝ) :
    e0 ∈ Q1Subspace.rowSpace Z ↔
      ∃ x : k → ℝ, (Matrix.transpose Z * Z) *ᵥ x = e0 := by
  rw [rowSpace_eq_range_transpose, mem_range_transpose_iff_exists_gram]

end Q1Paper.PaperI
