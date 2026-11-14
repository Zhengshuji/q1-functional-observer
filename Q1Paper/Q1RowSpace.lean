import Mathlib
import Q1Paper.Q1RankInclusion

/-!
# Row spaces, and the matrix form of the algebraic condition

The paper's algebraic condition is `rank [H_A; H] = rank H`, and the paper turns
it into `row H_A ⊆ row H`.  This file supplies the bridge between the matrix rank
and the row space:

* `rowSpace M` : the span of the rows of `M`, a submodule of `n → K`;
* `rank_eq_finrank_rowSpace` : `M.rank = dim (rowSpace M)`;
* `rowSpace_fromRows` : `rowSpace [A; B] = rowSpace A ⊔ rowSpace B`;
* `rank_fromRows_eq_rank_iff` : `rank [A; B] = rank B ↔ rowSpace A ≤ rowSpace B`.
-/

namespace Q1Subspace

open Module

variable {K : Type*} [Field K]
  {m n m₁ m₂ : Type*} [Fintype m] [Fintype n] [Fintype m₁] [Fintype m₂]

/-- The row space of a matrix: the span of its rows. -/
def rowSpace (M : Matrix m n K) : Submodule K (n → K) :=
  Submodule.span K (Set.range (fun i : m => M i))

/-- The row space is the span of the columns of the transpose. -/
theorem rowSpace_eq_span_col_transpose (M : Matrix m n K) :
    rowSpace M = Submodule.span K (Set.range M.transpose.col) := by
  rw [rowSpace]
  rfl

/-- **The bridge**: the rank of a matrix is the dimension of its row space. -/
theorem rank_eq_finrank_rowSpace (M : Matrix m n K) :
    Matrix.rank M = finrank K ↥(rowSpace M) := by
  rw [rowSpace_eq_span_col_transpose, ← Matrix.rank_eq_finrank_span_cols M.transpose]
  exact (Matrix.rank_transpose M).symm

/-- Stacking two matrices adds their row spaces. -/
theorem rowSpace_fromRows (A : Matrix m₁ n K) (B : Matrix m₂ n K) :
    rowSpace (Matrix.fromRows A B) = rowSpace A ⊔ rowSpace B := by
  have hset : Set.range (fun i : m₁ ⊕ m₂ => Matrix.fromRows A B i) =
      Set.range A ∪ Set.range B := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | inl i => exact Or.inl ⟨i, rfl⟩
      | inr j => exact Or.inr ⟨j, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr j, rfl⟩
  rw [rowSpace, rowSpace, rowSpace, hset, Submodule.span_union]

/-- **The algebraic condition as an inclusion**: `rank [A; B] = rank B` holds
exactly when the row space of `A` is contained in that of `B`. -/
theorem rank_fromRows_eq_rank_iff (A : Matrix m₁ n K) (B : Matrix m₂ n K) :
    Matrix.rank (Matrix.fromRows A B) = Matrix.rank B ↔ rowSpace A ≤ rowSpace B := by
  rw [rank_eq_finrank_rowSpace, rank_eq_finrank_rowSpace, rowSpace_fromRows,
    sup_comm (rowSpace A) (rowSpace B)]
  exact finrank_sup_eq_iff_le (rowSpace B) (rowSpace A)

end Q1Subspace
