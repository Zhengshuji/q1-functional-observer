/-
Q1Paper/Monotone.lean

The rank-theoretic ingredient of the monotonicity of DEC in the order: appending
a row of zeros to a matrix leaves both its row space and its rank unchanged.
With this, adjoining a zero row to the free block R leaves the compressed blocks
H = LN and H_A = LAN the same up to zero rows, so neither (5a) nor (5b) changes
and DEC(q) implies DEC(q+1).

The remaining bookkeeping (carrying the two block equations through
`Matrix.fromRows`) is not done here.
-/

import Mathlib
import Q1Paper.Q1Subspace

open Module LinearMap

namespace Q1Paper

variable {K : Type*} [Field K]

/-- Appending rows of zeros does not change the row space. -/
theorem rowSpan_fromRows_zero {n m r : Type*} [Fintype n] [Fintype m] [Fintype r]
    (M : Matrix n m K) :
    Q1Subspace.rowSpan (Matrix.fromRows M (0 : Matrix r m K)) = Q1Subspace.rowSpan M := by
  apply le_antisymm
  · rw [Q1Subspace.rowSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl i => exact Submodule.subset_span ⟨i, rfl⟩
    | inr j =>
        show (0 : m → K) ∈ Q1Subspace.rowSpan M
        exact Submodule.zero_mem _
  · rw [Q1Subspace.rowSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl i, rfl⟩

/-- Appending rows of zeros does not change the rank. -/
theorem rank_fromRows_zero {n m r : Type*} [Fintype n] [Fintype m] [Fintype r]
    (M : Matrix n m K) :
    (Matrix.fromRows M (0 : Matrix r m K)).rank = M.rank := by
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
  change finrank K ↥(Q1Subspace.rowSpan (Matrix.fromRows M (0 : Matrix r m K)))
    = finrank K ↥(Q1Subspace.rowSpan M)
  rw [rowSpan_fromRows_zero]

end Q1Paper
