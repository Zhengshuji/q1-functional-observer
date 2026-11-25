import Mathlib

/-!
# Constant rank of a linear pencil `z • H - H_A`

Interface for the spectral condition of the paper.  **The two blocks are
independent**: `H = L N` and `H_A = L A N` are blocks of `[L A; L] N`, and in
general `H_A ≠ H * A`, because `K_0 = ker[C; CA]` need not be invariant under
`A` (from `C x = 0` and `C A x = 0` one does not get `C A² x = 0`).  So the
pencil here is `z • H - H_A` with `H_A` an independent matrix.

Two equivalent ways of saying that its rank does not depend on `z`:

* `HasConstantRank H H_A` : `∃ r, ∀ z, rank (z • H - H_A) = r`;
* `RankIndependentOfScalar H H_A` : `∀ z w, rank (z • H - H_A) = rank (w • H - H_A)`.

The paper's condition fixes the value, `rank (z • H - H_A) = rank H`; that is
`SpectralCondition` below, and it implies constant rank with `r = rank H`.

Note the quantifier order in any minor-based reformulation: `∀ z, ∃ I J, det ≠ 0`
is what rank `ω` means; `∃ I J, ∀ z, det ≠ 0` is strictly stronger.
-/

namespace Q1Subspace

open Module

variable {K : Type*} [Field K]
  {m n : Type*} [Fintype m] [Fintype n]

/-- The rank of a matrix, as the dimension of the range of its column map. -/
noncomputable def matrixRank (M : Matrix m n K) : ℕ :=
  finrank K ↥(LinearMap.range (Matrix.mulVecLin M))

/-- The rank of the pencil `z • H - H_A` is independent of `z`. -/
def HasConstantRank (H H_A : Matrix m n K) : Prop :=
  ∃ r : ℕ, ∀ z : K, matrixRank (z • H - H_A) = r

/-- Pointwise form: any two values of the pencil have the same rank. -/
def RankIndependentOfScalar (H H_A : Matrix m n K) : Prop :=
  ∀ z w : K, matrixRank (z • H - H_A) = matrixRank (w • H - H_A)

/-- The spectral condition of the paper: the rank is constantly `rank H`. -/
def SpectralCondition (H H_A : Matrix m n K) : Prop :=
  ∀ z : K, matrixRank (z • H - H_A) = matrixRank H

/-- The two forms of constant rank are equivalent. -/
theorem hasConstantRank_iff_rankIndependent (H H_A : Matrix m n K) :
    HasConstantRank H H_A ↔ RankIndependentOfScalar H H_A := by
  constructor
  · rintro ⟨r, hr⟩ z w
    rw [hr z, hr w]
  · intro h
    exact ⟨matrixRank ((0 : K) • H - H_A), fun z => h z 0⟩

/-- The paper's condition is the special case `r = rank H`. -/
theorem spectralCondition_hasConstantRank (H H_A : Matrix m n K)
    (h : SpectralCondition H H_A) : HasConstantRank H H_A :=
  ⟨matrixRank H, h⟩

/-- At `z = 0` the pencil is `-H_A`, so the spectral condition gives
`rank H_A = rank H`.  This is the step that turns the algebraic inclusion
`row H_A ⊆ row H` into the equality `row H_A = row H`. -/
theorem spectralCondition_zero (H H_A : Matrix m n K)
    (h : SpectralCondition H H_A) : matrixRank ((0 : K) • H - H_A) = matrixRank H :=
  h 0

/-- Definitional unfolding at `z = 0`. -/
theorem spectralCondition_zero_eq_zero (H H_A : Matrix m n K) :
    ((0 : K) • H - H_A) = -H_A := by
  simp

end Q1Subspace
