import Mathlib
import Q1Paper.RowSpaceAlgebraic
import Q1Paper.SubspaceQuotient
import Q1Paper.PaperI.S01_Compression.CompressionMatrix

/-!
# The `rank [A; b] = rank A` solvability criterion for one right-hand side

Mathlib has `Matrix.mulVec_surjective_iff_rank_eq_card` (surjectivity of `x ↦ A x`), but no
criterion for a *single* right-hand side.  This file supplies it, reducing everything to the
project's row-space bridge `Q1Subspace.rank_fromRows_eq_rank_iff`
(`Q1Paper/RowSpaceAlgebraic.lean`), i.e. `rank [A; B] = rank B ↔ rowSpace A ≤ rowSpace B`.

## The shape of the statement (why the transpose appears)

`Matrix.fromRows` stacks two blocks sharing the **column** index, so `b : Fin m → K` cannot be a
row block of `A : Matrix (Fin m) (Fin n) K` (the literal `fromRows A (fun _ => b)` is ill-typed:
its columns would have index `Fin m` while `A` has `Fin n`).  The augmented matrix of the system
`A x = b` is the *column* augmentation `[A b]`, whose transpose is a row augmentation of `Aᵀ`:

  `[A b]ᵀ = fromRows Aᵀ (fun _ : PUnit => b)`,  and `rank [A b] = rank (fromRows Aᵀ b)`.

So the criterion below — `rank (fromRows Aᵀ (fun _ => b)) = rank A` — **is** `rank [A b] = rank A`.

## Main results

* `exists_mulVec_eq_iff_mem_rowSpace` : solvable ↔ `b ∈ rowSpace Aᵀ` (column space of `A`);
* `exists_mulVec_eq_iff_rank_fromRows` : solvable ↔ `rank [A b] = rank A`;
* `rank_fromRows_eq_rank_iff_mem` : `rank [A b] = rank A` ↔ `b ∈ rowSpace Aᵀ`;
* `not_exists_mulVec_iff_rank_lt` : infeasible ↔ `rank A < rank [A b]`.
-/

namespace Q1Subspace

open Module

variable {K : Type*} [Field K]

/-! ### Two blocks: the order of the blocks does not change the rank -/

section Blocks

variable {m n m₁ m₂ : Type*} [Fintype m] [Fintype n] [Fintype m₁] [Fintype m₂]

/-! The block-swap identity `rank [A; B] = rank [B; A]` already exists in the project as
`Q1Paper.PaperI.rank_fromRows_comm` (`Q1Paper/PaperI/CompressionMatrix.lean`); it is reused
below instead of being reproved. -/

/-- Stacking a block on top cannot lower the rank of the lower block. -/
theorem rank_le_rank_fromRows_right (A : Matrix m₁ n K) (B : Matrix m₂ n K) :
    Matrix.rank B ≤ Matrix.rank (Matrix.fromRows A B) := by
  rw [rank_eq_finrank_rowSpace, rank_eq_finrank_rowSpace, rowSpace_fromRows]
  exact Submodule.finrank_mono le_sup_right

omit [Fintype m] in
/-- `x ᵥ* Aᵀ = A *ᵥ x`: row multiplication by the transpose is column multiplication. -/
theorem vecMul_transpose_eq_mulVec (A : Matrix m n K) (x : n → K) :
    Matrix.vecMul x A.transpose = A.mulVec x := by
  funext i
  simp only [Matrix.vecMul, Matrix.mulVec, Matrix.transpose_apply]
  exact dotProduct_comm _ _

end Blocks

/-! ### A single right-hand side -/

section Single

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Solvability is membership in the column space**: `A x = b` is solvable exactly when `b`
lies in the row space of `Aᵀ`, i.e. in the span of the columns of `A`. -/
theorem exists_mulVec_eq_iff_mem_rowSpace (A : Matrix m n K) (b : m → K) :
    (∃ x : n → K, A.mulVec x = b) ↔ b ∈ rowSpace A.transpose := by
  have h := mem_rowSpan_iff_exists_vecMul (M := A.transpose) (w := b)
  rw [show rowSpan A.transpose = rowSpace A.transpose from rfl] at h
  simpa only [vecMul_transpose_eq_mulVec] using h.symm

/-- **The rank criterion for a single right-hand side**: `A x = b` is solvable exactly when the
augmented matrix `[A  b]` has the same rank as `A` (stated as `rank (fromRows Aᵀ b) = rank A`,
which is `rank [A b] = rank A` since `[A b]ᵀ = fromRows Aᵀ b`). -/
theorem exists_mulVec_eq_iff_rank_fromRows (A : Matrix m n K) (b : m → K) :
    (∃ x : n → K, A.mulVec x = b) ↔
      (Matrix.fromRows A.transpose (fun _ : PUnit => b)).rank = A.rank := by
  have h1 : (Matrix.fromRows A.transpose (fun _ : PUnit => b)).rank = A.rank
      ↔ (Matrix.fromRows (fun _ : PUnit => b) A.transpose).rank = A.rank := by
    rw [Q1Paper.PaperI.rank_fromRows_comm (A := A.transpose) (B := fun _ : PUnit => b)]
  have h2 : (Matrix.fromRows (fun _ : PUnit => b) A.transpose).rank = A.rank
      ↔ rowSpace (fun _ : PUnit => b) ≤ rowSpace A.transpose := by
    rw [← Matrix.rank_transpose (A := A)]
    exact rank_fromRows_eq_rank_iff (fun _ : PUnit => b) A.transpose
  have h3 : rowSpace (fun _ : PUnit => b) ≤ rowSpace A.transpose
      ↔ b ∈ rowSpace A.transpose := by
    constructor
    · intro hle
      exact hle (Submodule.subset_span ⟨PUnit.unit, rfl⟩)
    · intro hb
      simp only [rowSpace]
      exact Submodule.span_le.mpr (by rintro w ⟨i, rfl⟩; exact hb)
  exact (exists_mulVec_eq_iff_mem_rowSpace A b).trans (h3.symm.trans (h2.symm.trans h1.symm))

/-- **The rank criterion as a membership test**, matching
`Q1Subspace.mem_rowSpan_iff_exists_vecMul`. -/
theorem rank_fromRows_eq_rank_iff_mem (A : Matrix m n K) (b : m → K) :
    (Matrix.fromRows A.transpose (fun _ : PUnit => b)).rank = A.rank
      ↔ b ∈ rowSpace A.transpose :=
  (exists_mulVec_eq_iff_rank_fromRows A b).symm.trans
    (exists_mulVec_eq_iff_mem_rowSpace A b)

/-- **Infeasibility form**: the system is unsolvable exactly when adjoining `b` strictly raises
the rank.  (The inequality `rank A ≤ rank [A b]` is automatic; the content is that it is strict
precisely in the infeasible case.) -/
theorem not_exists_mulVec_iff_rank_lt (A : Matrix m n K) (b : m → K) :
    (¬ ∃ x : n → K, A.mulVec x = b) ↔
      A.rank < (Matrix.fromRows A.transpose (fun _ : PUnit => b)).rank := by
  have hmono : A.rank ≤ (Matrix.fromRows A.transpose (fun _ : PUnit => b)).rank := by
    have h1 : Matrix.rank A.transpose
        ≤ Matrix.rank (Matrix.fromRows (fun _ : PUnit => b) A.transpose) :=
      rank_le_rank_fromRows_right (fun _ : PUnit => b) A.transpose
    have h2 := Q1Paper.PaperI.rank_fromRows_comm (A := A.transpose) (B := fun _ : PUnit => b)
    rw [Matrix.rank_transpose (A := A)] at h1
    rw [← h2] at h1
    exact h1
  constructor
  · intro hno
    refine lt_of_le_of_ne hmono ?_
    intro heq
    exact hno ((exists_mulVec_eq_iff_rank_fromRows A b).mpr heq.symm)
  · intro hlt hex
    exact absurd ((exists_mulVec_eq_iff_rank_fromRows A b).mp hex).symm (ne_of_lt hlt)

end Single

end Q1Subspace
