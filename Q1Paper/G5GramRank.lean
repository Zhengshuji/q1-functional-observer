/-
Q1Paper/G5GramRank.lean

Item 2 of the expert reply, first half: the augmented matrix `D = [M  c]` satisfies
`D Dᵀ = M Mᵀ + c cᵀ`.  With `Matrix.rank_self_mul_transpose` this reduces the rank-consistency
criterion to the augmented-matrix rank test of the second half.
-/

import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Q1Paper.RankConsistency

open Matrix

namespace Q1Paper

/-- The column vector `c` as an `m × 1` matrix. -/
def colMatrix {m : ℕ} (c : Fin m → ℝ) : Matrix (Fin m) (Fin 1) ℝ :=
  Matrix.vecMulVec c (fun _ : Fin 1 => (1 : ℝ))

/-- `M` with the column `c` appended. -/
def augment {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) :
    Matrix (Fin m) (Fin n ⊕ Fin 1) ℝ :=
  M.fromCols (colMatrix c)

/-- `c cᵀ` as a matrix product of the column with its transpose. -/
theorem colMatrix_mul_transpose {m : ℕ} (c : Fin m → ℝ) :
    colMatrix c * (colMatrix c)ᵀ = Matrix.vecMulVec (m := Fin m) (n := Fin m) c c := by
  ext i j
  simp [colMatrix, Matrix.mul_apply, Matrix.vecMulVec, Matrix.transpose_apply]

/-- The augmented matrix has the expected Gram matrix. -/
theorem augment_mul_transpose {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) :
    augment M c * (augment M c)ᵀ = M * Mᵀ + Matrix.vecMulVec (m := Fin m) (n := Fin m) c c := by
  rw [augment, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows,
    colMatrix_mul_transpose]



/-- Multiplication of the augmented matrix by a vector, split along the two column blocks. -/
theorem augment_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ)
    (u : Fin n → ℝ) (v : Fin 1 → ℝ) :
    (augment M c).mulVec (Sum.elim u v) = M.mulVec u + (colMatrix c).mulVec v := by
  rw [augment, Matrix.fromCols_mulVec]
  simp



/-- Multiplication by the appended column: `(c) v = v 0 • c`. -/
theorem colMatrix_mulVec {m : ℕ} (c : Fin m → ℝ) (v : Fin 1 → ℝ) :
    (colMatrix c).mulVec v = v 0 • c := by
  funext i
  show (∑ j : Fin 1, colMatrix c i j * v j) = v 0 * c i
  rw [Fin.sum_univ_one]
  simp [colMatrix, Matrix.vecMulVec, mul_comm]

/-- The linear-map form of the block formula for the augmented matrix. -/
theorem augment_mulVecLin {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ)
    (w : Fin n ⊕ Fin 1 → ℝ) :
    (augment M c).mulVecLin w
      = M.mulVecLin (fun j => w (Sum.inl j)) + w (Sum.inr 0) • c := by
  have hw : w = Sum.elim (fun j => w (Sum.inl j)) (fun k => w (Sum.inr k)) := by
    funext x
    cases x <;> rfl
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hw, augment_mulVec, colMatrix_mulVec]
  simp

/-- Adjoining a column does not change the rank iff the column is already in the range. -/
theorem rank_augment_eq_iff {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) :
    (augment M c).rank = M.rank ↔ c ∈ LinearMap.range M.mulVecLin := by
  constructor
  · intro h
    have hle : M.mulVecLin.range ≤ (augment M c).mulVecLin.range := by
      rintro _ ⟨u, rfl⟩
      refine ⟨Sum.elim u 0, ?_⟩
      rw [augment_mulVecLin]
      simp
    have hfin : Module.finrank ℝ ↥(M.mulVecLin.range)
        = Module.finrank ℝ ↥((augment M c).mulVecLin.range) := by
      simpa [Matrix.rank] using h.symm
    have heq : M.mulVecLin.range = (augment M c).mulVecLin.range :=
      Submodule.eq_of_le_of_finrank_eq hle hfin
    have hc : c ∈ (augment M c).mulVecLin.range := by
      refine ⟨Pi.single (Sum.inr 0) (1 : ℝ), ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
      ext i
      simp [augment, Matrix.col, Matrix.fromCols_apply_inr, colMatrix, Matrix.vecMulVec]
    rw [← heq] at hc
    exact hc
  · intro hc
    obtain ⟨b, hb⟩ := hc
    have hle : (augment M c).mulVecLin.range ≤ M.mulVecLin.range := by
      rintro _ ⟨w, rfl⟩
      rw [augment_mulVecLin, ← hb]
      refine ⟨fun j => w (Sum.inl j) + w (Sum.inr 0) * b j, ?_⟩
      have hsplit : (fun j => w (Sum.inl j) + w (Sum.inr 0) * b j)
          = (fun j => w (Sum.inl j)) + w (Sum.inr 0) • b := rfl
      rw [hsplit, map_add, map_smul]
    have hle' : M.mulVecLin.range ≤ (augment M c).mulVecLin.range := by
      rintro _ ⟨u, rfl⟩
      exact ⟨Sum.elim u 0, by rw [augment_mulVecLin]; simp⟩
    have heq : M.mulVecLin.range = (augment M c).mulVecLin.range := le_antisymm hle' hle
    rw [Matrix.rank, Matrix.rank, ← heq]

/-- Rank-consistency criterion (Lemma 4): `M b = c` is solvable iff the Gram ranks agree. -/
theorem exists_mulVec_eq_iff_rank_gram {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin m → ℝ) :
    (∃ b : Fin n → ℝ, M.mulVec b = c) ↔
      (M * Mᵀ).rank = (M * Mᵀ + Matrix.vecMulVec c c).rank := by
  have h1 : (M * Mᵀ).rank = M.rank := Matrix.rank_self_mul_transpose M
  have h2 : (M * Mᵀ + Matrix.vecMulVec c c).rank = (augment M c).rank := by
    rw [← augment_mul_transpose, Matrix.rank_self_mul_transpose]
  have hiff : M.rank = (augment M c).rank ↔ c ∈ LinearMap.range M.mulVecLin := by
    rw [eq_comm]
    exact rank_augment_eq_iff M c
  rw [h1, h2, hiff]
  exact (exists_solution_iff_mem_range M.mulVecLin c).symm

end Q1Paper
