
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Rank
import Q1Paper.RankIdentity

/-!
Q1Paper/G4RankIdentity.lean

Item 1 of the expert reply: the matrix-level rank identity

  rank [P; M] = rank P + rank (M N),

for `N` a basis matrix of `ker P`.  Both halves are matrix adaptations of the abstract
identity `finrank_range_prod`.

Key API used (all verified in the pinned version):
`Matrix.rank_eq_finrank_span_*`, `Matrix.mulVecLin_mul`, `Matrix.fromRows_apply_inl/inr`,
`LinearEquiv.finrank_map_eq`, `LinearMap.range_comp`.
-/


open Matrix

namespace Q1Paper

variable {K : Type*} [Field K]

/-- `(α ⊕ β → K) ≃ₗ[K] (α → K) × (β → K)`. -/
noncomputable def sumArrowEquivProd (α β : Type*) :
    ((α ⊕ β) → K) ≃ₗ[K] ((α → K) × (β → K)) where
  toFun v := (fun a => v (Sum.inl a), fun b => v (Sum.inr b))
  invFun x := Sum.elim x.1 x.2
  left_inv v := by funext i; cases i <;> rfl
  right_inv x := by rcases x with ⟨u, v⟩; rfl
  map_add' u v := by apply Prod.ext <;> funext i <;> rfl
  map_smul' c v := by apply Prod.ext <;> funext i <;> rfl

/-- `rank [P; M] = rank P + dim (M (ker P))`, the matrix form of the rank identity. -/
theorem rank_fromRows_add_map {m n p : ℕ}
    (P : Matrix (Fin m) (Fin n) K) (M : Matrix (Fin p) (Fin n) K) :
    (Matrix.fromRows P M).rank =
      P.rank + Module.finrank K ↥(Submodule.map M.mulVecLin P.mulVecLin.ker) := by
  classical
  let e := sumArrowEquivProd (K := K) (Fin m) (Fin p)
  have hpair :
      e.toLinearMap.comp (Matrix.fromRows P M).mulVecLin =
        P.mulVecLin.prod M.mulVecLin := by
    refine LinearMap.ext ?_
    intro v
    apply Prod.ext <;> funext i <;>
      simp [e, sumArrowEquivProd, Matrix.mulVecLin_apply, Matrix.fromRows_apply_inl,
        Matrix.fromRows_apply_inr, Matrix.mulVec]
  have hrange :
      (P.mulVecLin.prod M.mulVecLin).range =
        Submodule.map e.toLinearMap (Matrix.fromRows P M).mulVecLin.range := by
    rw [← hpair, LinearMap.range_comp]
  calc (Matrix.fromRows P M).rank
      = Module.finrank K ↥(Matrix.fromRows P M).mulVecLin.range := rfl
    _ = Module.finrank K ↥(P.mulVecLin.prod M.mulVecLin).range := by
        rw [hrange, LinearEquiv.finrank_map_eq]
    _ = P.rank + Module.finrank K ↥(Submodule.map M.mulVecLin P.mulVecLin.ker) := by
        simpa [Matrix.rank] using finrank_range_prod P.mulVecLin M.mulVecLin

/-- The range of `N` is the kernel of `P` when `N` is a basis matrix of `ker P`. -/
theorem mulVecLin_range_eq_ker {m n r : ℕ}
    (P : Matrix (Fin m) (Fin n) K) (N : Matrix (Fin n) (Fin r) K)
    (hN : ∀ v : Fin n → K, P.mulVec v = 0 ↔ ∃ w, N.mulVec w = v) :
    N.mulVecLin.range = P.mulVecLin.ker := by
  ext v
  simp only [LinearMap.mem_range, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  exact (hN v).symm

/-- The matrix rank identity: `rank [P; M] = rank P + rank (M N)` for `N` a basis matrix
of `ker P`. -/
theorem rank_vstack_add_rank_mul {m n p r : ℕ}
    (P : Matrix (Fin m) (Fin n) K) (M : Matrix (Fin p) (Fin n) K)
    (N : Matrix (Fin n) (Fin r) K)
    (hN : ∀ v : Fin n → K, P.mulVec v = 0 ↔ ∃ w, N.mulVec w = v) :
    (Matrix.fromRows P M).rank = P.rank + (M * N).rank := by
  rw [rank_fromRows_add_map]
  congr 1
  have hrange :
      (M * N).mulVecLin.range = Submodule.map M.mulVecLin P.mulVecLin.ker := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp, mulVecLin_range_eq_ker P N hN]
  have hrank : (M * N).rank = Module.finrank K ↥((M * N).mulVecLin.range) := rfl
  rw [hrank, hrange]

end Q1Paper
