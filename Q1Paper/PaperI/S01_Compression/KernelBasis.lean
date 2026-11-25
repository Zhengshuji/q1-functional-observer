import Mathlib

/-!
Q1Paper/PaperI/S01_Compression/KernelBasis.lean

**A basis matrix for a submodule / kernel, over an arbitrary field.**

`Q1Paper/PaperI/T5DecC.lean` (and `Theorem5.lean`) take as an abstract hypothesis a
matrix `N` whose columns are a basis of `ker [CA; C]`:

  `(hN : N.mulVecLin.range = (Matrix.fromRows (C * A) C).mulVecLin.ker)` and
  `(hNk : N.rank = k)`.

This file *constructs* such an `N`, so the hypothesis is no longer needed.

Main results:

* `exists_basis_matrix_of_submodule` (general, any field `K`): every submodule `W` of
  `Fin n → K` is the range of an `n × finrank W` matrix `N` of full column rank.

* `exists_kernel_basis_matrix` (the `ℝ` instantiation for Theorem 5): for every
  `C : Matrix (Fin p) (Fin n) ℝ`, `A : Matrix (Fin n) (Fin n) ℝ` there are `k` and
  `N : Matrix (Fin n) (Fin k) ℝ` with `k = finrank ker [CA; C]`, `N.rank = k` and
  `N.mulVecLin.range = ker [CA; C]`.

* `exists_kernel_basis_matrix_of_finrank`: the same with a caller-chosen index size `k`
  and a proof `k = finrank ker [CA; C]`; this is the shape that lets a caller of
  `DECℂ_iff_exists_compressed` / `DECℂ_iff_exists_encodes` replace `hN`/`hNk`.

Route: take the `Module.finBasis` of `W`, use its vectors as the columns of `N`
(`Matrix.mulVecLin` is exactly `Matrix.mulVec`), and compare the range with `W` by
double inclusion; the reverse inclusion is `Basis.sum_repr`.  The rank statement is
the definition `Matrix.rank A = finrank R (range A.mulVecLin)`.
-/


open Module

namespace Q1Paper

/-- **Every submodule of a coordinate space is the range of a full-column-rank matrix.**

For a submodule `W` of `Fin n → K`, there is an `n × finrank W` matrix `N` whose
columns are a basis of `W`: its rank is `finrank W` and its `mulVecLin` range is `W`. -/
theorem exists_basis_matrix_of_submodule
    {K : Type*} [Field K] {n : ℕ}
    (W : Submodule K (Fin n → K)) :
    ∃ N : Matrix (Fin n) (Fin (Module.finrank K W)) K,
      Matrix.rank N = Module.finrank K W ∧ N.mulVecLin.range = W := by
  classical
  let b := Module.finBasis K W
  let N : Matrix (Fin n) (Fin (Module.finrank K W)) K :=
    fun i j => (b j : Fin n → K) i
  -- `N *ᵥ v` is the linear combination of the basis vectors with coefficients `v`.
  have hmul : ∀ v : Fin (Module.finrank K W) → K,
      N.mulVecLin v = ∑ j, v j • (b j : Fin n → K) := by
    intro v
    rw [Matrix.mulVecLin_apply]
    funext i
    simp only [Matrix.mulVec, dotProduct, N, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  -- `range N ⊆ W`: a linear combination of basis vectors of `W` lies in `W`.
  have hle : N.mulVecLin.range ≤ W := by
    rintro x ⟨v, rfl⟩
    rw [hmul v]
    exact Submodule.sum_mem W (fun j _ => Submodule.smul_mem W (v j) (b j).2)
  -- `W ⊆ range N`: expand `x ∈ W` in the basis.
  have hge : W ≤ N.mulVecLin.range := by
    intro x hx
    refine ⟨fun j => b.repr ⟨x, hx⟩ j, ?_⟩
    rw [hmul]
    -- Expand `x ∈ W` in the basis and push the subtype coercion through the sum.
    have h := congrArg (fun w : W => (w : Fin n → K)) (b.sum_repr ⟨x, hx⟩)
    rw [Submodule.coe_sum] at h
    simpa only [Submodule.coe_smul, Subtype.coe_mk] using h
  have hrange : N.mulVecLin.range = W := le_antisymm hle hge
  refine ⟨N, ?_, hrange⟩
  -- `Matrix.rank N = finrank K (range N) = finrank K W`.
  change Module.finrank K ↥(LinearMap.range N.mulVecLin) = Module.finrank K W
  rw [hrange]

/-- **A basis matrix of `ker [CA; C]` over `ℝ`.**

Given `C : Matrix (Fin p) (Fin n) ℝ` and `A : Matrix (Fin n) (Fin n) ℝ`, there exist
`k : ℕ` and `N : Matrix (Fin n) (Fin k) ℝ` whose columns are a basis of `ker [CA; C]`:
`k` is the dimension of the kernel, `N.rank = k`, and the range of `N.mulVecLin` is
exactly the kernel.  This removes the hypotheses `hN`, `hNk` of
`Q1Paper/PaperI/T5DecC.lean`. -/
theorem exists_kernel_basis_matrix
    {p n : ℕ} (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ (k : ℕ) (N : Matrix (Fin n) (Fin k) ℝ),
      k = Module.finrank ℝ ((Matrix.fromRows (C * A) C).mulVecLin.ker) ∧
      N.rank = k ∧ N.mulVecLin.range = (Matrix.fromRows (C * A) C).mulVecLin.ker := by
  classical
  obtain ⟨N, hrank, hrange⟩ :=
    exists_basis_matrix_of_submodule (K := ℝ)
      ((Matrix.fromRows (C * A) C).mulVecLin.ker)
  exact ⟨Module.finrank ℝ ((Matrix.fromRows (C * A) C).mulVecLin.ker), N, rfl, hrank, hrange⟩

/-- **The hypothesis shape of `T5DecC.lean`, with a caller-chosen index size `k`.**

If the caller has already fixed a natural number `k` together with a proof that it is
the dimension of `ker [CA; C]`, this produces `N : Matrix (Fin n) (Fin k) ℝ` with
`N.rank = k` and `N.mulVecLin.range = ker [CA; C]`.  A caller who currently passes
`(hN : N.mulVecLin.range = ...)` and `(hNk : N.rank = k)` can obtain this `N` from
`exists_kernel_basis_matrix_of_finrank` and then apply the existing theorems; no
abstract basis hypothesis is needed.

(Note: `N.rank = k` together with `N.mulVecLin.range = K` forces `k = finrank K`, so
the equality hypothesis `hk` cannot be dropped while keeping a fixed `k`.) -/
theorem exists_kernel_basis_matrix_of_finrank
    {p n k : ℕ} (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hk : k = Module.finrank ℝ ((Matrix.fromRows (C * A) C).mulVecLin.ker)) :
    ∃ N : Matrix (Fin n) (Fin k) ℝ,
      N.rank = k ∧ N.mulVecLin.range = (Matrix.fromRows (C * A) C).mulVecLin.ker := by
  classical
  subst hk
  obtain ⟨N, hrank, hrange⟩ :=
    exists_basis_matrix_of_submodule (K := ℝ)
      ((Matrix.fromRows (C * A) C).mulVecLin.ker)
  exact ⟨N, hrank, hrange⟩


end Q1Paper
