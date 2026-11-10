/-
Q1Paper/HyperplaneAvoid.lean

The linear-algebra primitive behind the degree-bounded Bezout lemma of the paper:

over an infinite field, finitely many nonzero linear functionals cannot all vanish
on the same vector.  Equivalently, finitely many proper hyperplanes do not cover
the space.

This is the step that allows a second linear combination `G = Σ bᵢ fᵢ` to avoid all
roots of a first nonzero combination `F = Σ aᵢ fᵢ`.
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Module LinearMap

namespace Q1Paper

variable {K V ι : Type*} [Field K] [Infinite K]
  [AddCommGroup V] [Module K V]

/-- If `ℓ` is a nonzero functional, there is a vector on which it does not vanish. -/
theorem exists_apply_ne_zero {ℓ : V →ₗ[K] K} (h : ℓ ≠ 0) : ∃ y, ℓ y ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (LinearMap.ext fun y => by simpa using hc y)

/-- Finitely many nonzero linear functionals have a common nonvanishing point. -/
theorem exists_forall_apply_ne_zero (s : Finset ι) (ℓ : ι → V →ₗ[K] K)
    (h : ∀ i ∈ s, ℓ i ≠ 0) : ∃ x, ∀ i ∈ s, ℓ i x ≠ 0 := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
      have hmem : ∀ i ∈ s, ℓ i ≠ 0 := fun i hi => h i (Finset.mem_insert_of_mem hi)
      have ha' : ℓ a ≠ 0 := h a (Finset.mem_insert_self a s)
      obtain ⟨x, hx⟩ := ih hmem
      obtain ⟨y, hy⟩ := exists_apply_ne_zero ha'
      by_cases hxa : ℓ a x = 0
      · let bad : Finset K :=
          insert 0 ((s.filter (fun i => ℓ i y ≠ 0)).image
            (fun i => - (ℓ i x) / (ℓ i y)))
        obtain ⟨t, ht⟩ := Finset.exists_notMem bad
        have ht0 : t ≠ 0 := by
          intro h0
          exact ht (h0 ▸ Finset.mem_insert_self 0 _)
        refine ⟨x + t • y, ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | his
        · have hval : ℓ i (x + t • y) = t * ℓ i y := by
            simp [map_add, map_smul, hxa]
          rw [hval]
          exact mul_ne_zero ht0 hy
        · by_cases hiy : ℓ i y = 0
          · have hval : ℓ i (x + t • y) = ℓ i x := by
              simp [map_add, map_smul, hiy]
            rw [hval]
            exact hx i his
          · intro hzero
            have h1 : ℓ i x + t * ℓ i y = 0 := by
              simpa [map_add, map_smul] using hzero
            have h2 : t * ℓ i y = - (ℓ i x) := by
              rw [eq_neg_iff_add_eq_zero, add_comm]
              exact h1
            have hti : t = - (ℓ i x) / (ℓ i y) := by
              field_simp
              exact h2
            exact ht (Finset.mem_insert.mpr (Or.inr
              (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨his, hiy⟩, hti.symm⟩)))
      · refine ⟨x, ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | his
        · exact hxa
        · exact hx i his

end Q1Paper
