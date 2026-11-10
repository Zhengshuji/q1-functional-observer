/-
Q1Paper/RankConsistency.lean

Lemma C, structural core: consistency of a linear system is membership of
the right-hand side in the range; equivalently the span of the right-hand
side is contained in the range.  The Gram/rank formulation is recorded in
the paper (and checked by c311); this file isolates the subspace form.
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Module LinearMap

namespace Q1Paper

variable {K E F : Type*}
  [Field K]
  [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

/-- Consistency of `T b = c` is membership of `c` in the range of `T`. -/
theorem exists_solution_iff_mem_range (T : E →ₗ[K] F) (c : F) :
    (∃ b : E, T b = c) ↔ c ∈ LinearMap.range T := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, rfl⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, hb⟩

/-- Consistency is equivalent to the span of `c` being contained in the
range of `T`. -/
theorem exists_solution_iff_span_le_range (T : E →ₗ[K] F) (c : F) :
    (∃ b : E, T b = c) ↔ Submodule.span K ({c} : Set F) ≤ LinearMap.range T := by
  constructor
  · intro h
    exact (Submodule.span_le).2 (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact (exists_solution_iff_mem_range T c).mp h)
  · intro h
    have hc : c ∈ LinearMap.range T :=
      h (Submodule.subset_span (by simp : c ∈ ({c} : Set F)))
    exact (exists_solution_iff_mem_range T c).mpr hc

/-- Consistency is equivalent to the range being unchanged after adjoining
the span of the right-hand side. -/
theorem exists_solution_iff_range_eq_sup_span (T : E →ₗ[K] F) (c : F) :
    (∃ b : E, T b = c) ↔
      LinearMap.range T = LinearMap.range T ⊔ Submodule.span K ({c} : Set F) := by
  constructor
  · intro h
    symm
    exact sup_eq_left.mpr ((exists_solution_iff_span_le_range T c).mp h)
  · intro h
    apply (exists_solution_iff_span_le_range T c).mpr
    rw [h]
    exact le_sup_right

end Q1Paper
