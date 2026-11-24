
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Q1Paper/RankConsistency.lean

Lemma C, structural core: consistency of a linear system is membership of
the right-hand side in the range; equivalently the span of the right-hand
side is contained in the range.  The Gram/rank formulation is recorded in
the paper (and checked by c311); this file isolates the subspace form.
-/


open Module LinearMap

namespace Q1Paper

variable {K E F : Type*}
  [Field K]
  [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

/-- Consistency of `T b = c` is membership of `c` in the range of `T`; this is the
definition of the range. -/
theorem exists_solution_iff_mem_range (T : E →ₗ[K] F) (c : F) :
    (∃ b : E, T b = c) ↔ c ∈ LinearMap.range T :=
  LinearMap.mem_range.symm

/-- Consistency is equivalent to the span of `c` being contained in the range of
`T`; the span of a singleton is contained in a submodule exactly when its
element is (`Submodule.span_singleton_le_iff_mem`). -/
theorem exists_solution_iff_span_le_range (T : E →ₗ[K] F) (c : F) :
    (∃ b : E, T b = c) ↔ Submodule.span K ({c} : Set F) ≤ LinearMap.range T := by
  rw [Submodule.span_singleton_le_iff_mem]
  exact LinearMap.mem_range.symm

/-- Consistency is equivalent to the range being unchanged after adjoining the
span of the right-hand side (`sup_eq_left`). -/
theorem exists_solution_iff_range_eq_sup_span (T : E →ₗ[K] F) (c : F) :
    (∃ b : E, T b = c) ↔
      LinearMap.range T = LinearMap.range T ⊔ Submodule.span K ({c} : Set F) := by
  rw [eq_comm, sup_eq_left, Submodule.span_singleton_le_iff_mem]
  exact LinearMap.mem_range.symm

end Q1Paper
