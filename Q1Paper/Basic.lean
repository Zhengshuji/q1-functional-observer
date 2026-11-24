
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Prod

/-!
Q1Paper/Basic.lean

Abstract linear-algebra core for the paper.
The file is intentionally independent of the old MyProof project.
-/


set_option linter.unusedSectionVars false

open Module LinearMap

namespace Q1Paper

variable {K E F : Type*}
  [Field K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The pair map `x ↦ (f x, g x)`, the abstract form of stacking two
linear maps. -/
def pairMap (f g : E →ₗ[K] F) : E →ₗ[K] F × F :=
  f.prod g

@[simp]
theorem pairMap_apply (f g : E →ₗ[K] F) (x : E) :
    pairMap f g x = (f x, g x) := rfl

/-- The kernel of the pair map is the intersection of the two kernels. -/
theorem ker_pairMap (f g : E →ₗ[K] F) :
    LinearMap.ker (pairMap f g) = LinearMap.ker f ⊓ LinearMap.ker g := by
  ext x
  simp [pairMap, LinearMap.mem_ker]

/-- Rank-nullity for the pair map: the rank of the stacked pair is the
dimension of the source minus the dimension of the common kernel. -/
theorem finrank_range_pairMap (f g : E →ₗ[K] F) :
    finrank K (LinearMap.range (pairMap f g)) =
      finrank K E - finrank K (LinearMap.ker (pairMap f g)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (pairMap f g)
  omega


/-- The common kernel of two maps. -/
def commonKer (f g : E →ₗ[K] F) : Submodule K E :=
  LinearMap.ker f ⊓ LinearMap.ker g

/-- The common-kernel form of the rank-nullity statement for the pair map. -/
theorem finrank_range_pairMap_common (f g : E →ₗ[K] F) :
    finrank K (LinearMap.range (pairMap f g)) =
      finrank K E - finrank K (commonKer f g) := by
  rw [show commonKer f g = LinearMap.ker (pairMap f g) by
    rw [commonKer, ker_pairMap]]
  exact finrank_range_pairMap f g

end Q1Paper
