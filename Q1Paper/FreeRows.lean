
import Q1Paper.Basic
import Q1Paper.KappaObs

/-!
Q1Paper/FreeRows.lean

Lemma B, algebraic core: the space of free compressed row pairs is the
range of the pair map, and its dimension is the rank of [N; AN].
-/


set_option linter.unusedSectionVars false

open Module LinearMap

namespace Q1Paper

variable {K E F : Type*}
  [Field K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The space of possible compressed free-row pairs `(H_i, H_A_i)`. -/
def freePairSpace (f g : E →ₗ[K] F) : Submodule K (F × F) :=
  LinearMap.range (KappaObs.pairMap f g)

/-- Membership in the free-pair space is exactly being a pair image. -/
theorem mem_freePairSpace_iff (f g : E →ₗ[K] F) (y : F × F) :
    y ∈ freePairSpace f g ↔ ∃ x : E, (f x, g x) = y :=
  Iff.rfl

/-- The dimension of the free-pair space plus the common-kernel dimension is
the state dimension. -/
theorem finrank_freePairSpace_add_ker (f g : E →ₗ[K] F) :
    finrank K (freePairSpace f g)
        + finrank K ↥(LinearMap.ker f ⊓ LinearMap.ker g) = finrank K E := by
  rw [freePairSpace]
  have h := KappaObs.finrank_ker_inf_add_finrank_range_pairMap f g
  omega

/-- The effective dimension `kappa_obs = r * dim freePairSpace`. -/
theorem kappaObs_eq_mul_freePairSpace (r : ℕ) (f g : E →ₗ[K] F) :
    KappaObs.kappaObs r f g = r * finrank K (freePairSpace f g) :=
  rfl


/-- If `f` is injective (for example `f = N` with `N` a basis), then the
state dimension is at most the free-pair dimension. -/
theorem finrank_domain_le_freePairSpace (f g : E →ₗ[K] F)
    (hf : Function.Injective f) :
    finrank K E ≤ finrank K (freePairSpace f g) := by
  have hker : LinearMap.ker f = ⊥ := (LinearMap.ker_eq_bot).mpr hf
  have h := finrank_range_pairMap f g
  rw [ker_pairMap, hker, bot_inf_eq, finrank_bot, Nat.sub_zero] at h
  rw [freePairSpace]
  rw [← h]
  exact le_rfl


end Q1Paper
