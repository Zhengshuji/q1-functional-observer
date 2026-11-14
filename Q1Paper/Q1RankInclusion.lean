import Mathlib

/-!
# Rank additivity versus inclusion

The step of the paper that turns the algebraic condition into a row-space inclusion:

  `rank [H_A; H] = rank H  ⟺  row H_A ⊆ row H`.

At the level of subspaces this is

  `finrank (S ⊔ T) = finrank S  ⟺  T ≤ S`,

proved here in general form.  The forward direction uses the dimension formula
`dim (S ⊔ T) + dim (S ⊓ T) = dim S + dim T`: the rank equality forces `dim T = dim (S ⊓ T)`,
hence `T = S ⊓ T ≤ S`.
-/

namespace Q1Subspace

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- `finrank (S ⊔ T) = finrank S` if and only if `T ≤ S`. -/
theorem finrank_sup_eq_iff_le [FiniteDimensional K E] (S T : Submodule K E) :
    finrank K ↥(S ⊔ T) = finrank K ↥S ↔ T ≤ S := by
  constructor
  · intro h
    have hdim : finrank K ↥(S ⊔ T) + finrank K ↥(S ⊓ T) =
        finrank K ↥S + finrank K ↥T :=
      Submodule.finrank_sup_add_finrank_inf_eq S T
    have hinf : finrank K ↥(S ⊓ T) ≤ finrank K ↥T := Submodule.finrank_mono inf_le_right
    have hTeq : finrank K ↥T = finrank K ↥(S ⊓ T) := by omega
    have hST : S ⊓ T = T := Submodule.eq_of_le_of_finrank_eq inf_le_right hTeq.symm
    rw [← hST]
    exact inf_le_left
  · intro h
    exact congrArg (fun X : Submodule K E => finrank K ↥X) (sup_eq_left.mpr h)

/-- Contrapositive form: a strict rank drop is exactly a failure of inclusion. -/
theorem finrank_sup_eq_iff_not_le [FiniteDimensional K E] (S T : Submodule K E) :
    finrank K ↥(S ⊔ T) ≠ finrank K ↥S ↔ ¬ T ≤ S := by
  constructor
  · intro h hle
    exact h ((finrank_sup_eq_iff_le S T).mpr hle)
  · intro h heq
    exact h ((finrank_sup_eq_iff_le S T).mp heq)

end Q1Subspace
