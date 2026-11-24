import Q1Paper.Q1Projection

/-!
# The dimensional half of tightness

For `W₀ ≤ W ≤ F × F` with `pi2 W ≤ pi1 W`, the span of the two projections of `W₀`
satisfies `dim (pi1 W₀ ⊔ pi2 W₀) ≤ dim (pi1 W)`, and in particular `dim (pi1 W₀) ≤ dim (pi1 W)`.
With `U₀ = pi1 W₀`, `V₀ = pi2 W₀` and `ω = dim (pi1 W)` these say `rank [U₀; V₀] ≤ ω` and
`dim U₀ ≤ ω`.  The first is exactly the dimension half of the paper's lower bound
`q_min ≥ ω + 1` on the minimum order; the (already formalised) other half is `ω + 1 ≤ dim W`.
-/

namespace Q1Subspace

open Module

variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- **Dimensional half of tightness.** If `W₀ ≤ W` and `pi2 W ≤ pi1 W`, then the span of
the two projections of `W₀` still has dimension at most `dim (pi1 W)`.  Both projections of
`W₀` land in `pi1 W`: the first by monotonicity of `pi1`, the second because
`pi2 W₀ ≤ pi2 W ≤ pi1 W`. -/
theorem finrank_sup_pi_le [FiniteDimensional K F] {W₀ W : Submodule K (F × F)}
    (h : W₀ ≤ W) (hle : pi2 W ≤ pi1 W) :
    finrank K ↥(pi1 W₀ ⊔ pi2 W₀) ≤ finrank K ↥(pi1 W) := by
  have h₁ : pi1 W₀ ≤ pi1 W := Submodule.map_mono h
  have h₂ : pi2 W₀ ≤ pi1 W := (Submodule.map_mono h).trans hle
  exact Submodule.finrank_mono (sup_le h₁ h₂)

/-- Monotonicity of the first projection's dimension in the subspace. -/
theorem finrank_pi1_mono [FiniteDimensional K F] {W₀ W : Submodule K (F × F)}
    (h : W₀ ≤ W) :
    finrank K ↥(pi1 W₀) ≤ finrank K ↥(pi1 W) :=
  Submodule.finrank_mono (Submodule.map_mono h)

end Q1Subspace
