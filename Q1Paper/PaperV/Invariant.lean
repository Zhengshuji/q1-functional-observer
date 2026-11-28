import Mathlib

/-!
Q1Paper/PaperV/Invariant.lean

§V, Theorem 17 — the structure step: **when `T ≤ U` and `Z''` maps `U` into `U + T`, it maps
`U` into `U`**, i.e. `U` is `Z''`-invariant.

Paper statement used in Theorem 17: for `t = 1` and `a = dim(U ∩ T) ≥ 1` one has
`T ⊆ U`, hence `U + T = U` and compatibility `U Z'' ⊆ U + T` reads `U Z'' ⊆ U` — invariance.
The content is that `a ≥ 1` with `t = 1` gives `T ⊆ U` (since `U ∩ T ≠ 0` inside a line), and
then the compatibility condition collapses.  This file records the collapse.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

namespace Q1Paper.PaperV

/-- **Theorem 17's structure step.** If `T ≤ U` and `Z` maps `U` into `U ⊔ T`, then `Z` maps
`U` into `U`; with `U ⊔ T = U` the compatibility condition *is* invariance. -/
theorem map_mem_of_le_sup {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]
    (T U : Submodule K E) (Z : E →ₗ[K] E) (hTU : T ≤ U)
    (hc : ∀ u ∈ U, Z u ∈ U ⊔ T) : ∀ u ∈ U, Z u ∈ U := by
  have h : U ⊔ T = U := sup_eq_left.mpr hTU
  simpa [h] using hc

/-- The pointwise form used in the paper: invariance is exactly compatibility when `T ≤ U`. -/
theorem invariant_iff_compat_of_le {K : Type*} [Field K] {E : Type*} [AddCommGroup E]
    [Module K E] (T U : Submodule K E) (Z : E →ₗ[K] E) (hTU : T ≤ U) :
    (∀ u ∈ U, Z u ∈ U) ↔ (∀ u ∈ U, Z u ∈ U ⊔ T) := by
  have h : U ⊔ T = U := sup_eq_left.mpr hTU
  constructor
  · intro hinv u hu
    rw [h]
    exact hinv u hu
  · intro hc u hu
    rw [h] at hc
    exact hc u hu

end Q1Paper.PaperV
