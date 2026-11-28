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

/-- **Theorem 17 (dimension step).** If `T` is one-dimensional and `T ⊓ U` is nonzero, then
`T ≤ U`: with `t = 1` and `a = dim (U ∩ T) ≥ 1` the whole of `T` sits inside `U`, which is what turns
compatibility into invariance. -/
theorem le_of_finrank_eq_one {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]
    {T U : Submodule K E} (hT : Module.finrank K ↥T = 1) (h : T ⊓ U ≠ ⊥) : T ≤ U := by
  have hfinT : Module.Finite K ↥T :=
    Module.finite_of_finrank_pos (by rw [hT]; exact Nat.zero_lt_one)
  have hfinInf : Module.Finite K ↥(T ⊓ U) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left)
      (Submodule.inclusion_injective inf_le_left)
  have hpos : 0 < Module.finrank K ↥(T ⊓ U) := by
    have hlt : (⊥ : Submodule K E) < T ⊓ U := bot_lt_iff_ne_bot.mpr h
    simpa using Submodule.finrank_lt_finrank_of_lt hlt
  have hle : T ⊓ U ≤ T := inf_le_left
  have hmono : Module.finrank K ↥(T ⊓ U) ≤ Module.finrank K ↥T :=
    Submodule.finrank_mono hle
  have hfin : Module.finrank K ↥(T ⊓ U) = 1 := by
    rw [hT] at hmono
    omega
  have hEq : T ⊓ U = T := Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hT])
  rw [← hEq]
  exact inf_le_right


end Q1Paper.PaperV
