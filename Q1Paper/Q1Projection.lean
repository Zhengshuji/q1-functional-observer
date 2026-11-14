import Mathlib

/-!
# Projections of a subspace of a product

For `W ≤ F × G` write `pi1 W` and `pi2 W` for the two projections.  The paper's
step "the algebraic condition plus the spectral condition at `λ = 0` force
`pi1 W = pi2 W`" is, at this level,

  `U₂ ≤ U₁` and `dim U₂ = dim U₁` imply `U₁ = U₂`,

since the algebraic condition gives `pi2 W ≤ pi1 W` and the spectral condition at
zero gives `dim (pi2 W) = dim (pi1 W)`.

Also recorded: `pi1` and `pi2` never increase the dimension, which is the first
half of the structural bound `dim W ≤ dim (pi1 W) + dim (pi2 W)`.
-/

namespace Q1Subspace

open Module

variable {K F G : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup G] [Module K G]

/-- The first projection of a subspace of a product. -/
def pi1 (W : Submodule K (F × G)) : Submodule K F :=
  W.map (LinearMap.fst K F G)

/-- The second projection of a subspace of a product. -/
def pi2 (W : Submodule K (F × G)) : Submodule K G :=
  W.map (LinearMap.snd K F G)

theorem mem_pi1 {W : Submodule K (F × G)} {x : F} :
    x ∈ pi1 W ↔ ∃ y : G, (x, y) ∈ W := by
  simp [pi1, Submodule.mem_map]

theorem mem_pi2 {W : Submodule K (F × G)} {y : G} :
    y ∈ pi2 W ↔ ∃ x : F, (x, y) ∈ W := by
  simp [pi2, Submodule.mem_map]

/-- Two submodules of the same dimension, one contained in the other, are equal. -/
theorem eq_of_le_of_finrank_eq {U₁ U₂ : Submodule K F} [FiniteDimensional K F]
    (h : U₂ ≤ U₁) (hdim : finrank K ↥U₂ = finrank K ↥U₁) : U₁ = U₂ :=
  (Submodule.eq_of_le_of_finrank_eq h hdim).symm

/-- **Step 3.** If the algebraic condition gives `pi2 W ≤ pi1 W` and the spectral
condition at `λ = 0` gives equal dimensions, then the two projections coincide. -/
theorem pi1_eq_pi2_of_le_of_finrank_eq {W : Submodule K (F × F)} [FiniteDimensional K F]
    (hle : pi2 W ≤ pi1 W) (hdim : finrank K ↥(pi2 W) = finrank K ↥(pi1 W)) :
    pi1 W = pi2 W :=
  eq_of_le_of_finrank_eq hle hdim


/-- The dimension of a subspace of a product is at most the sum of the dimensions
of its two projections: `W` embeds into `pi1 W × pi2 W`
(`Submodule.prodEquiv`). -/
theorem finrank_le_pi1_add_pi2 [FiniteDimensional K F] (W : Submodule K (F × F)) :
    finrank K ↥W ≤ finrank K ↥(pi1 W) + finrank K ↥(pi2 W) := by
  have hle : W ≤ (pi1 W).prod (pi2 W) := by
    rintro ⟨x, y⟩ hxy
    exact ⟨mem_pi1.mpr ⟨y, hxy⟩, mem_pi2.mpr ⟨x, hxy⟩⟩
  have hprod : finrank K ↥((pi1 W).prod (pi2 W))
      = finrank K ↥(pi1 W) + finrank K ↥(pi2 W) := by
    rw [← Module.finrank_prod]
    exact LinearEquiv.finrank_eq (Submodule.prodEquiv (pi1 W) (pi2 W))
  calc finrank K ↥W
      ≤ finrank K ↥((pi1 W).prod (pi2 W)) := Submodule.finrank_mono hle
    _ = finrank K ↥(pi1 W) + finrank K ↥(pi2 W) := hprod

/-- **Structural bound, upper half.** If the two projections of `W` coincide, then
`dim W ≤ 2 ω` with `ω` the common dimension. This is the half of
`ω + 1 ≤ dim W ≤ 2 ω` that the chart count of the algorithm uses. -/
theorem finrank_le_two_mul_of_pi1_eq_pi2 [FiniteDimensional K F]
    (W : Submodule K (F × F)) (h : pi1 W = pi2 W) :
    finrank K ↥W ≤ 2 * finrank K ↥(pi1 W) := by
  have hb := finrank_le_pi1_add_pi2 W
  rw [h] at hb
  calc finrank K ↥W ≤ finrank K ↥(pi2 W) + finrank K ↥(pi2 W) := hb
    _ = 2 * finrank K ↥(pi1 W) := by rw [h]; ring

end Q1Subspace
