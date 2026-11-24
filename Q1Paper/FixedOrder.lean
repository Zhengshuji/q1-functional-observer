
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Q1Paper/FixedOrder.lean

Lemma C, algebraic core of the G = F X substitution:
if X has a left inverse, then H_A = F (X B) for some F iff
H_A = G B for some unconstrained G.
-/


open Module LinearMap

namespace Q1Paper

variable {K W F : Type*}
  [Field K]
  [AddCommGroup W] [Module K W]
  [AddCommGroup F] [Module K F]

/-- The `G = F X` substitution: assuming `X` has a left inverse, the
existence of `F` with `H_A = F (X B)` is equivalent to the existence of an
unconstrained `G` with `H_A = G B`. -/
theorem G_form_iff (B : K →ₗ[K] W) (X : W →ₗ[K] F)
    (HA : K →ₗ[K] F)
    (hX : ∃ XL : F →ₗ[K] W, XL.comp X = LinearMap.id) :
    (∃ Fmap : F →ₗ[K] F, HA = Fmap.comp (X.comp B)) ↔
      ∃ G : W →ₗ[K] F, HA = G.comp B := by
  constructor
  · rintro ⟨Fmap, rfl⟩
    exact ⟨Fmap.comp X, rfl⟩
  · rintro ⟨G, rfl⟩
    rcases hX with ⟨XL, hXL⟩
    refine ⟨G.comp XL, ?_⟩
    apply LinearMap.ext
    intro x
    have hpoint : XL (X (B x)) = B x := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun f : W →ₗ[K] W => f (B x)) hXL
    simp [LinearMap.comp_apply, hpoint]

end Q1Paper
