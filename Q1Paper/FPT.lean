/-
Q1Paper/FPT.lean

Lemma F, first algebraic ingredients: the r = 0 left-inverse branch
(an injective pencil) and the zero-free-row parameter count.
-/

import Q1Paper.FreeRows
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Module LinearMap

namespace Q1Paper

variable {K W F : Type*}
  [Field K]
  [AddCommGroup W] [Module K W]
  [AddCommGroup F] [Module K F]

/-- A left inverse forces injectivity. -/
theorem injective_of_leftInverse (X : W →ₗ[K] F) (XL : F →ₗ[K] W)
    (h : XL.comp X = LinearMap.id) : Function.Injective X := by
  intro x y hxy
  have hx : XL (X x) = XL (X y) := congrArg XL hxy
  have hx' : XL (X x) = x := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun f : W →ₗ[K] W => f x) h
  have hy' : XL (X y) = y := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun f : W →ₗ[K] W => f y) h
  rw [hx', hy'] at hx
  exact hx

/-- A left inverse gives the dimension bound `dim W ≤ dim F`. -/
theorem finrank_le_of_leftInverse [FiniteDimensional K W]
    [FiniteDimensional K F] (X : W →ₗ[K] F) (XL : F →ₗ[K] W)
    (h : XL.comp X = LinearMap.id) : finrank K W ≤ finrank K F :=
  LinearMap.finrank_le_finrank_of_injective (injective_of_leftInverse X XL h)

/-- The `r = 0` case has no free-row variables. -/
theorem kappaObs_zero (f g : W →ₗ[K] F) :
    KappaObs.kappaObs 0 f g = 0 := by
  simp [KappaObs.kappaObs]


/-- For at least one free row, the free-pair dimension is bounded by the
effective parameter. -/
theorem freePairDim_le_kappaObs (r : ℕ) (hr : 1 ≤ r) (f g : W →ₗ[K] F) :
    finrank K (freePairSpace f g) ≤ KappaObs.kappaObs r f g := by
  rw [KappaObs.kappaObs]
  exact Nat.le_mul_of_pos_left _ hr


end Q1Paper
