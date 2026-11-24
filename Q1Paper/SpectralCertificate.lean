
import Mathlib

/-!
Q1Paper/SpectralCertificate.lean

Lemma D, first algebraic ingredient: the two-polynomial Bezout identity
underlying the bounded-degree certificate.
-/


open Polynomial

noncomputable section

namespace Q1Paper

variable {K : Type*} [Field K] [DecidableEq K]

/-- Two-polynomial Bezout: if the Euclidean gcd of `f` and `g` is one, then
there are polynomials `u,v` with `u f + v g = 1`. -/
theorem bezout_of_gcd_eq_one (f g : K[X]) (h : EuclideanDomain.gcd f g = 1) :
    ∃ u v : K[X], u * f + v * g = 1 := by
  refine ⟨EuclideanDomain.gcdA f g, EuclideanDomain.gcdB f g, ?_⟩
  have hh := EuclideanDomain.gcd_eq_gcd_ab f g
  rw [h] at hh
  -- hh : 1 = f * gcdA + g * gcdB
  calc
    EuclideanDomain.gcdA f g * f + EuclideanDomain.gcdB f g * g
        = f * EuclideanDomain.gcdA f g + g * EuclideanDomain.gcdB f g := by
          rw [mul_comm (EuclideanDomain.gcdA f g) f,
            mul_comm (EuclideanDomain.gcdB f g) g]
    _ = 1 := hh.symm


/-- A finite sum of real squares vanishes exactly when the vector is zero.
This is the positivity input behind the Gram/PSD rank criteria. -/
theorem sum_sq_eq_zero_iff {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    (∑ i, v i * v i = 0) ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have hnonneg : ∀ i, 0 ≤ v i * v i := fun i => mul_self_nonneg (v i)
    have hzero : v i * v i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp h i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hzero
  · rintro rfl
    simp


end Q1Paper

end
