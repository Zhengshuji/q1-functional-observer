import Mathlib
import Q1Paper.PaperV.Necessity

/-!
Q1Paper/PaperV/Gauss.lean

§III, the Gauss step of Theorem 4's necessity direction.

The paper's `g` is the monic gcd, over the fibre's function field `K = ℂ(t)`, of the
`d'`-minors of the pencil.  Its positive degree has to be turned into an honest common
divisor over the coordinate ring `R = ℂ[t]` before Corollary 10 can specialise it.
This file supplies that step:

* `exists_primitive_divisor_of_monic_dvd`: a monic `g ∈ K[X]` of positive degree that
  divides the image of a monic `F ∈ R[X]` has a primitive lift `h ∈ R[X]` with
  `h.leadingCoeff = 1`, `1 ≤ h.natDegree`, and `h ∣ f i` for every `i` whose image `g`
  divides;
* `exists_common_root_of_gcd`: consequently every specialisation of the family has a
  common root — the pointwise badness of Corollary 10, now with the Gauss step included.

The integrality input is `IsIntegrallyClosed.eq_map_mul_C_of_dvd` from Mathlib's Gauss
lemma file; `MvPolynomial σ ℂ` is integrally closed because `ℂ` is.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

open Polynomial MvPolynomial

namespace Q1Paper.PaperV

variable {σ : Type*}

/-- **Gauss step.**  Let `R = ℂ[t]`, `K = ℂ(t)`.  If a monic `g ∈ K[X]` of positive degree
divides the image of a monic `F ∈ R[X]`, then `g` has a primitive lift `h ∈ R[X]` with
leading coefficient `1`, positive degree, and `h ∣ f i` whenever `g ∣ (f i).map`. -/
theorem exists_primitive_divisor_of_monic_dvd
    {ι : Type*} (f : ι → Polynomial (MvPolynomial σ ℂ))
    (F : Polynomial (MvPolynomial σ ℂ)) (hF : F.Monic)
    (g : Polynomial (FractionRing (MvPolynomial σ ℂ)))
    (hg : g.Monic) (hdeg : 1 ≤ g.natDegree)
    (hgdvdF : g ∣ F.map (algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ))))
    (hgdvd : ∀ i, g ∣ (f i).map (algebraMap (MvPolynomial σ ℂ)
      (FractionRing (MvPolynomial σ ℂ)))) :
    ∃ h : Polynomial (MvPolynomial σ ℂ),
      h.IsPrimitive ∧ h.leadingCoeff = 1 ∧ 1 ≤ h.natDegree ∧ ∀ i, h ∣ f i := by
  classical
  -- clear denominators: a scalar multiple of `g` has coefficients in `R`
  obtain ⟨h, hhmap⟩ :=
    IsIntegrallyClosed.eq_map_mul_C_of_dvd
      (FractionRing (MvPolynomial σ ℂ)) hF hgdvdF
  -- `g` is monic, so the scalar is `1`
  have hmap : h.map (algebraMap (MvPolynomial σ ℂ)
      (FractionRing (MvPolynomial σ ℂ))) = g := by
    simpa [hg.leadingCoeff] using hhmap
  have hlead : (h.map (algebraMap (MvPolynomial σ ℂ)
      (FractionRing (MvPolynomial σ ℂ)))).leadingCoeff = 1 := by
    rw [hmap, hg.leadingCoeff]
  -- the lift has leading coefficient `1`
  have hhlead : h.leadingCoeff = 1 := by
    apply IsFractionRing.injective (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ))
    rw [← Polynomial.leadingCoeff_map_of_injective
      (IsFractionRing.injective (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ))) h,
      hmap, hg.leadingCoeff, map_one]
  -- hence it is primitive
  have hprim : h.IsPrimitive := by
    rw [isPrimitive_iff_isUnit_of_C_dvd]
    intro r hr
    have hcoeff : ∀ n, r ∣ h.coeff n :=
      (Polynomial.C_dvd_iff_dvd_coeff r h).mp hr
    have : r ∣ h.leadingCoeff := hcoeff h.natDegree
    rw [hhlead] at this
    exact isUnit_of_dvd_one this
  -- and it divides every member over `R`, by Gauss
  have hdvd : ∀ i, h ∣ f i := by
    intro i
    refine hprim.dvd_of_fraction_map_dvd_fraction_map
      (K := FractionRing (MvPolynomial σ ℂ)) ?_
    rw [hmap]
    exact hgdvd i
  refine ⟨h, hprim, hhlead, ?_, hdvd⟩
  -- positive degree is preserved by the (injective) map to `K`
  have hnat : h.natDegree = g.natDegree := by
    rw [← Polynomial.natDegree_map_eq_of_injective
      (IsFractionRing.injective (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ))) h, hmap]
  omega

/-- **Corollary 10 with the Gauss step.**  If the monic gcd `g` over `ℂ(t)[λ]` of the
family has positive degree, then every specialisation of the family has a common root:
every point of the fibre is bad. -/
theorem exists_common_root_of_gcd
    {ι : Type*} (f : ι → Polynomial (MvPolynomial σ ℂ))
    (F : Polynomial (MvPolynomial σ ℂ)) (hF : F.Monic)
    (g : Polynomial (FractionRing (MvPolynomial σ ℂ)))
    (hg : g.Monic) (hdeg : 1 ≤ g.natDegree)
    (hgdvdF : g ∣ F.map (algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ))))
    (hgdvd : ∀ i, g ∣ (f i).map (algebraMap (MvPolynomial σ ℂ)
      (FractionRing (MvPolynomial σ ℂ))))
    (t0 : σ → ℂ) :
    ∃ α : ℂ, ∀ i, ((f i).map (MvPolynomial.eval t0)).eval α = 0 := by
  obtain ⟨h, hprim, hlead, hdeg', hdvd⟩ :=
    exists_primitive_divisor_of_monic_dvd f F hF g hg hdeg hgdvdF hgdvd
  exact exists_common_root_of_divisor f h t0 1 (by rw [hlead]; rfl) one_ne_zero hdeg' hdvd

/-- **Corollary 10, with the Gauss step and no extra data.**  Suppose the family has a
member with nonzero constant `λ`-leading coefficient (as the `d'`-minors do when
`rank H = d'`), and a monic `g ∈ K[X]` of positive degree divides every member over `K`.
Then every specialisation has a common root. -/
theorem exists_common_root_of_gcd_family
    {ι : Type*} (f : ι → Polynomial (MvPolynomial σ ℂ))
    (i0 : ι) (c0 : ℂ) (hc0 : c0 ≠ 0)
    (hlc0 : (f i0).leadingCoeff = MvPolynomial.C c0)
    (g : Polynomial (FractionRing (MvPolynomial σ ℂ)))
    (hg : g.Monic) (hdeg : 1 ≤ g.natDegree)
    (hgdvd : ∀ i, g ∣ (f i).map (algebraMap (MvPolynomial σ ℂ)
      (FractionRing (MvPolynomial σ ℂ))))
    (t0 : σ → ℂ) :
    ∃ α : ℂ, ∀ i, ((f i).map (MvPolynomial.eval t0)).eval α = 0 := by
  classical
  -- a monic scalar multiple of the member with nonzero leading coefficient
  let F : Polynomial (MvPolynomial σ ℂ) :=
    Polynomial.C (MvPolynomial.C c0⁻¹) * f i0
  have hfi0 : f i0 ≠ 0 := by
    intro h0
    have hC : (MvPolynomial.C c0 : MvPolynomial σ ℂ) = 0 := by simpa [h0] using hlc0.symm
    exact hc0 (MvPolynomial.C_eq_zero.mp hC)
  have hF : F.Monic := by
    show F.leadingCoeff = 1
    dsimp only [F]
    rw [Polynomial.leadingCoeff_mul, hlc0, Polynomial.leadingCoeff_C]
    rw [← MvPolynomial.C_mul, inv_mul_cancel₀ hc0, MvPolynomial.C_1]
  have hFmap : F.map (algebraMap (MvPolynomial σ ℂ)
      (FractionRing (MvPolynomial σ ℂ))) =
      Polynomial.C (algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ))
        (MvPolynomial.C c0⁻¹)) *
      (f i0).map (algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ))) := by
    dsimp only [F]
    rw [Polynomial.map_mul, Polynomial.map_C]
  have hgdvdF : g ∣ F.map (algebraMap (MvPolynomial σ ℂ)
      (FractionRing (MvPolynomial σ ℂ))) := by
    rw [hFmap]
    exact dvd_mul_of_dvd_right (hgdvd i0) _
  exact exists_common_root_of_gcd f F hF g hg hdeg hgdvdF hgdvd t0

end Q1Paper.PaperV
