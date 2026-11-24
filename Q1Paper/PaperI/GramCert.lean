
import Q1Paper.PaperI.GramInj

/-!
Q1Paper/PaperI/GramCert.lean

D1 step 5: certificate equivalence.  If two Gram matrices differ by a nonzero
scalar, solvability of G x = e₀ is the same for both; applied to the window
matrices, whose Gram matrices differ by (ω!)², this transfers the certificate
between the injective-indexed and subset-indexed families.
-/


open Matrix Polynomial

namespace Q1Paper.PaperI

/-- **Scalar rescaling of a Gram certificate.** If `G₁ = c • G₂` with `c ≠ 0`,
solvability of `G x = e₀` is the same for the two matrices. -/
theorem gram_solvable_iff_smul {K : Type*} [Field K] {n : ℕ}
    (G₁ G₂ : Matrix (Fin n) (Fin n) K) (c : K)
    (hc : c ≠ 0) (h : G₁ = c • G₂) (e₀ : Fin n → K) :
    (∃ x, G₁ *ᵥ x = e₀) ↔ (∃ y, G₂ *ᵥ y = e₀) := by
  constructor
  · rintro ⟨x, hx⟩
    have hx' : G₂ *ᵥ x = c⁻¹ • e₀ := by
      have h1 := congrArg (fun v => c⁻¹ • v) hx
      simp only [h, smul_mulVec, smul_smul, inv_mul_cancel₀ hc, one_smul] at h1
      exact h1
    refine ⟨c • x, ?_⟩
    simp only [mulVec_smul, hx', smul_smul, mul_inv_cancel₀ hc, one_smul]
  · rintro ⟨y, hy⟩
    refine ⟨c⁻¹ • y, ?_⟩
    simp only [h, smul_mulVec, mulVec_smul, hy, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **Certificate equivalence for the two window matrices** (over `ℂ`, where
`(ω!)² ≠ 0`). -/
theorem gram_certificate_iff_subset {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) ℂ[X]) (ω : ℕ) :
    (∃ x, ((windowInj P ω)ᵀ * windowInj P ω) *ᵥ x = windowOne (K := ℂ) ω) ↔
      (∃ y, ((windowSub P ω)ᵀ * windowSub P ω) *ᵥ y = windowOne (K := ℂ) ω) := by
  have hc : ((ω.factorial * ω.factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (Nat.factorial_ne_zero ω) (Nat.factorial_ne_zero ω)
  have h : (windowInj P ω)ᵀ * windowInj P ω =
      ((ω.factorial * ω.factorial : ℕ) : ℂ) • ((windowSub P ω)ᵀ * windowSub P ω) := by
    rw [gram_inj_eq_factorial_smul P ω, Nat.cast_smul_eq_nsmul]
  exact gram_solvable_iff_smul _ _ _ hc h _

end Q1Paper.PaperI
