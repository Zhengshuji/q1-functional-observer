import Mathlib

/-!
Q1Paper/PaperV/LeadingCoeff.lean

§III, the leading coefficient step behind Theorem 4.

Paper statement used in the proof of Theorem 4 (`§III`):

  *The `λ`-leading coefficient of the `d' × d'` minor of `λ H - H A` on rows `I` and
  columns `J` is `det H_{IJ}`; on a nonzero minor this is a nonzero constant, which is
  what Lemma 5 (specialisation) needs.*

This file proves the **complete identity**, not just its nonvanishing form: the
coefficient of `λ ^ d` in `det (λ • H - B)` is `det H`, for arbitrary `B` and with no
hypothesis on `det H`.  The full form is what makes the corollary free (if `det H ≠ 0`
the coefficient is a nonzero constant) and it also covers the degenerate case `det H = 0`,
where the degree genuinely drops.

Mathematically this is one line: Leibniz expansion, and a product of `d` factors of degree
at most one has `λ ^ d`-coefficient equal to the product of their `λ`-coefficients.  The
Lean proof uses `Polynomial.coeff_prod_of_natDegree_le` to get the product coefficient in
one step.  No `sorry`, no axioms beyond Lean's three standard ones.
-/

namespace Q1Paper.PaperV

open Polynomial

variable {K : Type*} [Field K]

/-- The coefficient of `X ^ 1` in `C a * X - C b` is `a`. -/
theorem coeff_one_C_mul_X_sub_C (a b : K) :
    ((Polynomial.C a * Polynomial.X - Polynomial.C b : Polynomial K)).coeff 1 = a := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one,
    Polynomial.coeff_C]
  simp

/-- `C a * X - C b` has degree at most one (no hypothesis on `a`). -/
theorem natDegree_C_mul_X_sub_C_le (a b : K) :
    (Polynomial.C a * Polynomial.X - Polynomial.C b : Polynomial K).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · simpa using Polynomial.natDegree_C_mul_X_pow_le (R := K) a 1
  · rw [Polynomial.natDegree_C]
    exact Nat.zero_le 1

/-- **Leading coefficient (Theorem 4's step).** The `λ ^ d` coefficient of
`det (λ • H - B)` is `det H`, for every `B`. -/
theorem coeff_det_smul_sub_X {d : ℕ} (H B : Matrix (Fin d) (Fin d) K) :
    (Matrix.det (fun i j =>
      (Polynomial.C (H i j) * Polynomial.X - Polynomial.C (B i j) : Polynomial K))).coeff d
      = Matrix.det H := by
  classical
  set M : Matrix (Fin d) (Fin d) (Polynomial K) :=
    fun i j => (Polynomial.C (H i j) * Polynomial.X - Polynomial.C (B i j) : Polynomial K) with hM
  -- a Leibniz product has degree at most `d`, so its `λ ^ d` coefficient is the product
  -- of the `λ`-coefficients of its factors
  have hprod : ∀ σ : Equiv.Perm (Fin d), (∏ i, M (σ i) i).coeff d = ∏ i, H (σ i) i := by
    intro σ
    have h := Polynomial.coeff_prod_of_natDegree_le (s := Finset.univ)
      (f := fun i => M (σ i) i) (n := 1)
      (h := fun i _ => natDegree_C_mul_X_sub_C_le (H (σ i) i) (B (σ i) i))
    rw [Finset.card_univ, Fintype.card_fin, mul_one] at h
    rw [h]
    exact Finset.prod_congr rfl (fun i _ => coeff_one_C_mul_X_sub_C (H (σ i) i) (B (σ i) i))
  -- Leibniz, with the permutation sign moved inside `C`
  have hexp : M.det = ∑ σ : Equiv.Perm (Fin d),
      Polynomial.C (((Equiv.Perm.sign σ : ℤ) : K)) * ∏ i, M (σ i) i := by
    rw [Matrix.det_apply']
    exact Finset.sum_congr rfl
      (fun σ _ => by rw [map_intCast (Polynomial.C : K →+* Polynomial K)])
  calc (Matrix.det (fun i j =>
          (Polynomial.C (H i j) * Polynomial.X - Polynomial.C (B i j) : Polynomial K))).coeff d
      = (M.det).coeff d := by simp only [hM]
    _ = (∑ σ : Equiv.Perm (Fin d),
          Polynomial.C (((Equiv.Perm.sign σ : ℤ) : K)) * ∏ i, M (σ i) i).coeff d := by rw [hexp]
    _ = ∑ σ : Equiv.Perm (Fin d),
          (((Equiv.Perm.sign σ : ℤ) : K)) * (∏ i, H (σ i) i) := by
        rw [Polynomial.finsetSum_coeff]
        exact Finset.sum_congr rfl (fun σ _ => by rw [Polynomial.coeff_C_mul, hprod σ])
    _ = Matrix.det H := (Matrix.det_apply' H).symm

/-- **Corollary (what Theorem 4 uses).** A nonzero `det H` makes the `λ ^ d` coefficient
of `det (λ • H - B)` a nonzero constant, independent of `B`. -/
theorem coeff_det_smul_sub_X_ne_zero {d : ℕ} {H B : Matrix (Fin d) (Fin d) K}
    (hH : Matrix.det H ≠ 0) :
    (Matrix.det (fun i j =>
      (Polynomial.C (H i j) * Polynomial.X - Polynomial.C (B i j) : Polynomial K))).coeff d ≠ 0 := by
  rw [coeff_det_smul_sub_X]
  exact hH

end Q1Paper.PaperV
