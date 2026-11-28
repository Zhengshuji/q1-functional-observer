import Mathlib
import Q1Paper.PaperV.LeadingCoeff
import Q1Paper.PaperV.RootBound

/-!
Q1Paper/PaperV/CriticalSet.lean

§IV, the finiteness of the critical set `A` in the proof of Theorem 13.

Paper usage: `A = {α : rank(αX − B₀) < d'}`. Choosing a `d' × d'` submatrix on which `X` is
invertible, the determinant `p(α) = det(α X_{I,J} − (B₀)_{I,J})` is a polynomial of degree exactly
`d'` (leading coefficient `det X_{I,J} ≠ 0`), and `rank < d'` forces `p(α) = 0`. So `A` is contained
in the zero set of a nonzero polynomial of degree `d'`, hence has at most `d'` elements.

This file proves the two ingredients:

* `natDegree_det_smul_sub_X_le` : the determinant of `λ • H − B` has degree at most `d`;
* `card_roots_le_of_coeff_ne_zero` : a polynomial of degree at most `d` with nonzero `λ^d` coefficient
  has at most `d` roots in any finite set.

Together with `LeadingCoeff.coeff_det_smul_sub_X` (the `λ^d` coefficient is `det H`) they give the
finiteness of `A`.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

noncomputable section

open Classical

attribute [local instance] Classical.propDecidable

namespace Q1Paper.PaperV

open Polynomial

variable {K : Type*} [Field K]

/-- The determinant of `λ • H − B`, as a polynomial in `λ`, has degree at most `d`. -/
theorem natDegree_det_smul_sub_X_le {d : ℕ} (H B : Matrix (Fin d) (Fin d) K) :
    (Matrix.det (fun i j =>
      (Polynomial.C (H i j) * Polynomial.X - Polynomial.C (B i j) : Polynomial K))).natDegree
      ≤ d := by
  classical
  set M : Matrix (Fin d) (Fin d) (Polynomial K) :=
    fun i j => (Polynomial.C (H i j) * Polynomial.X - Polynomial.C (B i j) : Polynomial K) with hM
  rw [Matrix.det_apply']
  refine le_trans (Polynomial.natDegree_sum_le _ _) (Finset.sup_le fun σ _ => ?_)
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  rw [Polynomial.natDegree_intCast, Nat.zero_add]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin d)), (M (σ i) i).natDegree ≤ 1 :=
    fun i _ => natDegree_C_mul_X_sub_C_le (H (σ i) i) (B (σ i) i)
  calc (∑ i, (M (σ i) i).natDegree) ≤ ∑ _i : Fin d, 1 :=
        Finset.sum_le_sum fun i _ => h1 i (Finset.mem_univ i)
    _ = d := by simp

/-- A polynomial of degree at most `d` whose `λ^d` coefficient is nonzero has at most `d` roots in
any finite set. -/
theorem card_roots_le_of_coeff_ne_zero {d : ℕ} {p : Polynomial K}
    (hdeg : p.natDegree ≤ d) (hc : p.coeff d ≠ 0) (S : Finset K) :
    (S.filter fun x => p.IsRoot x).card ≤ d := by
  classical
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hc
  have hd : d ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero hc
  have hnd : p.natDegree = d := le_antisymm hdeg hd
  have := card_roots_le_natDegree p hp S
  omega

end Q1Paper.PaperV
