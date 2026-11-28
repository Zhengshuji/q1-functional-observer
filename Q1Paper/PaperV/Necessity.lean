import Mathlib
import Q1Paper.PaperV.Specialize

/-!
Q1Paper/PaperV/Necessity.lean

§III, the specialisation step of Theorem 4's necessity direction (Corollary 10).

Paper statement (Corollary 10, verbatim shape): if a positive-degree polynomial `h` with
constant nonzero `λ`-leading coefficient divides every `d'`-minor, then every point of the
fibre is bad: every specialisation of the minor family has a common root.

This file formalises the step that was previously only in the paper:

* over an algebraically closed field, a polynomial of positive `natDegree` has a root
  (`exists_root_of_natDegree_pos`);
* specialisation preserves the positive degree (Lemma 5, `Specialize.lean`);
* specialisation preserves divisibility (`map_dvd_of_dvd`);

hence the specialised divisor has a root, and that root is a common root of the
specialised family.

What this file does **not** contain is the Gauss step that produces `h` from the gcd over
the fraction field `ℂ(t)[λ]`.  That step is the remaining paper-side input of Theorem 4's
necessity direction; `Claims.lean` records it as such.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

open Polynomial MvPolynomial

namespace Q1Paper.PaperV

variable {σ : Type*}

/-- Over an algebraically closed field, a polynomial of positive `natDegree` has a root. -/
theorem exists_root_of_natDegree_pos {K : Type*} [Field K] [IsAlgClosed K]
    (p : Polynomial K) (hp : 1 ≤ p.natDegree) :
    ∃ x : K, p.IsRoot x := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hp
  have hdeg : p.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hp0]
    exact_mod_cast (Nat.ne_of_gt hp)
  exact IsAlgClosed.exists_root p hdeg

/-- **Corollary 10, specialisation step.**  If `h` has constant nonzero `λ`-leading
coefficient, positive degree, and divides every member of the family `f`, then at every
specialisation `t0` the family `f` has a common root: the fibre point is bad. -/
theorem exists_common_root_of_divisor
    {ι : Type*} (f : ι → Polynomial (MvPolynomial σ ℂ))
    (h : Polynomial (MvPolynomial σ ℂ)) (t0 : σ → ℂ) (c : ℂ)
    (hlc : h.leadingCoeff = MvPolynomial.C c) (hc : c ≠ 0)
    (hdeg : 1 ≤ h.natDegree) (hdvd : ∀ i, h ∣ f i) :
    ∃ α : ℂ, ∀ i, ((f i).map (MvPolynomial.eval t0)).eval α = 0 := by
  have hdeg' : 1 ≤ (h.map (MvPolynomial.eval t0)).natDegree :=
    specialized_common_factor h t0 c hlc hc hdeg
  obtain ⟨α, hα⟩ := exists_root_of_natDegree_pos (h.map (MvPolynomial.eval t0)) hdeg'
  refine ⟨α, ?_⟩
  intro i
  obtain ⟨q, hq⟩ := map_dvd_of_dvd t0 (hdvd i)
  calc ((f i).map (MvPolynomial.eval t0)).eval α
      = ((h.map (MvPolynomial.eval t0)) * q).eval α := by rw [hq]
    _ = (h.map (MvPolynomial.eval t0)).eval α * q.eval α := by rw [Polynomial.eval_mul]
    _ = 0 := by rw [hα]; ring

end Q1Paper.PaperV
