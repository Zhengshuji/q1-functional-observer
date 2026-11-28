import Mathlib

/-!
Q1Paper/PaperV/Specialize.lean

§III, Lemma 2 (**specialisation does not drop the λ-degree**).

Paper statement (verbatim):

  *Let `h ∈ ℂ[t][λ]` have `λ`-leading coefficient equal to a nonzero constant `c`.
  Then for every `t₀`, `natDegree (h(t₀,·)) = natDegree h`; consequently `h ∣ f` in
  `ℂ[t][λ]` implies `h(t₀,·) ∣ f(t₀,·)`.*

This is the only non-trivial step of the paper's criterion (§III): it says that a
positive-degree common divisor of the minors — whose primitive representative has a
constant λ-leading coefficient, namely `det H_{IJ}` on a nonzero `d' × d'` minor —
cannot disappear when the fibre parameters are specialised.  Hence "positive generic
degree" ⇔ "bad at every point of the fibre" (Corollary 8).

The coefficient ring is `MvPolynomial σ ℂ`, the fibre's coordinate ring; `eval t₀`
is the specialisation.  No `sorry`, no axioms beyond Lean's three standard ones.
-/

open Polynomial MvPolynomial

namespace Q1Paper.PaperV

variable {σ : Type*}

/-- **Lemma 2 (degree).** A nonzero constant λ-leading coefficient survives every
specialisation, so the λ-degree cannot drop. -/
theorem natDegree_map_eval_of_leadingCoeff_const
    (h : Polynomial (MvPolynomial σ ℂ)) (t0 : σ → ℂ) (c : ℂ)
    (hlc : h.leadingCoeff = MvPolynomial.C c) (hc : c ≠ 0) :
    (h.map (MvPolynomial.eval t0)).natDegree = h.natDegree := by
  have hmap : (MvPolynomial.eval t0) h.leadingCoeff ≠ 0 := by
    rw [hlc, MvPolynomial.eval_C]
    exact hc
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact Polynomial.natDegree_map_le
  · rw [Polynomial.coeff_map, Polynomial.coeff_natDegree]
    exact hmap

/-- **Lemma 2 (divisibility).** Divisibility is preserved by specialisation. -/
theorem map_dvd_of_dvd {h f : Polynomial (MvPolynomial σ ℂ)} (t0 : σ → ℂ)
    (hdvd : h ∣ f) :
    h.map (MvPolynomial.eval t0) ∣ f.map (MvPolynomial.eval t0) :=
  Polynomial.map_dvd _ hdvd

/-- **Corollary 8 (shape).** A divisor of positive degree with constant nonzero
λ-leading coefficient keeps positive degree after every specialisation: the fibre
cannot become feasible at a point where the generic common divisor has a root. -/
theorem specialized_common_factor
    (h : Polynomial (MvPolynomial σ ℂ)) (t0 : σ → ℂ) (c : ℂ)
    (hlc : h.leadingCoeff = MvPolynomial.C c) (hc : c ≠ 0)
    (hdeg : 1 ≤ h.natDegree) :
    1 ≤ (h.map (MvPolynomial.eval t0)).natDegree := by
  rw [natDegree_map_eval_of_leadingCoeff_const h t0 c hlc hc]
  exact hdeg

end Q1Paper.PaperV
