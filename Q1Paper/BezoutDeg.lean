/-
Q1Paper/BezoutDeg.lean

Towards the degree-bounded Bezout lemma of the paper.

* a family without common root has a nonzero linear combination;
* that combination has finitely many roots;
* over an algebraically closed field, two polynomials without common root are coprime
  (`IsCoprime`, i.e. `∃ a b, a * x + b * y = 1`);
* the Bezout multipliers can be chosen with `natDegree` below a bound `ω ≥ 1` that
  dominates both degrees.

The coprimality step avoids normalising `EuclideanDomain.gcd`: the gcd is a nonzero
constant, hence a unit, and multiplying a Bezout relation for the gcd by its inverse
gives one for 1.  The degree bounds come from reducing the first multiplier modulo the
second polynomial.
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsAlgClosed.Basic

open Polynomial

namespace Q1Paper

variable {K ι : Type*} [Field K] [Fintype ι]

/-- A family without common root has a nonzero linear combination. -/
theorem exists_ne_zero_linearCombination (f : ι → K[X])
    (h : ∀ x : K, ∃ i, (f i).eval x ≠ 0) :
    ∃ a : ι → K, (∑ i, C (a i) * f i) ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := h 0
  let a : ι → K := Pi.single i 1
  refine ⟨a, ?_⟩
  have hsum : (∑ j, C (a j) * f j) = f i := by
    rw [Finset.sum_eq_single i]
    · simp [a]
    · intro b _ hb
      simp [a, Pi.single_eq_of_ne hb]
    · intro hmem
      exact absurd (Finset.mem_univ i) hmem
  rw [hsum]
  intro hzero
  exact hi (by rw [hzero, eval_zero])

/-- A nonzero combination of such a family has only finitely many roots. -/
theorem exists_ne_zero_with_finite_roots (f : ι → K[X])
    (h : ∀ x : K, ∃ i, (f i).eval x ≠ 0) :
    ∃ F : K[X], F ≠ 0 ∧ Set.Finite {x : K | IsRoot F x} := by
  obtain ⟨a, ha⟩ := exists_ne_zero_linearCombination f h
  exact ⟨∑ i, C (a i) * f i, ha, finite_setOfPred_isRoot ha⟩

section

variable [IsAlgClosed K]

/-- Over an algebraically closed field, polynomials without common root satisfy a
Bezout identity. -/
theorem isCoprime_of_no_common_root {F G : K[X]} (hF : F ≠ 0)
    (h : ∀ x : K, ¬ (F.IsRoot x ∧ G.IsRoot x)) : IsCoprime F G := by
  classical
  set d := EuclideanDomain.gcd F G with hd
  have hdvdF : d ∣ F := EuclideanDomain.gcd_dvd_left F G
  have hdvdG : d ∣ G := EuclideanDomain.gcd_dvd_right F G
  have hd0 : d ≠ 0 := by
    intro h0
    obtain ⟨q, hq⟩ := hdvdF
    rw [h0] at hq
    exact hF (by rw [hq]; simp)
  have hnat : d.natDegree = 0 := by
    by_contra hne
    have hdegne : d.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hd0]
      simpa using hne
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root d hdegne
    have hx' : d.eval x = 0 := hx
    have hxF : F.IsRoot x := by
      obtain ⟨q, hq⟩ := hdvdF
      rw [hq]
      show (d * q).eval x = 0
      rw [eval_mul, hx', zero_mul]
    have hxG : G.IsRoot x := by
      obtain ⟨q, hq⟩ := hdvdG
      rw [hq]
      show (d * q).eval x = 0
      rw [eval_mul, hx', zero_mul]
    exact h x ⟨hxF, hxG⟩
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hnat
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0] at hc
    exact hd0 (by simpa using hc.symm)
  have hgcd : d = F * EuclideanDomain.gcdA F G + G * EuclideanDomain.gcdB F G := by
    rw [hd]
    exact EuclideanDomain.gcd_eq_gcd_ab F G
  refine ⟨C c⁻¹ * EuclideanDomain.gcdA F G, C c⁻¹ * EuclideanDomain.gcdB F G, ?_⟩
  have hone : C c⁻¹ * d = 1 := by
    rw [← hc, ← C_mul, inv_mul_cancel₀ hc0, C_1]
  calc C c⁻¹ * EuclideanDomain.gcdA F G * F
        + C c⁻¹ * EuclideanDomain.gcdB F G * G
      = C c⁻¹ * (F * EuclideanDomain.gcdA F G + G * EuclideanDomain.gcdB F G) := by
        ring
    _ = C c⁻¹ * d := by rw [hgcd]
    _ = 1 := hone

end

/-- Degree-bounded Bezout: the multipliers can be chosen with `natDegree` below any
`ω ≥ 1` that dominates both degrees. -/
theorem exists_bezout_deg_lt {F G : K[X]} {ω : ℕ}
    (hF : F ≠ 0) (hG : G ≠ 0) (hω : 1 ≤ ω)
    (hFd : F.natDegree ≤ ω) (hGd : G.natDegree ≤ ω)
    (h : IsCoprime F G) :
    ∃ u v : K[X], u * F + v * G = 1 ∧ u.natDegree < ω ∧ v.natDegree < ω := by
  classical
  by_cases hF0 : F.natDegree = 0
  · -- `F` is a nonzero constant
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hF0
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0] at hc
      exact hF (by rw [← hc]; simp)
    refine ⟨C c⁻¹, 0, ?_, ?_, ?_⟩
    · rw [← hc, ← C_mul, inv_mul_cancel₀ hc0, C_1]
      simp
    · rw [Polynomial.natDegree_C]
      exact hω
    · rw [Polynomial.natDegree_zero]
      exact hω
  · by_cases hG0 : G.natDegree = 0
    · -- `G` is a nonzero constant
      obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hG0
      have hc0 : c ≠ 0 := by
        intro h0
        rw [h0] at hc
        exact hG (by rw [← hc]; simp)
      refine ⟨0, C c⁻¹, ?_, ?_, ?_⟩
      · rw [← hc, ← C_mul, inv_mul_cancel₀ hc0, C_1]
        simp
      · rw [Polynomial.natDegree_zero]
        exact hω
      · rw [Polynomial.natDegree_C]
        exact hω
    · -- both are nonconstant
      obtain ⟨u₀, v₀, hbez⟩ := h
      set q : K[X] := u₀ / G with hq
      set r : K[X] := u₀ % G with hr
      have hdiv : r + q * G = u₀ := by
        have h1 := EuclideanDomain.mod_add_div u₀ G
        rw [← hr, ← hq, mul_comm] at h1
        exact h1
      have hrdeg : r.natDegree < G.natDegree := Polynomial.natDegree_mod_lt u₀ hG0
      have hrd : r.natDegree < ω := lt_of_lt_of_le hrdeg hGd
      have hkey : r * F + (v₀ + q * F) * G = 1 := by
        have hu : u₀ * F = r * F + q * G * F := by rw [← hdiv]; ring
        calc r * F + (v₀ + q * F) * G = (r * F + q * G * F) + v₀ * G := by ring
          _ = u₀ * F + v₀ * G := by rw [hu]
          _ = 1 := hbez
      refine ⟨r, v₀ + q * F, hkey, hrd, ?_⟩
      set v : K[X] := v₀ + q * F with hvdef
      by_cases hv : v = 0
      · rw [hv]
        exact hω
      · have hvG : v * G = 1 - r * F := by
          have h1 := hkey
          rw [hvdef] at h1
          rw [← h1]
          ring
        have hmul : (v * G).natDegree = v.natDegree + G.natDegree :=
          Polynomial.natDegree_mul hv hG
        have hupper : (1 - r * F).natDegree ≤ max 0 (r * F).natDegree := by
          have h1 : (1 - r * F) = (1 : K[X]) + (-(r * F)) := by ring
          rw [h1]
          calc ((1 : K[X]) + (-(r * F))).natDegree
              ≤ max (1 : K[X]).natDegree (-(r * F)).natDegree :=
                Polynomial.natDegree_add_le _ _
            _ ≤ max 0 (r * F).natDegree := by
                rw [Polynomial.natDegree_neg, Polynomial.natDegree_one]
        rw [← hvG, hmul] at hupper
        by_cases hr0 : r = 0
        · rw [hr0] at hupper
          simp only [zero_mul, Polynomial.natDegree_zero, max_eq_left (Nat.zero_le _)] at hupper
          omega
        · have hrF : (r * F).natDegree = r.natDegree + F.natDegree :=
            Polynomial.natDegree_mul hr0 hF
          rw [hrF] at hupper
          omega

end Q1Paper
