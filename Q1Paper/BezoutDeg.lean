/-
Q1Paper/BezoutDeg.lean

First steps towards the degree-bounded Bezout lemma of the paper: the existence of
a nonzero linear combination of a family without common root, and the finiteness of
its root set.  These feed the hyperplane-avoidance lemma (`HyperplaneAvoid.lean`)
that produces the second combination coprime to the first.
-/

import Mathlib.Algebra.Polynomial.Roots

open Polynomial

namespace Q1Paper

variable {K ι : Type*} [Field K] [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
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

end Q1Paper
