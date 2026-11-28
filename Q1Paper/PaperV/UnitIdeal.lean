import Mathlib

/-!
Q1Paper/PaperV/UnitIdeal.lean

§III, the Bezout step behind Theorem 4 and Theorem 7.

Paper statement used twice: if the greatest common divisor of a finite family of polynomials over a
field is `1`, then the family generates the unit ideal, i.e. there are coefficient polynomials with
`∑ A i * f i = 1`.

* In Theorem 4 this is the step "the minors have gcd one, hence the pencil has full rank at the
  generic point".
* In Theorem 7 it is the Bezout identity that is then cleared of denominators to produce the nonzero
  `D ∈ ℂ[t]`.

Note on the instance: `s.gcd f` for `Polynomial K` needs `NormalizedGCDMonoid (Polynomial K)`, which
Mathlib does not synthesise from `[Field K]` alone; the local `Classical.decEq` instance unlocks it
without adding a hypothesis to the statement.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

noncomputable section

open Classical

attribute [local instance] Classical.decEq

namespace Q1Paper.PaperV

/-- **Unit-ideal step.** A finite family of polynomials over a field with gcd `1` admits a Bezout
identity. -/
theorem exists_combination_eq_one_of_gcd_eq_one {K : Type*} [Field K]
    {ι : Type*} (s : Finset ι) (f : ι → Polynomial K)
    (hgcd : s.gcd f = 1) :
    ∃ A : ι → Polynomial K, ∑ i ∈ s, A i * f i = 1 := by
  obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul (R := Polynomial K) s f
  refine ⟨g, ?_⟩
  rw [← hgcd, hg]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The same family generates the unit ideal. -/
theorem ideal_span_eq_top_of_gcd_eq_one {K : Type*} [Field K] {ι : Type*}
    (s : Finset ι) (f : ι → Polynomial K) (hgcd : s.gcd f = 1) :
    Ideal.span (Set.range f) = ⊤ := by
  obtain ⟨A, hA⟩ := exists_combination_eq_one_of_gcd_eq_one s f hgcd
  rw [Ideal.eq_top_iff_one, ← hA]
  refine Ideal.sum_mem _ fun i _ => ?_
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- Binary form: coprimality *is* a Bezout pair. -/
theorem exists_combination_eq_one {K : Type*} [Field K] (f g : Polynomial K)
    (h : IsCoprime f g) : ∃ A B : Polynomial K, A * f + B * g = 1 := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨a, b, hab⟩

end Q1Paper.PaperV

end
