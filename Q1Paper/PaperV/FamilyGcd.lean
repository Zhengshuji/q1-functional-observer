import Mathlib

/-!
Q1Paper/PaperV/FamilyGcd.lean

§III, the finite-family form of the criterion's algebraic core.

Paper statement (Theorem 4, family form): a finite family of nonzero polynomials over an
algebraically closed field has a greatest common divisor which is a unit exactly when the family
admits no common root.  This is the form actually used in the paper, where the family is the set of
all `d'`-minors of the pencil.

Instance note: `Finset.gcd` needs `NormalizedGCDMonoid (Polynomial K)`, which for an abstract field
`K` is derived through `StrongNormalizedGCDMonoid K` and hence needs `[DecidableEq K]`; the local
classical instance supplies it without changing the statement.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

set_option maxHeartbeats 800000

open Polynomial

attribute [local instance] Classical.decEq

namespace Q1Paper.PaperV

/-- **Theorem 4, family form.** For a finite family of nonzero polynomials over an algebraically
closed field, the gcd of the family is a unit iff the family has no common root. -/
theorem isUnit_gcd_iff_no_common_root {K : Type*} [Field K] [IsAlgClosed K]
    {ι : Type*} (s : Finset ι) (f : ι → Polynomial K) (hne : ∀ i ∈ s, f i ≠ 0) :
    IsUnit (s.gcd f) ↔ ∀ x : K, ¬ ∀ i ∈ s, (f i).IsRoot x := by
  constructor
  · rintro hg x hx
    have hdvd : (X - C x : Polynomial K) ∣ s.gcd f :=
      Finset.dvd_gcd fun i hi => Polynomial.dvd_iff_isRoot.mpr (hx i hi)
    have hunit : IsUnit (X - C x : Polynomial K) :=
      isUnit_iff_dvd_one.mpr (dvd_trans hdvd (isUnit_iff_dvd_one.mp hg))
    have hnot : ¬ IsUnit (X - C x : Polynomial K) := by
      rintro ⟨v, hv⟩
      have hmul : (X - C x : Polynomial K) * ((v⁻¹ : (Polynomial K)ˣ) : Polynomial K) = 1 := by
        rw [← hv]
        simp
      have h := congrArg (Polynomial.eval x) hmul
      simpa using h
    exact hnot hunit
  · intro h
    by_contra hnot
    have hdeg : (s.gcd f).degree ≠ 0 := fun hd =>
      hnot (Polynomial.isUnit_iff_degree_eq_zero.mpr hd)
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (s.gcd f) hdeg
    exact h x fun i hi =>
      Polynomial.dvd_iff_isRoot.mp
        (dvd_trans (Polynomial.dvd_iff_isRoot.mpr hx) (Finset.gcd_dvd hi))

/-- **Theorem 4, sufficiency at a point.** If the family of minors has gcd one, then at every `x` at
least one member of the family is nonzero at `x`: this is the step "the pencil has full rank at every
`λ`" in the criterion. -/
theorem exists_eval_ne_zero_of_isUnit_gcd {K : Type*} [Field K] [IsAlgClosed K]
    {ι : Type*} (s : Finset ι) (f : ι → Polynomial K) (hne : ∀ i ∈ s, f i ≠ 0)
    (hgcd : IsUnit (s.gcd f)) (x : K) : ∃ i ∈ s, (f i).eval x ≠ 0 := by
  have h := (isUnit_gcd_iff_no_common_root s f hne).mp hgcd x
  push_neg at h
  obtain ⟨i, hi, hne0⟩ := h
  exact ⟨i, hi, by simpa [Polynomial.IsRoot.def] using hne0⟩


/-- **Theorem 4, necessity at a point.** If some `x` makes every member of the family vanish, the gcd
cannot be a unit: this is the shape used when a single fibre point already fails the rank condition. -/
theorem not_isUnit_gcd_of_forall_eval_eq_zero {K : Type*} [Field K] [IsAlgClosed K]
    {ι : Type*} (s : Finset ι) (f : ι → Polynomial K) (x : K)
    (h : ∀ i ∈ s, (f i).eval x = 0) : ¬ IsUnit (s.gcd f) := by
  intro hg
  have hdvd : (X - C x : Polynomial K) ∣ s.gcd f :=
    Finset.dvd_gcd fun i hi => Polynomial.dvd_iff_isRoot.mpr (by
      rw [Polynomial.IsRoot.def]; exact h i hi)
  have hunit : IsUnit (X - C x : Polynomial K) :=
    isUnit_iff_dvd_one.mpr (dvd_trans hdvd (isUnit_iff_dvd_one.mp hg))
  have hnot : ¬ IsUnit (X - C x : Polynomial K) := by
    rintro ⟨v, hv⟩
    have hmul : (X - C x : Polynomial K) * ((v⁻¹ : (Polynomial K)ˣ) : Polynomial K) = 1 := by
      rw [← hv]
      simp
    have hc := congrArg (Polynomial.eval x) hmul
    simpa using hc
  exact hnot hunit


end Q1Paper.PaperV
