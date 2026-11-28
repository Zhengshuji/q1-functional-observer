import Mathlib

/-!
Q1Paper/PaperV/UnionZeros.lean

§IV, the algebraic core of Theorem 13's last step.

Paper usage: in the proof of Theorem 13 the parameter space is `ℂ^{qa}` (the fibre coordinates `Y`)
and, for each `α` in the finite set `A`, `E_α` is the set of `Y` at which every `d'`-minor vanishes.
Badness says the `E_α` cover the parameter space. The paper then uses that `ℂ^{qa}` is irreducible to
conclude that one `E_α` is everything.

The same conclusion follows from a purely algebraic fact, without any dimension theory: a finite
union of proper zero sets is proper. That is what this file proves.

* `eq_zero_of_forall_eval_eq_zero` : a multivariate polynomial over an infinite field vanishing
  everywhere is zero (`MvPolynomial.funext`).
* `exists_forall_eval_ne_zero` : finitely many nonzero polynomials have a common nonvanishing point
  (multiply them, then use the previous lemma).
* `exists_eq_zero_of_forall_exists_eval_eq_zero` : if the zero sets of a finite family cover the
  whole space, one member of the family is identically zero.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

namespace Q1Paper.PaperV

variable {K : Type*} [Field K] [Infinite K]
variable {σ ι : Type*}

/-- A multivariate polynomial that vanishes at every point is zero. -/
theorem eq_zero_of_forall_eval_eq_zero (p : MvPolynomial σ K)
    (h : ∀ v : σ → K, MvPolynomial.eval v p = 0) : p = 0 := by
  have := MvPolynomial.funext (p := p) (q := 0) (fun v => by
    simpa using h v)
  simpa using this

/-- Finitely many nonzero polynomials have a common nonvanishing point: a finite union of proper
zero sets is proper. -/
theorem exists_forall_eval_ne_zero [Fintype ι] (p : ι → MvPolynomial σ K)
    (h : ∀ i, p i ≠ 0) : ∃ v : σ → K, ∀ i, MvPolynomial.eval v (p i) ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  -- every point kills some member, hence kills the product
  have hprod : (∏ i, p i) = 0 := by
    apply eq_zero_of_forall_eval_eq_zero
    intro v
    obtain ⟨i, hi⟩ := hcon v
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hne : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => h i)
  exact hne hprod

/-- **Theorem 13, covering step.** If the zero sets of a finite family cover the whole parameter
space, then one member of the family vanishes identically. -/
theorem exists_eq_zero_of_forall_exists_eval_eq_zero [Fintype ι] (p : ι → MvPolynomial σ K)
    (hcov : ∀ v : σ → K, ∃ i, MvPolynomial.eval v (p i) = 0) : ∃ i, p i = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨v, hv⟩ := exists_forall_eval_ne_zero p hcon
  obtain ⟨i, hi⟩ := hcov v
  exact hv i hi

end Q1Paper.PaperV
