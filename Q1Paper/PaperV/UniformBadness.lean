import Mathlib

/-!
Q1Paper/PaperV/UniformBadness.lean

§IV, the direction "a fixed spectral factor fails the fibre everywhere".

Paper usage: Theorem 13 ends by producing a single `λ₀` that kills every `d'`-minor at every point of
the fibre. The mathematical content of that conclusion is: a factor with *constant* coefficients
(`g ∈ ℂ[λ]`) of positive degree, dividing the pencil's minors over the parameter ring, produces a
common root after every specialisation.

That is proved here in its cleanest form: if `g ∈ K[λ]` has positive degree, divides `f ∈ K[t][λ]`
after embedding, and `K` is algebraically closed, then at every `t₀ ∈ K` the specialised polynomial
`f(t₀)` shares a root with `g`. This is the "uniform badness ⇒ pointwise badness" step; it is the
counterpart of `not_isUnit_gcd_of_forall_eval_eq_zero` in `FamilyGcd.lean`, which gives the converse
implication.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

namespace Q1Paper.PaperV

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Specialising the embedded copy of `g ∈ K[λ]` gives `g` back. -/
theorem map_evalRingHom_map_C (g : Polynomial K) (t₀ : K) :
    Polynomial.map (Polynomial.evalRingHom t₀) (Polynomial.map Polynomial.C g) = g := by
  rw [Polynomial.map_map]
  have : (Polynomial.evalRingHom t₀).comp Polynomial.C = RingHom.id K := by
    ext a
    simp
  rw [this, Polynomial.map_id]

/-- **Uniform badness implies pointwise badness.** A positive-degree factor with constant coefficients
of `f ∈ K[t][λ]` forces, at every `t₀`, a common root of `g` and the specialised `f(t₀)`. -/
theorem exists_common_root_of_uniform_factor (g : Polynomial K) (hdeg : 1 ≤ g.natDegree)
    (f : Polynomial (Polynomial K))
    (hdvd : Polynomial.map Polynomial.C g ∣ f) (t₀ : K) :
    ∃ x : K, g.IsRoot x ∧ (Polynomial.map (Polynomial.evalRingHom t₀) f).IsRoot x := by
  -- `g` has a root because it has positive degree and `K` is algebraically closed
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hdeg' : g.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hg0]
    have hpos : (0 : ℕ) < g.natDegree := hdeg
    exact_mod_cast Nat.pos_iff_ne_zero.mp hpos
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root g hdeg'
  refine ⟨x, hx, ?_⟩
  -- the root survives every specialisation, because the divisibility does
  have hdvd' : g ∣ Polynomial.map (Polynomial.evalRingHom t₀) f := by
    obtain ⟨q, hq⟩ := hdvd
    refine ⟨Polynomial.map (Polynomial.evalRingHom t₀) q, ?_⟩
    rw [hq, Polynomial.map_mul, map_evalRingHom_map_C]
  exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd' hx

end Q1Paper.PaperV
