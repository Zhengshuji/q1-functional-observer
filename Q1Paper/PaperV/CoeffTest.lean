import Mathlib

/-!
Q1Paper/PaperV/CoeffTest.lean

§IV, Proposition 15 (**coefficient test**): "a fixed `λ₀` kills every minor at every point of the
fibre" is the same as "every coefficient polynomial `q_{I,m}` vanishes at `λ₀`".

Paper statement: write each nonzero `d'`-minor as
`f_I(λ, y) = ∑_e λ^e ∑_m a_{I,e,m} y^m` and put `q_{I,m}(λ) = ∑_e a_{I,e,m} λ^e`; then the fibre
is entirely bad iff the family `{q_{I,m}}` has a common root.

This file formalises the algebraic core: substituting `λ = x` into a `y`-polynomial with
`λ`-polynomial coefficients (outer variable `y`, coefficients in `K[λ]`) gives zero exactly when
every `λ`-coefficient vanishes at `x`, together with the finite-family and the existential forms.

Note on the literal form `f.eval x`: Mathlib's `Polynomial.eval (x : R) (p : R[X]) : R` requires
the evaluation point to have the coefficient type, so with `R = K[λ]` the point would have to be a
`λ`-polynomial, while `(f.coeff m).eval x` needs `x : K`.  The mathematically intended operation
"substitute `λ = x` in every coefficient" is `Polynomial.map` along `Polynomial.evalRingHom x`, and
that is what is proved.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

namespace Q1Paper.PaperV

variable {K : Type*} [Field K]

/-- Applying `evalRingHom x` is ordinary evaluation at `x`. -/
theorem evalRingHom_apply (x : K) (q : Polynomial K) :
    (Polynomial.evalRingHom x) q = q.eval x := by
  simp

/-- **Proposition 15 (single polynomial).** The `y`-polynomial obtained by substituting `λ = x`
into the coefficients is zero iff every `λ`-coefficient vanishes at `x`. -/
theorem eval_zero_iff_coeff_eval_zero
    (f : Polynomial (Polynomial K)) (x : K) :
    f.map (Polynomial.evalRingHom x) = 0 ↔ ∀ m, (f.coeff m).eval x = 0 := by
  rw [Polynomial.ext_iff]
  constructor
  · intro h m
    have h' := h m
    rwa [Polynomial.coeff_map, Polynomial.coeff_zero, evalRingHom_apply] at h'
  · intro h m
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, evalRingHom_apply]
    exact h m

/-- **Proposition 15 (finite family).** Pointwise at a fixed `λ₀ = x`. -/
theorem forall_eval_zero_iff_forall_coeff {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (Polynomial K)) (x : K) :
    (∀ I ∈ s, (f I).map (Polynomial.evalRingHom x) = 0) ↔
      ∀ I ∈ s, ∀ m, ((f I).coeff m).eval x = 0 := by
  simp only [eval_zero_iff_coeff_eval_zero]

/-- **Proposition 15 (existential form).** The `∃ λ₀` of the paper's statement. -/
theorem exists_forall_eval_zero_iff_exists_forall_coeff {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (Polynomial K)) :
    (∃ x : K, ∀ I ∈ s, (f I).map (Polynomial.evalRingHom x) = 0) ↔
      ∃ x : K, ∀ I ∈ s, ∀ m, ((f I).coeff m).eval x = 0 := by
  simp only [eval_zero_iff_coeff_eval_zero]

end Q1Paper.PaperV
