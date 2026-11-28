import Mathlib
import Q1Paper.PaperV.Criterion
import Q1Paper.PaperV.Gauss

/-!
Q1Paper/PaperV/CriterionNecessity.lean

§III, Theorem 4's necessity direction in matrix form.

The chain `Necessity.lean` + `Gauss.lean` produces a common root of a family of
polynomials.  This file feeds the actual object of the paper into that chain: the
`d`-minors of a polynomial matrix `M` over `ℂ[t][λ]`.  If

* a monic `g ∈ ℂ(t)[λ]` of positive degree divides the image of every `d`-minor, and
* some `d`-minor has a nonzero constant `λ`-leading coefficient,

then at every fibre point `t0` there is a `λ = α` where the evaluated matrix has rank
strictly below `d`: the point is bad.

This is the bundling step: it connects `minor`, the root step and the Gauss step into one
statement about `M`, so Theorem 4's necessity no longer has to be assembled by hand.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

open Polynomial MvPolynomial

set_option maxHeartbeats 800000

namespace Q1Paper.PaperV

variable {σ : Type*}

/-- The `d`-minor of a polynomial matrix over the coordinate ring `ℂ[t]`. -/
noncomputable def minorR {q k d : ℕ}
    (M : Matrix (Fin q) (Fin k) (Polynomial (MvPolynomial σ ℂ)))
    (p : (Fin d → Fin q) × (Fin d → Fin k)) : Polynomial (MvPolynomial σ ℂ) :=
  (M.submatrix p.1 p.2).det

/-- **Theorem 4, necessity (matrix form).**  A positive-degree monic common divisor of the
`d`-minors over `ℂ(t)[λ]`, together with one minor of nonzero constant leading coefficient,
forces rank `< d` at some `λ` for every specialisation `t0`. -/
theorem rank_lt_of_gcd_pos
    {q k d : ℕ} (M : Matrix (Fin q) (Fin k) (Polynomial (MvPolynomial σ ℂ)))
    (g : Polynomial (FractionRing (MvPolynomial σ ℂ)))
    (hg : g.Monic) (hdeg : 1 ≤ g.natDegree)
    (hgdvd : ∀ p : (Fin d → Fin q) × (Fin d → Fin k),
      g ∣ (minorR M p).map (algebraMap (MvPolynomial σ ℂ)
        (FractionRing (MvPolynomial σ ℂ))))
    (p0 : (Fin d → Fin q) × (Fin d → Fin k)) (c0 : ℂ) (hc0 : c0 ≠ 0)
    (hlc0 : (minorR M p0).leadingCoeff = MvPolynomial.C c0)
    (t0 : σ → ℂ) :
    ∃ α : ℂ, (M.map (Polynomial.eval₂RingHom (MvPolynomial.eval t0) α)).rank < d := by
  classical
  -- the root produced by the specialisation + Gauss chain
  obtain ⟨α, hα⟩ :=
    exists_common_root_of_gcd_family (fun p => minorR M p) p0 c0 hc0 hlc0 g hg hdeg hgdvd t0
  refine ⟨α, ?_⟩
  -- assume the evaluated matrix has rank at least `d`
  by_contra hlt
  rw [not_lt] at hlt
  obtain ⟨e, f, hdet⟩ :=
    exists_submatrix_det_ne_zero_of_le_rank
      (M.map (Polynomial.eval₂RingHom (MvPolynomial.eval t0) α)) hlt
  -- its determinant is the evaluation of the corresponding minor
  have hdet_eq : ((M.map (Polynomial.eval₂RingHom (MvPolynomial.eval t0) α)).submatrix e f).det
      = Polynomial.eval₂RingHom (MvPolynomial.eval t0) α (minorR M (e, f)) := by
    rw [Matrix.submatrix_map]
    simpa [minorR] using
      (RingHom.map_det (Polynomial.eval₂RingHom (MvPolynomial.eval t0) α)
        (M.submatrix e f)).symm
  -- and that evaluation vanishes because `α` is a common root
  have hψ : Polynomial.eval₂RingHom (MvPolynomial.eval t0) α (minorR M (e, f)) = 0 := by
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_eval_map]
    exact hα (e, f)
  rw [hdet_eq, hψ] at hdet
  exact hdet rfl

end Q1Paper.PaperV
