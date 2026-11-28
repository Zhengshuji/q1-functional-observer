import Mathlib
import Q1Paper.PaperV.FamilyGcd
import Q1Paper.PaperV.MinorEval
import Q1Paper.PaperV.RankMinor

/-!
Q1Paper/PaperV/Criterion.lean

§III, Theorem 4 in Lean form (sufficiency direction).

Chain assembled here:

* `FamilyGcd.exists_eval_ne_zero_of_isUnit_gcd` : a family with unit gcd has, at every point, a member
  that does not vanish there;
* `MinorEval.eval_det_submatrix` : evaluating a minor commutes with evaluating the matrix;
* `RankMinor.le_rank_of_det_submatrix_ne_zero` : a nonzero minor forces the rank up.

Conclusion: if the family of `d × d` minors of a polynomial matrix has unit gcd, then at every
`x : K` the evaluated matrix has rank at least `d`. With the paper's standing hypothesis
`rank H = d'` (row-full-rank) the reverse inequality is automatic, which is exactly the criterion.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

set_option maxHeartbeats 800000

-- `Finset.gcd` on `Polynomial K` needs `NormalizedGCDMonoid (Polynomial K)`, which for an abstract
-- field is derived through an instance that requires decidable equality.
attribute [local instance] Classical.decEq

namespace Q1Paper.PaperV

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- The `d`-minor attached to a pair of row and column selections. -/
noncomputable def minor {q k d : ℕ} (M : Matrix (Fin q) (Fin k) (Polynomial K))
    (p : (Fin d → Fin q) × (Fin d → Fin k)) : Polynomial K :=
  (M.submatrix p.1 p.2).det

/-- **Theorem 4, sufficiency.** If the family of `d`-minors of a polynomial matrix has unit gcd, then
the matrix obtained by evaluating at any `x` has rank at least `d`. -/
theorem le_rank_map_of_isUnit_gcd_minor {q k d : ℕ}
    (M : Matrix (Fin q) (Fin k) (Polynomial K))
    (s : Finset ((Fin d → Fin q) × (Fin d → Fin k)))
    (hne : ∀ p ∈ s, minor M p ≠ 0)
    (hgcd : IsUnit (s.gcd (fun p => minor M p))) (x : K) :
    d ≤ (M.map (Polynomial.evalRingHom x)).rank := by
  obtain ⟨p, hp, hpx⟩ :=
    exists_eval_ne_zero_of_isUnit_gcd s (fun p => minor M p) hne hgcd x
  have hdet : ((M.map (Polynomial.evalRingHom x)).submatrix p.1 p.2).det ≠ 0 := by
    rw [← eval_det_submatrix M x p.1 p.2]
    exact hpx
  exact le_rank_of_det_submatrix_ne_zero _ p.1 p.2 hdet

end Q1Paper.PaperV
