import Mathlib

/-!
Q1Paper/PaperV/MinorEval.lean

§III, the evaluation bridge for minors.

Paper usage: the `d'`-minors of the pencil `λH − K` are polynomials in `λ`; evaluating such a minor
at `λ = x` is the same as taking the minor of the evaluated matrix. This is what lets a statement
about the polynomial matrix be read off pointwise, and it is the bridge between the coefficient
description of Proposition 11 and the rank description of the criterion.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

set_option maxHeartbeats 800000

namespace Q1Paper.PaperV

/-- Evaluation of a minor equals the minor of the evaluation. -/
theorem eval_det_submatrix {K : Type*} [Field K] {q k d : ℕ}
    (M : Matrix (Fin q) (Fin k) (Polynomial K)) (x : K)
    (e : Fin d → Fin q) (f : Fin d → Fin k) :
    Polynomial.eval x ((M.submatrix e f).det) =
      ((M.map (Polynomial.evalRingHom x)).submatrix e f).det := by
  show (Polynomial.evalRingHom x) ((M.submatrix e f).det) = _
  rw [RingHom.map_det]
  show ((M.submatrix e f).map (Polynomial.evalRingHom x)).det =
    ((M.map (Polynomial.evalRingHom x)).submatrix e f).det
  rw [← Matrix.submatrix_map]

end Q1Paper.PaperV
