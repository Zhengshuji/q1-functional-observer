import Mathlib

/-!
Q1Paper/PaperV/KerRank.lean

§IV, Proposition 18 — the linear-algebra kernel of **column dependence**.

Paper statement: if a subspace `A` of the column space satisfies `A ≤ ker P(λ₀)` at every point of
the fibre and `dim A > k - d'`, then `rank P(λ₀) < d'` and `(5b)` fails everywhere.  Proposition 14
(column drop) is the case where `A` is spanned by coordinate vectors.

The kernel proved here: a linear map with a large subspace inside its kernel has small rank.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

namespace Q1Paper.PaperV

open Module

/-- **Proposition 18 (rank kernel).** If `f : K^k → K^q` has a subspace `A ≤ ker f` with
`k - dim A < d`, then `rank f < d`. -/
theorem rank_lt_of_le_ker {K : Type*} [Field K] {k q d : ℕ}
    (f : (Fin k → K) →ₗ[K] (Fin q → K)) (A : Submodule K (Fin k → K))
    (hA : A ≤ LinearMap.ker f) (hdim : k - Module.finrank K A < d) :
    Module.finrank K f.range < d := by
  have hmono : Module.finrank K A ≤ Module.finrank K (LinearMap.ker f) :=
    Submodule.finrank_mono hA
  have hrn : Module.finrank K f.range + Module.finrank K (LinearMap.ker f) = k := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    simpa using h
  have h1 : k - Module.finrank K (LinearMap.ker f) ≤ k - Module.finrank K A :=
    Nat.sub_le_sub_left hmono k
  have h2 : k - Module.finrank K (LinearMap.ker f) = Module.finrank K f.range := by
    omega
  rw [h2] at h1
  exact lt_of_le_of_lt h1 hdim

/-- **Proposition 18 for a matrix.** `Matrix.rank M` is `finrank K (range M.mulVecLin)`, so the
matrix form is the linear-map form applied to `M.mulVecLin`. -/
theorem matrix_rank_lt_of_le_ker {K : Type*} [Field K] {k q d : ℕ}
    (M : Matrix (Fin q) (Fin k) K) (A : Submodule K (Fin k → K))
    (hA : A ≤ LinearMap.ker M.mulVecLin) (hdim : k - Module.finrank K A < d) :
    M.rank < d :=
  rank_lt_of_le_ker M.mulVecLin A hA hdim

end Q1Paper.PaperV
