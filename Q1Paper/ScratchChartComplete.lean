import Q1Paper.PaperI.MainTheorems

/-!
# Chart completeness, step 1

The external review of the algorithm verification asks, before anything else, for the
**equivalence between the original feasibility problem and the finite chart system** of
`eq:phi`.  The forward direction (`Feasible L → a Φ-point`) decomposes into small steps; this
file proves the first and most specific one.

With `N` a matrix whose columns lie in `ker[C; CA]` (so `C N = 0` and `C A N = 0`), `H = L N`,
`H_A = L A N`, the paper's `(5a)` — in row-space form
`row[LA; L; CA; C] = row[L; CA; C]` — implies

  `row(H_A) ≤ row(H)`.

This is exactly what lets **one** matrix `B` serve both `H = X B` and `H_A = G B` in `eq:phi`
(items (iii) and (iv)); without it the two factorizations would need different `B`.

The proof is the paper's one-liner: `(5a)` gives `row(LA) ≤ row[L; CA; C]`; right-multiplying by
`N` turns each row space into its image under `vecMulLinear N`, and `[L; CA; C] * N` is
`[H; 0; 0]` because `N` annihilates `C` and `C A`.
-/

namespace Q1Paper.ScratchChartComplete

open Q1Paper Q1Subspace

variable {K : Type*} [Field K]
variable {p q n k : ℕ}

/-- **Chart completeness, step 1.**  If `N` annihilates `C` and `C A`, and `(5a)` holds in
row-space form, then `row(L A N) ≤ row(L N)`. -/
theorem row_LA_mul_le_row_L_mul (A : Matrix (Fin n) (Fin n) K) (C : Matrix (Fin p) (Fin n) K)
    (L : Matrix (Fin q) (Fin n) K) (N : Matrix (Fin n) (Fin k) K)
    (hCN : C * N = 0) (hCAN : C * A * N = 0)
    (h5a : rowSpace (Matrix.fromRows (L * A) (Matrix.fromRows L (Matrix.fromRows (C * A) C)))
        = rowSpace (Matrix.fromRows L (Matrix.fromRows (C * A) C))) :
    rowSpace (L * A * N) ≤ rowSpace (L * N) := by
  -- (5a) gives `row(L A) ≤ row[L; CA; C]`
  have hle : rowSpace (L * A) ≤ rowSpace (Matrix.fromRows L (Matrix.fromRows (C * A) C)) := by
    calc rowSpace (L * A)
        ≤ rowSpace (L * A) ⊔ rowSpace (Matrix.fromRows L (Matrix.fromRows (C * A) C)) :=
          le_sup_left
      _ = rowSpace (Matrix.fromRows (L * A) (Matrix.fromRows L (Matrix.fromRows (C * A) C))) :=
          (rowSpace_fromRows _ _).symm
      _ = rowSpace (Matrix.fromRows L (Matrix.fromRows (C * A) C)) := h5a
  -- push the inclusion through right multiplication by `N`
  have hmap := Submodule.map_mono (f := Matrix.vecMulLinear N) hle
  rw [← rowSpace_mul_eq_map, ← rowSpace_mul_eq_map] at hmap
  -- `[L; CA; C] * N = [L N; (CA) N; C N] = [H; 0; 0]`, whose row space is `row(H)`
  rw [Matrix.fromRows_mul, Matrix.fromRows_mul, rowSpace_fromRows, rowSpace_fromRows,
    hCN, hCAN] at hmap
  have hzero : rowSpace (0 : Matrix (Fin p) (Fin k) K) = ⊥ := by
    rw [Q1Subspace.rowSpace, Submodule.span_eq_bot]
    rintro _ ⟨i, rfl⟩
    rfl
  rw [hzero] at hmap
  simpa using hmap

end Q1Paper.ScratchChartComplete
