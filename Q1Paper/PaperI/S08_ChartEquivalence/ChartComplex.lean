import Q1Paper.PaperI.S08_ChartEquivalence.ChartComplete
import Q1Paper.PaperI.S08_ChartEquivalence.FromRowsMap

/-!
# Complexification and the complex-λ spectral condition

The paper's condition (5b) quantifies over `ℂ`, while the Lean `DEC` uses `rawSpectral`, which
quantifies over the base field.  The implication that holds — and that the chart argument needs —
is **complex implies real**: specialise `z = ↑λ`, push the entrywise map through the four-block
stack, and use that complexification preserves the rank.

Two interface lemmas make that possible:

* `rank_map_ofReal_sum`: rank is preserved by complexification for a `Sum`-indexed matrix (the
  four-block stack).  Rather than reprove rank preservation under a field extension, reindex the
  rows to `Fin` with `Fintype.equivFin`, use the `@[simp]` invariance `Matrix.rank_submatrix`, and
  apply the existing `rank_map_ofReal`.
* `fromRows_map` (in `PaperI/FromRowsMap.lean`): `fromRows` commutes with an entrywise map.
-/

namespace Q1Paper.PaperI.ChartComplex

open Q1Paper Q1Subspace Q1Paper.PaperI Q1Paper.PaperI.FromRowsMap

/-- The row index of the four-block stack `[·; ·; CA; C]`. -/
abbrev RowIdx (q p : ℕ) := Fin q ⊕ (Fin p ⊕ Fin p)

/-- **Complexification preserves the rank of a `Sum`-indexed matrix.** -/
theorem rank_map_ofReal_sum {q p n : ℕ} (M : Matrix (RowIdx q p) (Fin n) ℝ) :
    (M.map (algebraMap ℝ ℂ)).rank = M.rank := by
  let e : Fin (Fintype.card (RowIdx q p)) ≃ RowIdx q p := (Fintype.equivFin _).symm
  let N : Matrix (Fin (Fintype.card (RowIdx q p))) (Fin n) ℝ := M.submatrix e (Equiv.refl _)
  have hmap : (M.map (algebraMap ℝ ℂ)).submatrix e (Equiv.refl _) =
      N.map (algebraMap ℝ ℂ) := by
    ext i j
    rfl
  calc (M.map (algebraMap ℝ ℂ)).rank
      = ((M.map (algebraMap ℝ ℂ)).submatrix e (Equiv.refl _)).rank := by
          rw [Matrix.rank_submatrix]
    _ = (N.map (algebraMap ℝ ℂ)).rank := by rw [hmap]
    _ = N.rank := rank_map_ofReal N
    _ = M.rank := by rw [Matrix.rank_submatrix]

/-- The paper's spectral condition for real data, quantified over `ℂ`. -/
def spectralComplex {p q n : ℕ}
    (C CA : Matrix (Fin p) (Fin n) ℝ) (L LA : Matrix (Fin q) (Fin n) ℝ) : Prop :=
  ∀ z : ℂ,
    (Matrix.fromRows (z • L.map (algebraMap ℝ ℂ) - LA.map (algebraMap ℝ ℂ))
        (Matrix.fromRows (CA.map (algebraMap ℝ ℂ)) (C.map (algebraMap ℝ ℂ)))).rank =
      (Matrix.fromRows (L.map (algebraMap ℝ ℂ))
        (Matrix.fromRows (CA.map (algebraMap ℝ ℂ)) (C.map (algebraMap ℝ ℂ)))).rank

/-- **Complex is stronger than real**: the complex-λ condition implies `rawSpectral`. -/
theorem complex_spectral_implies_real {p q n : ℕ}
    (C CA : Matrix (Fin p) (Fin n) ℝ) (L LA : Matrix (Fin q) (Fin n) ℝ)
    (h : spectralComplex C CA L LA) : rawSpectral C CA L LA := by
  intro lam
  have hspec := h (algebraMap ℝ ℂ lam)
  have hscalar : ((algebraMap ℝ ℂ lam) • L.map (algebraMap ℝ ℂ) - LA.map (algebraMap ℝ ℂ)) =
      (lam • L - LA).map (algebraMap ℝ ℂ) := by
    ext i j
    simp [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply]
  have e1 : Matrix.fromRows ((algebraMap ℝ ℂ lam) • L.map (algebraMap ℝ ℂ) -
        LA.map (algebraMap ℝ ℂ))
        (Matrix.fromRows (CA.map (algebraMap ℝ ℂ)) (C.map (algebraMap ℝ ℂ)))
      = (Matrix.fromRows (lam • L - LA) (Matrix.fromRows CA C)).map (algebraMap ℝ ℂ) := by
    rw [fromRows_map, fromRows_map, hscalar]
  have e2 : Matrix.fromRows (L.map (algebraMap ℝ ℂ))
        (Matrix.fromRows (CA.map (algebraMap ℝ ℂ)) (C.map (algebraMap ℝ ℂ)))
      = (Matrix.fromRows L (Matrix.fromRows CA C)).map (algebraMap ℝ ℂ) := by
    rw [fromRows_map, fromRows_map]
  rw [e1, e2, rank_map_ofReal_sum, rank_map_ofReal_sum] at hspec
  exact hspec

end Q1Paper.PaperI.ChartComplex
