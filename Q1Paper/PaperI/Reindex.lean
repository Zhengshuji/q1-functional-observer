import Q1Paper.PaperI.ChartComplex

/-!
# Row reindexing preserves the raw conditions

`DEC C A L0 r` is `∃ R, let L := fromRows L0 R, rawAlgebraic … ∧ rawSpectral …`, and Mathlib's
`fromRows` gives `L` the row type `Fin r0 ⊕ Fin r`.  `PhiPoint` is indexed by `Fin q`, because its
Gram field needs `minorFamily`, which wants `Fin` indices.

So linking the chart point to `DEC` needs one transfer: the raw conditions are invariant under a
row bijection.  `rawAlgebraic` is a rank equality of a four-block stack, so the bijection has to be
assembled blockwise; then `Matrix.rank_submatrix` (a `@[simp]` invariance) finishes it.
-/

namespace Q1Paper.PaperI.Reindex

open Q1Paper Q1Subspace Q1Paper.PaperI

variable {K : Type*} [Field K]
variable {p q q' n : Type*} [Fintype p] [Fintype q] [Fintype q'] [Fintype n]

/-- The block bijection induced by a row bijection `e : q' ≃ q` on the four-block stack. -/
def blockEquiv (e : q' ≃ q) (p : Type*) :
    q' ⊕ (q' ⊕ (p ⊕ p)) ≃ q ⊕ (q ⊕ (p ⊕ p)) :=
  Equiv.sumCongr e (Equiv.sumCongr e (Equiv.refl (p ⊕ p)))

/-- **`rawAlgebraic` is invariant under a row bijection.** -/
theorem rawAlgebraic_submatrix (C CA : Matrix p n K) (L LA : Matrix q n K) (e : q' ≃ q) :
    rawAlgebraic C CA (L.submatrix e id) (LA.submatrix e id) ↔
      rawAlgebraic C CA L LA := by
  have hstack : Matrix.fromRows (LA.submatrix e id)
        (Matrix.fromRows (L.submatrix e id) (Matrix.fromRows CA C)) =
      (Matrix.fromRows LA (Matrix.fromRows L (Matrix.fromRows CA C))).submatrix
        (blockEquiv e p) (Equiv.refl n) := by
    ext i j
    rcases i with i | i | i | i <;> rfl
  have hstack2 : Matrix.fromRows (L.submatrix e id) (Matrix.fromRows CA C) =
      (Matrix.fromRows L (Matrix.fromRows CA C)).submatrix
        (Equiv.sumCongr e (Equiv.refl (p ⊕ p))) (Equiv.refl n) := by
    ext i j
    rcases i with i | i | i <;> rfl
  unfold rawAlgebraic
  rw [hstack, hstack2,
    Matrix.rank_submatrix (em := blockEquiv e p) (en := Equiv.refl n),
    Matrix.rank_submatrix (em := Equiv.sumCongr e (Equiv.refl (p ⊕ p))) (en := Equiv.refl n)]

end Q1Paper.PaperI.Reindex
