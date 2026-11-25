import Q1Paper.PaperI.S08_ChartEquivalence.ReindexAlgebraic
/-!
# Row reindexing preserves the raw spectral condition

The companion of `rawAlgebraic_submatrix`.  Here the stack is only **two** blocks at the top level,
`[lam • L - LA; CA; C]` = `fromRows (lam • L - LA) (fromRows CA C)`, and `CA` is *not* reindexed —
only the free block is.  So the relevant bijection is `Equiv.sumCongr e (Equiv.refl (p ⊕ p))`, not
`blockEquiv`.  The one extra step over `rawAlgebraic_submatrix` is pushing `submatrix` through the
scalar multiplication and the subtraction.
-/

namespace Q1Paper.PaperI.ReindexSpectral

open Q1Paper Q1Subspace Q1Paper.PaperI Q1Paper.PaperI.ReindexAlgebraic

variable {K : Type*} [Field K]
variable {p q q' n : Type*} [Fintype p] [Fintype q] [Fintype q'] [Fintype n]

/-- **`rawSpectral` survives a row bijection**: if the reindexed data satisfy `(5b)`, so do the
original data. -/
theorem rawSpectral_submatrix (C CA : Matrix p n K) (L LA : Matrix q n K) (e : q' ≃ q)
    (h : rawSpectral C CA (L.submatrix e id) (LA.submatrix e id)) :
    rawSpectral C CA L LA := by
  intro lam
  have hspec := h lam
  have hsm : (lam • L.submatrix e id - LA.submatrix e id) =
      (lam • L - LA).submatrix e id := by
    ext i j
    simp [Matrix.sub_apply, Matrix.smul_apply]
  rw [hsm] at hspec
  have hstack1 : Matrix.fromRows ((lam • L - LA).submatrix e id) (Matrix.fromRows CA C) =
      (Matrix.fromRows (lam • L - LA) (Matrix.fromRows CA C)).submatrix
        (Equiv.sumCongr e (Equiv.refl (p ⊕ p))) (Equiv.refl n) := by
    ext i j
    rcases i with i | i | i <;> rfl
  have hstack2 : Matrix.fromRows (L.submatrix e id) (Matrix.fromRows CA C) =
      (Matrix.fromRows L (Matrix.fromRows CA C)).submatrix
        (Equiv.sumCongr e (Equiv.refl (p ⊕ p))) (Equiv.refl n) := by
    ext i j
    rcases i with i | i | i <;> rfl
  rw [hstack1, hstack2] at hspec
  simp only [Matrix.rank_submatrix] at hspec
  exact hspec

end Q1Paper.PaperI.ReindexSpectral
