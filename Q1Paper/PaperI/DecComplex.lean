import Q1Paper.PaperI.ChartComplex
import Q1Paper.PaperI.Soundness

/-!
# `complexDEC`: the complex-λ decision problem

A second reader's verdict: the paper's Algorithm 1 decides the **complex**-λ version, and the
real-λ `DEC` can only be an auxiliary definition — the Gram certificate (`claim11_iff_gram`)
characterises the complex condition, so completeness has no chance for the real one.

## Why the definition failed five times

The error pointed at `L * A` inside the **second** conjunct.  The cause was mine: `rawAlgebraic` is
polymorphic in its index **types** (`{p q n : Type*}`), but I had declared `spectralComplexRaw` with
`{p q n : ℕ}`, i.e. `Fin q` indices.  `DEC`'s free block has the row type `Fin r0 ⊕ Fin r`, which is
**not** of the form `Fin q`, so the second conjunct could never accept it, while the first could.
Indexing by types fixes it — and the same generalisation is needed for the rank lemma.
-/

namespace Q1Paper.PaperI.DecComplex

open Q1Paper Q1Subspace Q1Paper.PaperI Q1Paper.PaperI.FromRowsMap

/-- **Complexification preserves the rank, for any finite index types.**  Reindex to `Fin`, use
`rank_map_ofReal`, reindex back. -/
theorem rank_map_ofReal_any {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) :
    (M.map (algebraMap ℝ ℂ)).rank = M.rank := by
  let em : m ≃ Fin (Fintype.card m) := Fintype.equivFin m
  let en : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  have hmap : (M.map (algebraMap ℝ ℂ)).submatrix em.symm en.symm =
      (M.submatrix em.symm en.symm).map (algebraMap ℝ ℂ) := by
    ext i j
    rfl
  calc (M.map (algebraMap ℝ ℂ)).rank
      = ((M.map (algebraMap ℝ ℂ)).submatrix em.symm en.symm).rank := by
          rw [Matrix.rank_submatrix (em := em.symm) (en := en.symm)]
    _ = ((M.submatrix em.symm en.symm).map (algebraMap ℝ ℂ)).rank := by rw [hmap]
    _ = (M.submatrix em.symm en.symm).rank := rank_map_ofReal _
    _ = M.rank := by rw [Matrix.rank_submatrix (em := em.symm) (en := en.symm)]

/-- **The paper's spectral condition**: the complexified data satisfy `(5b)` over `ℂ`.  Indexed by
**types**, like `rawAlgebraic`, so that it accepts the `Sum` row type of `[L₀; R]`. -/
def spectralComplexRaw {p q n : Type*} [Fintype p] [Fintype q] [Fintype n]
    (C CA : Matrix p n ℝ) (L LA : Matrix q n ℝ) : Prop :=
  Q1Paper.PaperI.rawSpectral (C.map (algebraMap ℝ ℂ)) (CA.map (algebraMap ℝ ℂ))
    (L.map (algebraMap ℝ ℂ)) (LA.map (algebraMap ℝ ℂ))

/-- **The complex-λ decision problem**, in exactly the shape of `DEC`. -/
def complexDEC {p r0 n : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (r : ℕ) : Prop :=
  ∃ R : Matrix (Fin r) (Fin n) ℝ,
    let L := Matrix.fromRows L0 R
    rawAlgebraic C (C * A) L (L * A) ∧ spectralComplexRaw C (C * A) L (L * A)

/-- **Complex is stronger than real**, in full generality. -/
theorem spectralComplex_implies_raw {p q n : Type*} [Fintype p] [Fintype q] [Fintype n]
    (C CA : Matrix p n ℝ) (L LA : Matrix q n ℝ) (h : spectralComplexRaw C CA L LA) :
    rawSpectral C CA L LA := by
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
  rw [e1, e2] at hspec
  simp only [rank_map_ofReal_any] at hspec
  exact hspec

/-- **The only relation that holds between the two versions**: complex implies real. -/
theorem dec_of_complexDEC {p r0 n : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (r : ℕ) (h : complexDEC C A L0 r) :
    DEC C A L0 r := by
  obtain ⟨R, h1, h2⟩ := h
  exact ⟨R, h1, spectralComplex_implies_raw C (C * A) _ _ h2⟩

end Q1Paper.PaperI.DecComplex
