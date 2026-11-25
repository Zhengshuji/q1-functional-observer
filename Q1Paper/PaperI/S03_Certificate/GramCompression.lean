
import Q1Paper.PaperI.S03_Certificate.GramCoefficients
import Q1Paper.Window

/-!
Q1Paper/PaperI/S03_Certificate/GramCompression.lean

Section III-D, last layer: the Gram matrix of the window matrix is the
compressed coefficient form.  With the minor family indexed by pairs of row and
column subsets and `Z` the window matrix of Claim 10, the `(t,t')` entry of
`Zᵀ Z` is the sum over the window shift `j` of the coefficient Gram form:

  `(Zᵀ Z)_{t,t'} = ∑_{j : Fin ω} (if j ≤ t and j ≤ t' then S_{t-j, t'-j} else 0)`.
-/


namespace Q1Paper.PaperI

open Matrix Polynomial

variable {K : Type*} [Field K]

/-- The family of maximal minors of `P`, indexed by pairs of row/column subsets. -/
noncomputable def windowMinorFamily {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X]) (ω : ℕ) :
    (Set.powersetCard (Fin q) ω × Set.powersetCard (Fin ℓ) ω) → K[X] :=
  fun i => maximalMinor P (rowEmb i.1) (colEmb i.2)

/-- **Window Gram entry identity.** -/
theorem windowGram_entry {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X]) (ω : ℕ)
    (t t' : Fin (2 * ω)) :
    ((Q1Paper.windowMatrix (windowMinorFamily P ω) ω)ᵀ *
      Q1Paper.windowMatrix (windowMinorFamily P ω) ω) t t' =
      ∑ j : Fin ω,
        if (j : ℕ) ≤ (t : ℕ) ∧ (j : ℕ) ≤ (t' : ℕ) then
          coeffGram P ω ((t : ℕ) - (j : ℕ)) ((t' : ℕ) - (j : ℕ))
        else 0 := by
  classical
  let Z : Matrix ((Set.powersetCard (Fin q) ω × Set.powersetCard (Fin ℓ) ω) × Fin ω)
      (Fin (2 * ω)) K := Q1Paper.windowMatrix (windowMinorFamily P ω) ω
  have hL : ((Q1Paper.windowMatrix (windowMinorFamily P ω) ω)ᵀ *
        Q1Paper.windowMatrix (windowMinorFamily P ω) ω) t t'
      = ∑ p : (Set.powersetCard (Fin q) ω × Set.powersetCard (Fin ℓ) ω) × Fin ω,
          Z p t * Z p t' := by
    rw [Matrix.mul_apply]
    rfl
  rw [hL]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : (j : ℕ) ≤ (t : ℕ)
  · by_cases h2 : (j : ℕ) ≤ (t' : ℕ)
    · rw [if_pos ⟨h1, h2⟩]
      have hsimp : ∀ i : Set.powersetCard (Fin q) ω × Set.powersetCard (Fin ℓ) ω,
          Z (i, j) t * Z (i, j) t'
            = minorCoeff P ω ((t : ℕ) - (j : ℕ)) i.1 i.2 *
              minorCoeff P ω ((t' : ℕ) - (j : ℕ)) i.1 i.2 := by
        intro i
        simp [Z, Q1Paper.windowMatrix, windowMinorFamily, minorCoeff, h1, h2]
      simp only [hsimp]
      rw [coeffGram, ← Finset.sum_product']
      simp
    · rw [if_neg (by omega)]
      simp [Z, Q1Paper.windowMatrix, windowMinorFamily, h2]
  · rw [if_neg (by omega)]
    simp [Z, Q1Paper.windowMatrix, windowMinorFamily, h1]

/-- The compressed coefficient matrix of the window Gram form. -/
noncomputable def compressedGram {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X]) (ω : ℕ) :
    Matrix (Fin (2 * ω)) (Fin (2 * ω)) K :=
  fun t t' => ∑ j : Fin ω,
    if (j : ℕ) ≤ (t : ℕ) ∧ (j : ℕ) ≤ (t' : ℕ) then
      coeffGram P ω ((t : ℕ) - (j : ℕ)) ((t' : ℕ) - (j : ℕ)) else 0

/-- **The window Gram matrix is the compressed coefficient matrix.** -/
theorem windowGram_eq_compressed {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X]) (ω : ℕ) :
    (Q1Paper.windowMatrix (windowMinorFamily P ω) ω)ᵀ *
      Q1Paper.windowMatrix (windowMinorFamily P ω) ω = compressedGram P ω := by
  ext t t'
  rw [windowGram_entry]
  rfl

end Q1Paper.PaperI

