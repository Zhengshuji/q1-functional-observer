
import Q1Paper.PaperI.S03_Certificate.CauchyBinet
import Q1Paper.PaperI.S03_Certificate.MinorRank

/-!
Q1Paper/PaperI/S03_Certificate/GramKernel.lean

Section III-D, layers 1-2:

* `selectedCols P J`: the columns of `P : Matrix (Fin q) (Fin ℓ) K[X]` selected by
  `J : Set.powersetCard (Fin ℓ) ω`, enumerated in increasing order (`orderEmbOfFin`);
* `gramKernelEval ω P lam mu`: the Gram kernel evaluated at the parameters `lam`
  and `mu`, `∑_{|J| = ω} det (P(lam)_{:,J}ᵀ P(mu)_{:,J})`, with `J` ranging over
  the ω-element subsets of the ℓ columns (the paper's convention: `J` is a
  *column* set, `I` a *row* set).

Then `gramKernelEval_eq_double_sum`: the double maximal-minor expansion, obtained
by applying the ported square Cauchy–Binet (`Matrix.det_mul_eq_sum_det_submatrix`)
to each fixed column set `J`.
-/


namespace Q1Paper.PaperI

open Matrix Polynomial

variable {K : Type*} [Field K]

/-- The columns of `P` indexed by the subset `J`, in increasing order. -/
noncomputable def selectedCols {q ℓ ω : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X])
    (J : Set.powersetCard (Fin ℓ) ω) : Matrix (Fin q) (Fin ω) K[X] :=
  P.submatrix id ((J : Finset (Fin ℓ)).orderEmbOfFin (Set.powersetCard.card_eq J))

/-- The increasing embedding of a row subset `Fin ω → Fin q`. -/
noncomputable def rowEmb {q ω : ℕ} (I : Set.powersetCard (Fin q) ω) : Fin ω → Fin q :=
  (I : Finset (Fin q)).orderEmbOfFin (Set.powersetCard.card_eq I)

/-- The increasing embedding of a column subset `Fin ω → Fin ℓ`. -/
noncomputable def colEmb {ℓ ω : ℕ} (J : Set.powersetCard (Fin ℓ) ω) : Fin ω → Fin ℓ :=
  (J : Finset (Fin ℓ)).orderEmbOfFin (Set.powersetCard.card_eq J)

@[simp]
theorem selectedCols_apply {q ℓ ω : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X])
    (J : Set.powersetCard (Fin ℓ) ω) :
    selectedCols P J = P.submatrix id (colEmb J) := rfl

/-- The Gram kernel of the maximal minors, evaluated at `lam` and `mu`. -/
noncomputable def gramKernelEval {q ℓ : ℕ} (ω : ℕ) (P : Matrix (Fin q) (Fin ℓ) K[X])
    (lam mu : K) : K :=
  ∑ J : Set.powersetCard (Fin ℓ) ω,
    (((selectedCols P J).map (Polynomial.eval lam))ᵀ *
      ((selectedCols P J).map (Polynomial.eval mu))).det

/-- **Double maximal-minor expansion.**  The Gram kernel is the sum over all pairs
of row and column subsets of the products of the corresponding maximal minors. -/
theorem gramKernelEval_eq_double_sum {q ℓ : ℕ} (ω : ℕ) (P : Matrix (Fin q) (Fin ℓ) K[X])
    (lam mu : K) :
    gramKernelEval ω P lam mu =
      ∑ I : Set.powersetCard (Fin q) ω, ∑ J : Set.powersetCard (Fin ℓ) ω,
        (maximalMinor P (rowEmb I) (colEmb J)).eval lam *
          (maximalMinor P (rowEmb I) (colEmb J)).eval mu := by
  classical
  have hterm : ∀ J : Set.powersetCard (Fin ℓ) ω,
      (((selectedCols P J).map (Polynomial.eval lam))ᵀ *
        ((selectedCols P J).map (Polynomial.eval mu))).det
        = ∑ I : Set.powersetCard (Fin q) ω,
            (maximalMinor P (rowEmb I) (colEmb J)).eval lam *
              (maximalMinor P (rowEmb I) (colEmb J)).eval mu := by
    intro J
    rw [Matrix.det_mul_eq_sum_det_submatrix]
    refine Finset.sum_congr rfl fun I _ => ?_
    congr 1
    · -- the `lam` factor
      rw [← Matrix.transpose_submatrix, Matrix.det_transpose, Matrix.submatrix_map,
        eval_maximalMinor, selectedCols_apply, Matrix.submatrix_submatrix, Matrix.submatrix_map]
      rfl
    · -- the `mu` factor
      rw [Matrix.submatrix_map, eval_maximalMinor, selectedCols_apply,
        Matrix.submatrix_submatrix, Matrix.submatrix_map]
      rfl
  calc gramKernelEval ω P lam mu
      = ∑ J : Set.powersetCard (Fin ℓ) ω,
          ∑ I : Set.powersetCard (Fin q) ω,
            (maximalMinor P (rowEmb I) (colEmb J)).eval lam *
              (maximalMinor P (rowEmb I) (colEmb J)).eval mu := by
        unfold gramKernelEval
        exact Finset.sum_congr rfl fun J _ => hterm J
    _ = ∑ I : Set.powersetCard (Fin q) ω,
          ∑ J : Set.powersetCard (Fin ℓ) ω,
            (maximalMinor P (rowEmb I) (colEmb J)).eval lam *
              (maximalMinor P (rowEmb I) (colEmb J)).eval mu :=
        Finset.sum_comm

/-- Boundary case: if ω exceeds the number of columns, the Gram kernel vanishes
(the index type of ω-element column sets is empty). -/
theorem gramKernelEval_eq_zero_of_lt {q ℓ : ℕ} (ω : ℕ) (P : Matrix (Fin q) (Fin ℓ) K[X])
    (lam mu : K) (h : ℓ < ω) : gramKernelEval ω P lam mu = 0 := by
  classical
  haveI : IsEmpty (Set.powersetCard (Fin ℓ) ω) :=
    ⟨fun J => by
      have h1 : (J : Finset (Fin ℓ)).card ≤ ℓ := by
        simpa using Finset.card_le_univ (J : Finset (Fin ℓ))
      have h2 : (J : Finset (Fin ℓ)).card = ω := Set.powersetCard.card_eq J
      omega⟩
  simp [gramKernelEval]

end Q1Paper.PaperI

