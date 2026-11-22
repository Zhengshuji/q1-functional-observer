/-
Q1Paper/PaperI/RowSpanBridge.lean

D1 step 6: the two window matrices have the same row space.  This closes the
bridge between the injective-map-indexed minor family (Claim 11/12) and the
subset-indexed family (Section III-D).
-/

import Q1Paper.PaperI.GramInj

open Matrix Polynomial

namespace Q1Paper.PaperI

variable {K : Type*} [Field K]

/-- The row span of a matrix. -/
def rowSpan {ι : Type*} {n : ℕ} (Z : Matrix ι (Fin n) K) : Submodule K (Fin n → K) :=
  Submodule.span K (Set.range Z)

/-- An injective index pair with prescribed image: the increasing embeddings. -/
noncomputable def preimagePair {q ℓ ω : ℕ}
    (s : Set.powersetCard (Fin q) ω × Set.powersetCard (Fin ℓ) ω) : Inj q ω × Inj ℓ ω :=
  (⟨rowEmb s.1, ((s.1 : Finset (Fin q)).orderEmbOfFin (Set.powersetCard.card_eq s.1)).injective⟩,
    ⟨colEmb s.2, ((s.2 : Finset (Fin ℓ)).orderEmbOfFin (Set.powersetCard.card_eq s.2)).injective⟩)

/-- The chosen preimage has the prescribed image. -/
theorem imagePair_preimagePair {q ℓ ω : ℕ}
    (s : Set.powersetCard (Fin q) ω × Set.powersetCard (Fin ℓ) ω) :
    imagePair (preimagePair s) = s := by
  apply Prod.ext
  · apply Subtype.ext
    show imageFinset (rowEmb s.1) = (s.1 : Finset (Fin q))
    rw [imageFinset, rowEmb, Finset.image_orderEmbOfFin_univ]
  · apply Subtype.ext
    show imageFinset (colEmb s.2) = (s.2 : Finset (Fin ℓ))
    rw [imageFinset, colEmb, Finset.image_orderEmbOfFin_univ]

/-- **Row-space equality** of the two window matrices (D1 step 6). -/
theorem rowSpan_windowInj_eq {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X]) (ω : ℕ) :
    rowSpan (windowInj P ω) = rowSpan (windowSub P ω) := by
  classical
  have hWin : ∀ (x : Inj q ω × Inj ℓ ω) (j : Fin ω),
      windowInj P ω (x, j) = pairSign (K := K) x • windowSub P ω (imagePair x, j) := by
    intro x j
    funext t
    exact windowRow_inj_eq_sign_mul P ω x j t
  have hWout : ∀ (s : Set.powersetCard (Fin q) ω × Set.powersetCard (Fin ℓ) ω) (j : Fin ω),
      windowSub P ω (s, j) = pairSign (K := K) (preimagePair s) • windowInj P ω (preimagePair s, j) := by
    intro s j
    have h1 : windowInj P ω (preimagePair s, j) =
        pairSign (K := K) (preimagePair s) • windowSub P ω (s, j) := by
      rw [hWin (preimagePair s) j, imagePair_preimagePair]
    rw [h1, smul_smul, ← pow_two, pairSign_sq (K := K), one_smul]
  apply le_antisymm
  · rw [rowSpan, Submodule.span_le]
    rintro _ ⟨⟨x, j⟩, rfl⟩
    rw [hWin x j]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(imagePair x, j), rfl⟩)
  · rw [rowSpan, Submodule.span_le]
    rintro _ ⟨⟨s, j⟩, rfl⟩
    rw [hWout s j]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(preimagePair s, j), rfl⟩)

end Q1Paper.PaperI
