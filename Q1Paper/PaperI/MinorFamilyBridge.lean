/-
Q1Paper/PaperI/MinorFamilyBridge.lean

D1 bridge between the two index families of maximal minors:

* `minorFamily` (Claim 11/12): indexed by pairs of *injective maps*
  `Fin ω → Fin q` and `Fin ω → Fin k`;
* `windowMinorFamily` (§III-D): indexed by pairs of *subsets*
  `Set.powersetCard (Fin q) ω × Set.powersetCard (Fin k) ω`.

Each subset pair occurs in the injective family exactly `(ω!)²` times, with the
sign of the reordering; hence the two window matrices have the same row space and
Gram matrices differing by the positive factor `(ω!)²`.

Contents so far:
* `det_submatrix_perm` : permuting rows and columns multiplies the determinant
  by the product of the two signs;
* `imageFin`           : the image of an injection as an `ω`-element subset;
* `imageEquiv`         : `Fin ω ≃ ↥(image of ρ)`;
* `permOfInjective`    : the permutation that reorders `Fin ω` by the image;
* `rowEmb_permOfInjective` : `rowEmb (imageFin ρ) (permOfInjective ρ i) = ρ i`.
-/

import Q1Paper.PaperI.GramCompression

namespace Q1Paper.PaperI

open Matrix

variable {K : Type*} [Field K]

/-- **Determinant under row/column permutations.** -/
theorem det_submatrix_perm {ω : ℕ} (σ τ : Equiv.Perm (Fin ω))
    (M : Matrix (Fin ω) (Fin ω) K) :
    (M.submatrix σ τ).det =
      (Equiv.Perm.sign σ : K) * (Equiv.Perm.sign τ : K) * M.det := by
  have h : M.submatrix σ τ = (M.submatrix σ id).submatrix id τ := by
    rw [Matrix.submatrix_submatrix]
    rfl
  rw [h, Matrix.det_permute', Matrix.det_permute]
  ring

variable {q ω : ℕ}

/-- The image of an injective map `Fin ω → Fin q`, as an `ω`-element subset. -/
noncomputable def imageFin (ρ : Fin ω → Fin q) (hρ : Function.Injective ρ) :
    Set.powersetCard (Fin q) ω :=
  ⟨Finset.univ.image ρ, by
    rw [Set.powersetCard.mem_iff, Finset.card_image_of_injective Finset.univ hρ,
      Finset.card_univ]
    simp⟩

/-- The bijection `Fin ω ≃ ↥(image of ρ)` induced by `ρ`. -/
noncomputable def imageEquiv (ρ : Fin ω → Fin q) (hρ : Function.Injective ρ) :
    Fin ω ≃ ↥((imageFin ρ hρ : Finset (Fin q))) :=
  Equiv.ofBijective (fun i => ⟨ρ i, by simp [imageFin]⟩)
    ⟨fun i j h => hρ (Subtype.ext_iff.mp h),
     fun x => by
       obtain ⟨i, hi⟩ := Finset.mem_image.mp x.2
       exact ⟨i, Subtype.ext hi.2⟩⟩

/-- The permutation of `Fin ω` that sends `i` to the position of `ρ i` in the
increasing enumeration of the image of `ρ`. -/
noncomputable def permOfInjective (ρ : Fin ω → Fin q) (hρ : Function.Injective ρ) :
    Equiv.Perm (Fin ω) :=
  (imageEquiv ρ hρ).trans
    (Finset.orderIsoOfFin (imageFin ρ hρ : Finset (Fin q))
      (Set.powersetCard.card_eq (imageFin ρ hρ))).symm.toEquiv

/-- The defining property of the reordering permutation. -/
theorem rowEmb_permOfInjective (ρ : Fin ω → Fin q) (hρ : Function.Injective ρ)
    (i : Fin ω) :
    rowEmb (imageFin ρ hρ) (permOfInjective ρ hρ i) = ρ i := by
  rw [rowEmb, ← Finset.coe_orderIsoOfFin_apply]
  have h : (Finset.orderIsoOfFin (imageFin ρ hρ : Finset (Fin q))
      (Set.powersetCard.card_eq (imageFin ρ hρ))) (permOfInjective ρ hρ i) =
      imageEquiv ρ hρ i := by
    unfold permOfInjective
    rw [Equiv.trans_apply]
    exact OrderIso.apply_symm_apply _ _
  rw [h]
  rfl

end Q1Paper.PaperI
