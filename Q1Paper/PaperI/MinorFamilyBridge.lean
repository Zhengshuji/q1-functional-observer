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

open Matrix Polynomial

variable {K : Type*} [Field K]

/-- **Determinant under row/column permutations** (over any commutative ring, so
that it applies to polynomial matrices). -/
theorem det_submatrix_perm {R : Type*} [CommRing R] {ω : ℕ} (σ τ : Equiv.Perm (Fin ω))
    (M : Matrix (Fin ω) (Fin ω) R) :
    (M.submatrix σ τ).det =
      (Equiv.Perm.sign σ : R) * (Equiv.Perm.sign τ : R) * M.det := by
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


noncomputable def embOfFinset {α : Type*} [LinearOrder α] {ω : ℕ}
    (s : Finset α) (h : s.card = ω) : Fin ω → α :=
  s.orderEmbOfFin h

/-- The image of an injection, as a plain `Finset`. -/
def imageFinset {q ω : ℕ} (ρ : Fin ω → Fin q) : Finset (Fin q) :=
  Finset.univ.image ρ

/-- The cardinality of the image. -/
theorem imageFinset_card {q ω : ℕ} (ρ : Fin ω → Fin q) (hρ : Function.Injective ρ) :
    (imageFinset ρ).card = ω := by
  rw [imageFinset, Finset.card_image_of_injective Finset.univ hρ, Finset.card_univ]
  simp

/-- The bijection `Fin ω ≃ ↥(image of ρ)`. -/
noncomputable def imageEquivFinset {q ω : ℕ} (ρ : Fin ω → Fin q)
    (hρ : Function.Injective ρ) : Fin ω ≃ ↥(imageFinset ρ) :=
  Equiv.ofBijective (fun i => ⟨ρ i, by simp [imageFinset]⟩)
    ⟨fun i j h => hρ (Subtype.ext_iff.mp h),
     fun x => by
       obtain ⟨i, hi⟩ := Finset.mem_image.mp x.2
       exact ⟨i, Subtype.ext hi.2⟩⟩

/-- The permutation reordering `Fin ω` by the increasing enumeration of the image. -/
noncomputable def permOfImage {q ω : ℕ} (ρ : Fin ω → Fin q) (hρ : Function.Injective ρ) :
    Equiv.Perm (Fin ω) :=
  (imageEquivFinset ρ hρ).trans
    (Finset.orderIsoOfFin (imageFinset ρ) (imageFinset_card ρ hρ)).symm.toEquiv

/-- The defining property of the reordering permutation. -/
theorem embOfFinset_permOfImage {q ω : ℕ} (ρ : Fin ω → Fin q) (hρ : Function.Injective ρ)
    (i : Fin ω) :
    embOfFinset (imageFinset ρ) (imageFinset_card ρ hρ) (permOfImage ρ hρ i) = ρ i := by
  unfold embOfFinset permOfImage
  rw [← Finset.coe_orderIsoOfFin_apply]
  rw [Equiv.trans_apply]
  change ↑((Finset.orderIsoOfFin (imageFinset ρ) (imageFinset_card ρ hρ))
      ((Finset.orderIsoOfFin (imageFinset ρ) (imageFinset_card ρ hρ)).symm
        (imageEquivFinset ρ hρ i))) = ρ i
  rw [OrderIso.apply_symm_apply]
  rfl

/-- **Determinant of a submatrix up to row/column permutations.** -/
theorem det_submatrix_comp {q ℓ ω : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X])
    (f : Fin ω → Fin q) (g : Fin ω → Fin ℓ) (σ τ : Equiv.Perm (Fin ω))
    (ρ : Fin ω → Fin q) (κ : Fin ω → Fin ℓ)
    (hf : ∀ i, f (σ i) = ρ i) (hg : ∀ j, g (τ j) = κ j) :
    (P.submatrix ρ κ).det =
      (Equiv.Perm.sign σ : K[X]) * (Equiv.Perm.sign τ : K[X]) * (P.submatrix f g).det := by
  have hsub : P.submatrix ρ κ = (P.submatrix f g).submatrix σ τ := by
    funext i j
    show P (ρ i) (κ j) = P (f (σ i)) (g (τ j))
    rw [hf i, hg j]
  calc (P.submatrix ρ κ).det
      = ((P.submatrix f g).submatrix σ τ).det := by rw [hsub]
    _ = (Equiv.Perm.sign σ : K[X]) * (Equiv.Perm.sign τ : K[X]) * (P.submatrix f g).det :=
        det_submatrix_perm σ τ _

/-- **Single-minor sign relation.**  The minor indexed by two injections equals
the product of the two reordering signs times the minor indexed by the
increasing enumerations of their images. -/
theorem maximalMinor_injective_eq_signed_image {q ℓ : ℕ}
    (P : Matrix (Fin q) (Fin ℓ) K[X]) {ω : ℕ}
    (ρ : Fin ω → Fin q) (hρ : Function.Injective ρ)
    (κ : Fin ω → Fin ℓ) (hκ : Function.Injective κ) :
    maximalMinor P ρ κ =
      (Equiv.Perm.sign (permOfImage ρ hρ) : K[X]) *
        (Equiv.Perm.sign (permOfImage κ hκ) : K[X]) *
        maximalMinor P (embOfFinset (imageFinset ρ) (imageFinset_card ρ hρ))
          (embOfFinset (imageFinset κ) (imageFinset_card κ hκ)) := by
  unfold maximalMinor
  exact det_submatrix_comp P _ _ _ _ ρ κ
    (embOfFinset_permOfImage ρ hρ) (embOfFinset_permOfImage κ hκ)

end Q1Paper.PaperI


