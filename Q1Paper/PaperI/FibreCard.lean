/-
Q1Paper/PaperI/FibreCard.lean

Fibre cardinalities of the "image of an injection" map, used to turn a sum over
injective index maps into a sum over `ω`-element subsets (Claim 11/12, §III-D).

Contents:
* `injective_of_imageFinset_eq` : a map `Fin ω → Fin q` whose image has `ω`
  elements is injective;
* `card_fibre_imageFinset`      : that fibre has cardinality `ω!`;
* `card_fibre_imageFin`         : the same statement phrased with `imageFin`;
* `imagePair`, `card_fibre_pair`: the pair version, fibre cardinality `ω! * ω!`.
-/

import Q1Paper.PaperI.FibreSum

namespace Q1Paper.PaperI

/-! ### Single-index fibres -/

/-- **Injectivity from an image equality.**  A map `ρ : Fin ω → Fin q` whose
image inside `I` (with `I.card = ω`) already has `ω` elements is injective. -/
theorem injective_of_imageFinset_eq {q ω : ℕ} {I : Finset (Fin q)} (hI : I.card = ω)
    {ρ : Fin ω → Fin q} (hρ : imageFinset ρ = I) : Function.Injective ρ := by
  have h1 : (imageFinset ρ).card = (Finset.univ : Finset (Fin ω)).card := by
    rw [hρ, hI]
    simp
  have h2 : Set.InjOn ρ ↑(Finset.univ : Finset (Fin ω)) := Finset.card_image_iff.mp h1
  exact fun x y hxy => h2 (Finset.mem_univ x) (Finset.mem_univ y) hxy

/-- The map from the fibre of `imageFinset` over `I` to the bijections
`Fin ω ≃ ↥I` that it induces. -/
noncomputable def fibreToEquiv {q ω : ℕ} (I : Finset (Fin q)) (hI : I.card = ω)
    (ρ : {ρ : Fin ω → Fin q // imageFinset ρ = I}) : Fin ω ≃ ↥I :=
  Equiv.ofBijective
    (fun i => (⟨ρ.1 i, by
        have h : ρ.1 i ∈ imageFinset ρ.1 :=
          Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
        rwa [ρ.2] at h⟩ : ↥I))
    ⟨fun i j h => injective_of_imageFinset_eq hI ρ.2 (Subtype.ext_iff.mp h),
     fun x => by
       obtain ⟨i, -, hi⟩ :=
         Finset.mem_image.mp (show x.1 ∈ imageFinset ρ.1 from by rw [ρ.2]; exact x.2)
       exact ⟨i, Subtype.ext hi⟩⟩

/-- **The fibre of the image map is the set of orderings of `I`.** -/
noncomputable def fibreEquiv {q ω : ℕ} (I : Finset (Fin q)) (hI : I.card = ω) :
    {ρ : Fin ω → Fin q // imageFinset ρ = I} ≃ (Fin ω ≃ ↥I) where
  toFun := fibreToEquiv I hI
  invFun e := ⟨fun i => (e i : Fin q), by
    ext x
    simp only [imageFinset, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ (e i).2, fun hx => ⟨e.symm ⟨x, hx⟩, by simp⟩⟩⟩
  left_inv ρ := by
    refine Subtype.ext (funext fun i => ?_)
    rfl
  right_inv e := by
    refine Equiv.ext fun i => ?_
    exact Subtype.ext rfl

/-- **Fibre cardinality, single index.**  Exactly `ω!` maps `Fin ω → Fin q` have
image equal to a prescribed `ω`-element set `I`. -/
theorem card_fibre_imageFinset {q ω : ℕ} (I : Finset (Fin q)) (hI : I.card = ω) :
    Fintype.card {ρ : Fin ω → Fin q // imageFinset ρ = I} = ω.factorial := by
  classical
  rw [Fintype.card_congr (fibreEquiv I hI),
    Fintype.card_equiv (Finset.orderIsoOfFin I hI).toEquiv, Fintype.card_fin]

/-! ### Pair fibres -/

section Pair

/-- The type of injections `Fin ω ↪ Fin q`, as a subtype. -/
abbrev Inj (q ω : ℕ) := {ρ : Fin ω → Fin q // Function.Injective ρ}

/-- The image map on a pair of injections, into pairs of `ω`-element subsets. -/
noncomputable def imagePair {q ℓ ω : ℕ} (x : Inj q ω × Inj ℓ ω) :
    ↑(Set.powersetCard (Fin q) ω) × ↑(Set.powersetCard (Fin ℓ) ω) :=
  (imageFin x.1.1 x.1.2, imageFin x.2.1 x.2.2)

/-- The first component of `imagePair`, definitionally. -/
theorem imagePair_fst {q ℓ ω : ℕ} (x : Inj q ω × Inj ℓ ω) :
    (imagePair x).1 = imageFin x.1.1 x.1.2 := rfl

/-- The second component of `imagePair`, definitionally. -/
theorem imagePair_snd {q ℓ ω : ℕ} (x : Inj q ω × Inj ℓ ω) :
    (imagePair x).2 = imageFin x.2.1 x.2.2 := rfl

/-- **Single-index fibre, phrased with `imageFin`.** -/
theorem card_fibre_imageFin {q ω : ℕ} (I : ↑(Set.powersetCard (Fin q) ω)) :
    Fintype.card {ρ : Inj q ω // imageFin ρ.1 ρ.2 = I} = ω.factorial := by
  classical
  have e : {ρ : Inj q ω // imageFin ρ.1 ρ.2 = I} ≃
      {ρ : Fin ω → Fin q // imageFinset ρ = I.1} :=
    { toFun := fun ρ => ⟨ρ.1.1, congrArg Subtype.val ρ.2⟩
      invFun := fun ρ =>
        ⟨⟨ρ.1, injective_of_imageFinset_eq I.2 ρ.2⟩, Subtype.ext ρ.2⟩
      left_inv := fun ρ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun ρ => Subtype.ext rfl }
  rw [Fintype.card_congr e, card_fibre_imageFinset I.1 I.2]

/-- **The pair condition splits into the two single conditions.** -/
theorem imagePair_eq_iff {q ℓ ω : ℕ} (I : ↑(Set.powersetCard (Fin q) ω))
    (J : ↑(Set.powersetCard (Fin ℓ) ω)) (x : Inj q ω × Inj ℓ ω) :
    (imagePair x = (I, J)) ↔
      (imageFin x.1.1 x.1.2 = I ∧ imageFin x.2.1 x.2.2 = J) := by
  rw [Prod.ext_iff, imagePair_fst, imagePair_snd]

/-- **Fibre cardinality for a pair of injections.**  Every fibre of the pair
image map has exactly `ω! * ω!` elements. -/
theorem card_fibre_pair {q ℓ ω : ℕ} (I : ↑(Set.powersetCard (Fin q) ω))
    (J : ↑(Set.powersetCard (Fin ℓ) ω)) :
    Fintype.card {x : Inj q ω × Inj ℓ ω // imagePair x = (I, J)} =
      ω.factorial * ω.factorial := by
  classical
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (imagePair_eq_iff I J))]
  rw [Fintype.card_congr
    (Equiv.subtypeProdEquivProd (p := fun ρ : Inj q ω => imageFin ρ.1 ρ.2 = I)
      (q := fun κ : Inj ℓ ω => imageFin κ.1 κ.2 = J))]
  rw [Fintype.card_prod, card_fibre_imageFin I, card_fibre_imageFin J]

end Pair

end Q1Paper.PaperI
