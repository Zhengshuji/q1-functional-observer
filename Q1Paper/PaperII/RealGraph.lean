/-
Q1Paper/PaperII/RealGraph.lean

Paper II, Proposition `prop:tight`: the complexification of a real graph extension.

A real linear map `G` on `U ≤ (Fin k → ℝ)` that preserves `U`, together with `b ∈ U`, has a
graph `W(G,b) ⊆ (Fin k → ℝ) × (Fin k → ℝ)`; the paper's real-design criterion speaks of its
image in the complex pair space.  This module builds that image:

* `Gfun` / `GcU` / `GcU_phi` -- the complexification of `G` on `UC U`;
* `GR`          -- the same endomorphism over `ℝ`, on `U` itself;
* `phiPair`     -- the coordinatewise complexification of the pair space;
* `phiPair_mem_graphExt` -- it maps the real graph into the complex one.
-/

import Q1Paper.PaperII.Realification
import Q1Paper.PaperII.GraphExtension

open Module Matrix

namespace Q1Paper.PaperII

variable {k : ℕ}

/-- The value of `phi` is the coordinatewise coercion to `ℂ`. -/
@[simp] theorem phi_apply (x : Fin k → ℝ) (i : Fin k) :
    phi (Fin k) x i = (x i : ℂ) := rfl

/-- Complexifying a real matrix commutes with applying it to a vector. -/
theorem map_mulVec_phi (Gm : Matrix (Fin k) (Fin k) ℝ) (x : Fin k → ℝ) :
    (Gm.map (algebraMap ℝ ℂ)) *ᵥ (phi (Fin k) x) = phi (Fin k) (Gm *ᵥ x) := by
  funext i
  simp only [phi_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  push_cast
  rfl

/-- The complexified matrix, as a ℂ-linear map on the ambient space. -/
noncomputable def Gfun (Gm : Matrix (Fin k) (Fin k) ℝ) :
    (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ) :=
  (Gm.map (algebraMap ℝ ℂ)).mulVecLin

/-- `Gfun` preserves the complexification of a real subspace that `Gm` preserves. -/
theorem Gfun_mem_UC (U : Submodule ℝ (Fin k → ℝ)) (Gm : Matrix (Fin k) (Fin k) ℝ)
    (hG : ∀ x ∈ U, Gm *ᵥ x ∈ U) :
    ∀ z ∈ UC U, Gfun Gm z ∈ UC U := by
  have h : UC U ≤ Submodule.comap (Gfun Gm) (UC U) := by
    rw [UC, Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    exact Submodule.mem_comap.mpr
      (Submodule.subset_span ⟨Gm *ᵥ u, hG u hu, (map_mulVec_phi Gm u).symm⟩)
  intro z hz
  exact h hz

/-- **Complexification of a real endomorphism**: the `ℂ`-linear endomorphism of `UC U`
induced by a real matrix that preserves `U`. -/
noncomputable def GcU (U : Submodule ℝ (Fin k → ℝ)) (Gm : Matrix (Fin k) (Fin k) ℝ)
    (hG : ∀ x ∈ U, Gm *ᵥ x ∈ U) : ↥(UC U) →ₗ[ℂ] ↥(UC U) where
  toFun z := ⟨Gfun Gm z.1, Gfun_mem_UC U Gm hG z.1 z.2⟩
  map_add' x y := Subtype.ext (map_add (Gfun Gm) x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul (Gfun Gm) c x.1)

/-- The defining property of `GcU` on the spanning set. -/
theorem GcU_phi (U : Submodule ℝ (Fin k → ℝ)) (Gm : Matrix (Fin k) (Fin k) ℝ)
    (hG : ∀ x ∈ U, Gm *ᵥ x ∈ U) (u : ↥U) :
    (GcU U Gm hG ⟨phi (Fin k) (u : Fin k → ℝ), Submodule.subset_span ⟨_, u.2, rfl⟩⟩ : ↥(UC U))
      = ⟨phi (Fin k) (Gm *ᵥ (u : Fin k → ℝ)), Submodule.subset_span ⟨_, hG _ u.2, rfl⟩⟩ :=
  Subtype.ext (map_mulVec_phi Gm (u : Fin k → ℝ))

/-- **The same endomorphism over `ℝ`**: the restriction of `Gm` to `U`. -/
noncomputable def GR (U : Submodule ℝ (Fin k → ℝ)) (Gm : Matrix (Fin k) (Fin k) ℝ)
    (hG : ∀ x ∈ U, Gm *ᵥ x ∈ U) : ↥U →ₗ[ℝ] ↥U where
  toFun u := ⟨Gm *ᵥ (u : Fin k → ℝ), hG _ u.2⟩
  map_add' x y := Subtype.ext (by simp [Matrix.mulVec_add])
  map_smul' c x := Subtype.ext (by simp [Matrix.mulVec_smul])

@[simp] theorem GR_apply (U : Submodule ℝ (Fin k → ℝ)) (Gm : Matrix (Fin k) (Fin k) ℝ)
    (hG : ∀ x ∈ U, Gm *ᵥ x ∈ U) (u : ↥U) :
    (GR U Gm hG u : Fin k → ℝ) = Gm *ᵥ (u : Fin k → ℝ) := rfl

/-- Coordinatewise complexification of the pair space. -/
noncomputable def phiPair : ((Fin k → ℝ) × (Fin k → ℝ)) →ₗ[ℝ] ((Fin k → ℂ) × (Fin k → ℂ)) where
  toFun z := (phi (Fin k) z.1, phi (Fin k) z.2)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

@[simp] theorem phiPair_apply (z : (Fin k → ℝ) × (Fin k → ℝ)) :
    phiPair z = (phi (Fin k) z.1, phi (Fin k) z.2) := rfl

/-- **The real graph maps into the complex graph.**  Elementwise form of the identity
`phiPair '' W_ℝ(G,b) ⊆ W_ℂ(G,b)`. -/
theorem phiPair_mem_graphExt (U : Submodule ℝ (Fin k → ℝ)) (Gm : Matrix (Fin k) (Fin k) ℝ)
    (hG : ∀ x ∈ U, Gm *ᵥ x ∈ U) (b : ↥U)
    {z : (Fin k → ℝ) × (Fin k → ℝ)}
    (hz : z ∈ graphExt U (GR U Gm hG) b) :
    phiPair z ∈ graphExt (UC U) (GcU U Gm hG)
      ⟨phi (Fin k) (b : Fin k → ℝ), Submodule.subset_span ⟨b, b.2, rfl⟩⟩ := by
  rw [mem_graphExt] at hz
  obtain ⟨h, α, hx, hy⟩ := hz
  have hh : phi (Fin k) (h : Fin k → ℝ) ∈ UC U :=
    Submodule.subset_span ⟨h, h.2, rfl⟩
  rw [show phiPair z = (phi (Fin k) z.1, phi (Fin k) z.2) from rfl, mem_graphExt]
  refine ⟨⟨phi (Fin k) (h : Fin k → ℝ), hh⟩, α, by rw [hx], ?_⟩
  rw [hy, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, Submodule.coe_add,
    Submodule.coe_smul]
  congr 1
  exact (congrArg Subtype.val (GcU_phi U Gm hG h)).symm


/-- The inclusion `U → ↥(UC U)`, `u ↦ phi u`. -/
noncomputable def phiU (U : Submodule ℝ (Fin k → ℝ)) : ↥U →ₗ[ℝ] ↥(UC U) where
  toFun u := ⟨phi (Fin k) (u : Fin k → ℝ), Submodule.subset_span ⟨u, u.2, rfl⟩⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (by simp)

@[simp] theorem phiU_apply (U : Submodule ℝ (Fin k → ℝ)) (u : ↥U) :
    ((phiU U u : ↥(UC U)) : Fin k → ℂ) = phi (Fin k) (u : Fin k → ℝ) := rfl

theorem phiU_eq (U : Submodule ℝ (Fin k → ℝ)) (u : ↥U) :
    phiU U u = ⟨phi (Fin k) (u : Fin k → ℝ), Submodule.subset_span ⟨u, u.2, rfl⟩⟩ := rfl

/-- The domain of the graph parameters, complexified: `(h, c) ↦ (phi h, c)`. -/
noncomputable def phiDom (U : Submodule ℝ (Fin k → ℝ)) :
    (↥U × ℝ) →ₗ[ℝ] (↥(UC U) × ℂ) where
  toFun p := (phiU U p.1, (p.2 : ℂ))
  map_add' p q := by
    ext <;> simp
  map_smul' c p := by
    ext <;> simp

@[simp] theorem phiDom_apply (U : Submodule ℝ (Fin k → ℝ)) (p : ↥U × ℝ) :
    phiDom U p = (phiU U p.1, (p.2 : ℂ)) := rfl

/-- **The two graph maps agree after complexification.** -/
theorem graphMap_phiDom (U : Submodule ℝ (Fin k → ℝ)) (Gm : Matrix (Fin k) (Fin k) ℝ)
    (hG : ∀ x ∈ U, Gm *ᵥ x ∈ U) (b : ↥U) (p : ↥U × ℝ) :
    graphMap (UC U) (GcU U Gm hG)
        ⟨phi (Fin k) (b : Fin k → ℝ), Submodule.subset_span ⟨b, b.2, rfl⟩⟩ (phiDom U p)
      = phiPair (graphMap U (GR U Gm hG) b p) := by
  obtain ⟨u, c⟩ := p
  have h2 : ((GcU U Gm hG (phiU U u) : ↥(UC U)) : Fin k → ℂ)
      = phi (Fin k) (Gm *ᵥ (u : Fin k → ℝ)) := by
    rw [phiU_eq U u]
    exact congrArg Subtype.val (GcU_phi U Gm hG u)
  have h3 : (algebraMap ℝ (Fin k → ℝ)) c * (b : Fin k → ℝ) = c • (b : Fin k → ℝ) := by
    ext i
    simp
  have h4 : (algebraMap ℂ (Fin k → ℂ)) (c : ℝ) * phi (Fin k) (b : Fin k → ℝ)
      = (c : ℂ) • phi (Fin k) (b : Fin k → ℝ) := by
    ext i
    simp
  apply Prod.ext
  · rfl
  · simp only [graphMap, LinearMap.coe_mk, AddHom.coe_mk, phiPair_apply, phiDom_apply,
      Submodule.coe_add, Submodule.coe_smul, GR_apply, h2, phiU_apply, h3, h4, map_add,
      map_smul]
    rw [show ((c : ℂ) • (phi (Fin k) (b : Fin k → ℝ)))
        = c • (phi (Fin k) (b : Fin k → ℝ)) from by
      ext i
      simp]


/-- The `phi`-images of `U` are the values of the range of `phiU`. -/
theorem range_phiU_val (U : Submodule ℝ (Fin k → ℝ)) :
    ((phi (Fin k)) '' (U : Set (Fin k → ℝ)))
      = Subtype.val '' (Set.range (phiU U)) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨phiU U ⟨u, hu⟩, ⟨⟨u, hu⟩, rfl⟩, rfl⟩
  · rintro ⟨-, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, u.2, rfl⟩

/-- **`phiU` spans the complexification.** -/
theorem span_phiU (U : Submodule ℝ (Fin k → ℝ)) :
    Submodule.span ℂ (Set.range (phiU U)) = ⊤ := by
  refine le_antisymm le_top ?_
  intro h _
  have hmap : (h : Fin k → ℂ) ∈ Submodule.map (Submodule.subtype (UC U))
      (Submodule.span ℂ (Set.range (phiU U))) := by
    rw [Submodule.map_span]
    show (h : Fin k → ℂ) ∈ Submodule.span ℂ (Subtype.val '' Set.range (phiU U))
    rw [← range_phiU_val U]
    exact h.2
  obtain ⟨h', hh', heq⟩ := Submodule.mem_map.mp hmap
  have hh : h' = h := Subtype.ext heq
  rwa [hh] at hh'


/-- **`phiDom` spans its target**: every `(h, c)` with `h ∈ UC U` is reached. -/
theorem span_phiDom (U : Submodule ℝ (Fin k → ℝ)) :
    Submodule.span ℂ (Set.range (phiDom U)) = ⊤ := by
  set S := Submodule.span ℂ (Set.range (phiDom U)) with hS
  have hinl : Submodule.map (LinearMap.inl ℂ ↥(UC U) ℂ) (⊤ : Submodule ℂ ↥(UC U)) ≤ S := by
    rw [← span_phiU U, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨y, ⟨u, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨(u, 0), rfl⟩
  refine le_antisymm le_top ?_
  intro z _
  obtain ⟨hh, c⟩ := z
  have h1 : ((hh, (0 : ℂ)) : ↥(UC U) × ℂ) ∈ S :=
    hinl (Submodule.mem_map_of_mem (Submodule.mem_top))
  have hz : ((hh, c) : ↥(UC U) × ℂ) = (hh, 0) + ((0 : ↥(UC U)), c) := by
    ext <;> simp
  rw [hz]
  refine Submodule.add_mem _ h1 ?_
  have hsplit : (((0 : ↥(UC U)), c) : ↥(UC U) × ℂ) = c • (((0 : ↥(UC U)), (1 : ℂ))) := by
    ext <;> simp
  rw [hsplit]
  refine Submodule.smul_mem _ c (Submodule.subset_span ⟨(0, 1), ?_⟩)
  rw [phiDom_apply]
  simp

/-- **The complex graph is the `ℂ`-span of the real graph's image.** -/
theorem graphExt_span_phiPair (U : Submodule ℝ (Fin k → ℝ)) (Gm : Matrix (Fin k) (Fin k) ℝ)
    (hG : ∀ x ∈ U, Gm *ᵥ x ∈ U) (b : ↥U) :
    Submodule.span ℂ
        (phiPair '' (graphExt U (GR U Gm hG) b : Set ((Fin k → ℝ) × (Fin k → ℝ))))
      = graphExt (UC U) (GcU U Gm hG)
          ⟨phi (Fin k) (b : Fin k → ℝ), Submodule.subset_span ⟨b, b.2, rfl⟩⟩ := by
  have hb : phi (Fin k) (b : Fin k → ℝ) ∈ UC U := Submodule.subset_span ⟨b, b.2, rfl⟩
  have hcomp : (phiPair ∘ graphMap U (GR U Gm hG) b)
      = (graphMap (UC U) (GcU U Gm hG) ⟨phi (Fin k) (b : Fin k → ℝ), hb⟩ ∘ phiDom U) :=
    funext fun p => (graphMap_phiDom U Gm hG b p).symm
  have hset : (phiPair '' (graphExt U (GR U Gm hG) b : Set ((Fin k → ℝ) × (Fin k → ℝ))))
      = graphMap (UC U) (GcU U Gm hG) ⟨phi (Fin k) (b : Fin k → ℝ), hb⟩
        '' (Set.range (phiDom U)) := by
    show phiPair '' (Set.range (graphMap U (GR U Gm hG) b))
      = graphMap (UC U) (GcU U Gm hG) ⟨phi (Fin k) (b : Fin k → ℝ), hb⟩
        '' (Set.range (phiDom U))
    rw [← Set.range_comp, hcomp, Set.range_comp]
  rw [hset, ← Submodule.map_span, span_phiDom U, Submodule.map_top]
  rfl


/-- The real pair row space of a real design (the `ℝ`-analogue of `WR`). -/
noncomputable def WRreal (A : Matrix (Fin n) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (R : Matrix (Fin r) (Fin n) ℝ) :
    Submodule ℝ ((Fin k → ℝ) × (Fin k → ℝ)) :=
  Q1Paper.pairRowSpace (Matrix.fromRows L0 R * N) (Matrix.fromRows L0 R * (A * N))

/-- The complexified `L` times the complexified `N` is the complexification of the product. -/
theorem Lc_mul (L0 : Matrix (Fin r0) (Fin n) ℝ) (R : Matrix (Fin r) (Fin n) ℝ)
    (N : Matrix (Fin n) (Fin k) ℝ) :
    Lc L0 R * (N.map (algebraMap ℝ ℂ))
      = (Matrix.fromRows L0 R * N).map (algebraMap ℝ ℂ) := by
  rw [Lc]
  exact (Matrix.map_mul (f := algebraMap ℝ ℂ)).symm

/-- The complexified `L` times the complexified `A N` is the complexification of the product. -/
theorem Lc_mul_A (A : Matrix (Fin n) (Fin n) ℝ) (L0 : Matrix (Fin r0) (Fin n) ℝ)
    (R : Matrix (Fin r) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ) :
    Lc L0 R * (Ac A * (N.map (algebraMap ℝ ℂ)))
      = (Matrix.fromRows L0 R * (A * N)).map (algebraMap ℝ ℂ) := by
  have hA : Ac A * N.map (algebraMap ℝ ℂ) = (A * N).map (algebraMap ℝ ℂ) := by
    rw [Ac]
    exact (Matrix.map_mul (f := algebraMap ℝ ℂ)).symm
  rw [hA, Lc]
  exact (Matrix.map_mul (f := algebraMap ℝ ℂ)).symm

/-- **The complex `W` of a real design is the complexification of its real `W`.** -/
theorem WR_eq_span_phiPair_WRreal (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Matrix (Fin n) (Fin k) ℝ) (L0 : Matrix (Fin r0) (Fin n) ℝ)
    (R : Matrix (Fin r) (Fin n) ℝ) :
    WR A (N.map (algebraMap ℝ ℂ)) L0 R
      = Submodule.span ℂ (phiPair '' (WRreal A N L0 R : Set ((Fin k → ℝ) × (Fin k → ℝ)))) := by
  have h1 := Lc_mul L0 R N
  have h2 := Lc_mul_A A L0 R N
  have hset : Set.range (fun i : Fin r0 ⊕ Fin r =>
        (((Matrix.fromRows L0 R * N).map (algebraMap ℝ ℂ)) i,
         ((Matrix.fromRows L0 R * (A * N)).map (algebraMap ℝ ℂ)) i))
      = phiPair '' Set.range (fun i : Fin r0 ⊕ Fin r =>
        (((Matrix.fromRows L0 R * N) i), ((Matrix.fromRows L0 R * (A * N)) i))) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨_, ⟨i, rfl⟩, ?_⟩
      apply Prod.ext <;> funext j <;> simp [phi_apply, Matrix.map_apply]
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [WR, WRreal, Q1Paper.pairRowSpace, Q1Paper.pairRowSpace, h1, h2, hset]
  -- the `ℝ`-span and the generating set have the same `ℂ`-span of `phiPair`-images
  have key : ∀ z ∈ Submodule.span ℝ (Set.range (fun i : Fin r0 ⊕ Fin r =>
        (((Matrix.fromRows L0 R * N) i), ((Matrix.fromRows L0 R * (A * N)) i)))),
      phiPair z ∈ Submodule.span ℂ
        (phiPair '' Set.range (fun i : Fin r0 ⊕ Fin r =>
          (((Matrix.fromRows L0 R * N) i), ((Matrix.fromRows L0 R * (A * N)) i)))) := by
    intro z hz
    refine Submodule.span_induction (p := fun y _ => phiPair y ∈ Submodule.span ℂ
      (phiPair '' Set.range (fun i : Fin r0 ⊕ Fin r =>
        (((Matrix.fromRows L0 R * N) i), ((Matrix.fromRows L0 R * (A * N)) i))))) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨_, ⟨i, rfl⟩, rfl⟩
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb
    · intro c a _ ha
      have hc : phiPair (c • a) = (c : ℂ) • phiPair a := by
        rw [map_smul]
        ext <;> simp
      rw [hc]
      exact Submodule.smul_mem _ (c : ℂ) ha
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    exact Submodule.subset_span ⟨z, Submodule.subset_span hz, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact key z hz


/-- The real `W₀` in the pair space (the `ℝ`-analogue of `W0`). -/
noncomputable def W0real (A : Matrix (Fin n) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) : Submodule ℝ ((Fin k → ℝ) × (Fin k → ℝ)) :=
  Q1Paper.pairRowSpace (L0 * N) (L0 * (A * N))

/-- The real `T` in the pair space (the `ℝ`-analogue of `TR`). -/
noncomputable def TRreal (A : Matrix (Fin n) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ) :
    Submodule ℝ ((Fin k → ℝ) × (Fin k → ℝ)) :=
  Q1Paper.pairRowSpace N (A * N)

/-- `W₀` in encoded form. -/
theorem W0real_eq (A : Matrix (Fin n) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) :
    W0real A N L0 = Submodule.map (Φ (K := ℝ)).toLinearMap
      (Q1Subspace.rowSpace (pairRows (L0 * N) (L0 * (A * N)))) := by
  rw [W0real]
  exact pairRowSpace_eq_map_pairRows (L0 * N) (L0 * (A * N))

/-- `T` in encoded form. -/
theorem TRreal_eq (A : Matrix (Fin n) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ) :
    TRreal A N = Submodule.map (Φ (K := ℝ)).toLinearMap
      (Q1Subspace.rowSpace (pairRows N (A * N))) := by
  rw [TRreal]
  exact pairRowSpace_eq_map_pairRows N (A * N)

/-- **The real sandwich, converse, in the encoded space**: an encoded subspace between
`row(L₀M)` and `row(M)` of the right dimension is realised by a real design of `r` rows,
whose real pair space is the image of the encoded subspace under `Φ`. -/
theorem exists_design_of_encoded (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Matrix (Fin n) (Fin k) ℝ) (L0 : Matrix (Fin r0) (Fin n) ℝ)
    {Wenc : Submodule ℝ (Fin (k + k) → ℝ)}
    (hW0 : Q1Subspace.rowSpace (L0 * pairRows N (A * N)) ≤ Wenc)
    (hWT : Wenc ≤ Q1Subspace.rowSpace (pairRows N (A * N)))
    (hdim : Module.finrank ℝ ↥Wenc
      ≤ Module.finrank ℝ ↥(Q1Subspace.rowSpace (L0 * pairRows N (A * N))) + r) :
    ∃ R : Matrix (Fin r) (Fin n) ℝ,
      WRreal A N L0 R = Submodule.map (Φ (K := ℝ)).toLinearMap Wenc := by
  obtain ⟨R, hR⟩ := Q1Paper.claim4_converse (K := ℝ) (L0 := L0)
    (M := pairRows N (A * N)) (W := Wenc) hW0 hWT hdim
  refine ⟨R, ?_⟩
  rw [WRreal, pairRowSpace_eq_map_pairRows, ← hR,
    (mul_pairRows (Matrix.fromRows L0 R) N (A * N)).symm]


/-- **The real sandwich, converse, in the pair space**: a real subspace between `W₀` and `T`
of quotient dimension at most `r` is realised by a real design of `r` rows. -/
theorem exists_design_of_pairRowSpace (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Matrix (Fin n) (Fin k) ℝ) (L0 : Matrix (Fin r0) (Fin n) ℝ)
    {W : Submodule ℝ ((Fin k → ℝ) × (Fin k → ℝ))}
    (hW0 : W0real A N L0 ≤ W) (hWT : W ≤ TRreal A N)
    (hdim : Module.finrank ℝ ↥W ≤ Module.finrank ℝ ↥(W0real A N L0) + r) :
    ∃ R : Matrix (Fin r) (Fin n) ℝ, WRreal A N L0 R = W := by
  classical
  set Wenc : Submodule ℝ (Fin (k + k) → ℝ) :=
    Submodule.comap (Φ (K := ℝ)).toLinearMap W with hWenc
  -- membership transports through `Φ`
  have hmem : ∀ x : Fin (k + k) → ℝ, x ∈ Wenc ↔ (Φ (K := ℝ)) x ∈ W := by
    intro x
    rw [hWenc]
    exact Submodule.mem_comap
  -- `W` is the image of `Wenc`
  have hmap : Submodule.map (Φ (K := ℝ)).toLinearMap Wenc = W := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem y).mp hy
    · intro hz
      refine ⟨(Φ (K := ℝ)).symm z, ?_, (Φ (K := ℝ)).apply_symm_apply z⟩
      refine (hmem _).mpr ?_
      rwa [LinearEquiv.apply_symm_apply]
  -- the two sandwich conditions
  have hW0' : Q1Subspace.rowSpace (L0 * pairRows N (A * N)) ≤ Wenc := by
    intro x hx
    refine (hmem x).mpr ?_
    refine hW0 ?_
    rw [W0real_eq]
    exact Submodule.mem_map_of_mem (by rwa [← mul_pairRows])
  have hWT' : Wenc ≤ Q1Subspace.rowSpace (pairRows N (A * N)) := by
    intro x hx
    have hxW : (Φ (K := ℝ)) x ∈ TRreal A N := hWT ((hmem x).mp hx)
    rw [TRreal_eq] at hxW
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hxW
    rwa [← (Φ (K := ℝ)).injective hyx]
  -- the dimension
  have hdimW : Module.finrank ℝ ↥Wenc = Module.finrank ℝ ↥W := by
    have hcomap : Wenc = Submodule.map (Φ (K := ℝ)).symm.toLinearMap W := by
      ext x
      rw [hmem]
      constructor
      · intro hx
        exact ⟨Φ (K := ℝ) x, hx, (Φ (K := ℝ)).symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [hcomap]
    exact LinearEquiv.finrank_map_eq (Φ (K := ℝ)).symm W
  have hdim0 : Module.finrank ℝ ↥(Q1Subspace.rowSpace (L0 * pairRows N (A * N)))
      = Module.finrank ℝ ↥(W0real A N L0) := by
    rw [W0real_eq, mul_pairRows]
    exact (LinearEquiv.finrank_map_eq (Φ (K := ℝ)) _).symm
  -- apply the encoded converse
  obtain ⟨R, hR⟩ := exists_design_of_encoded A N L0 hW0' hWT' (by
    rw [hdim0, hdimW]
    exact hdim)
  exact ⟨R, by rw [hR, hmap]⟩

end Q1Paper.PaperII
