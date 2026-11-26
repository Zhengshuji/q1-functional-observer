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

set_option maxHeartbeats 1000000

open Module Matrix

namespace Q1Paper.PaperII

variable {k : ℕ}

/-- The value of `phi` is the coordinatewise coercion to `ℂ`. -/
@[simp] theorem phi_apply (x : Fin k → ℝ) (i : Fin k) :
    phi (Fin k) x i = (x i : ℂ) := rfl

/-- `phi` is injective at zero. -/
theorem phi_eq_zero {x : Fin k → ℝ} (h : phi (Fin k) x = 0) : x = 0 := by
  funext i
  have hi := congrFun h i
  simpa [phi_apply] using hi

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


/-- **Prop 3, the `(⇐)` direction for the paper's real designs.**  If the real graph
`W_ℝ(G,b)` sits inside the real sandwich and its complexification is feasible, then the
minimum order over real designs satisfies
`t_min^ℝ ≤ dim_ℝ U + 1 − s₀`. -/
theorem tMinC_le_of_graph_real {p : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (hN : (N.map (algebraMap ℝ ℂ)).mulVecLin.range
      = (Matrix.fromRows ((C.map (algebraMap ℝ ℂ)) * (A.map (algebraMap ℝ ℂ)))
          (C.map (algebraMap ℝ ℂ))).mulVecLin.ker)
    {U : Submodule ℝ (Fin k → ℝ)} {Gm : Matrix (Fin k) (Fin k) ℝ}
    (hG : ∀ x ∈ U, Gm *ᵥ x ∈ U) {b : ↥U} (hb : b ≠ 0)
    (hW0 : W0real A N L0 ≤ graphExt U (GR U Gm hG) b)
    (hWT : graphExt U (GR U Gm hG) b ≤ TRreal A N)
    (hW0C : W0 A (N.map (algebraMap ℝ ℂ)) L0
      ≤ graphExt (UC U) (GcU U Gm hG)
          ⟨phi (Fin k) (b : Fin k → ℝ), Submodule.subset_span ⟨b, b.2, rfl⟩⟩)
    (hfeas : IsFeasible (graphExt (UC U) (GcU U Gm hG)
      ⟨phi (Fin k) (b : Fin k → ℝ), Submodule.subset_span ⟨b, b.2, rfl⟩⟩)) :
    tMinC A N L0
      ≤ ((Module.finrank ℝ ↥U + 1
          - Module.finrank ℂ ↥(W0 A (N.map (algebraMap ℝ ℂ)) L0) : ℕ) : WithTop ℕ) := by
  classical
  set bC : ↥(UC U) := ⟨phi (Fin k) (b : Fin k → ℝ), Submodule.subset_span ⟨b, b.2, rfl⟩⟩ with hbC
  set WRr : Submodule ℝ ((Fin k → ℝ) × (Fin k → ℝ)) := graphExt U (GR U Gm hG) b with hWRr
  set WC : Submodule ℂ ((Fin k → ℂ) × (Fin k → ℂ)) := graphExt (UC U) (GcU U Gm hG) bC with hWC
  -- build the real design
  obtain ⟨R, hR⟩ := exists_design_of_pairRowSpace (A := A) (N := N) (L0 := L0) (W := WRr)
    (by rw [hWRr]; exact hW0) (by rw [hWRr]; exact hWT) (by
      rw [hWRr, graphExt_finrank U (GR U Gm hG) b hb]
      exact Nat.le_add_left _ _)
  -- its complex `W` is the complex graph
  have hWR : WR A (N.map (algebraMap ℝ ℂ)) L0 R = WC := by
    rw [WR_eq_span_phiPair_WRreal, hR, hWRr, hWC]
    exact graphExt_span_phiPair U Gm hG b
  have hW0le : W0 A (N.map (algebraMap ℝ ℂ)) L0 ≤ WR A (N.map (algebraMap ℝ ℂ)) L0 R := by
    rw [hWR]; exact hW0C
  have hfeasR : IsFeasible (WR A (N.map (algebraMap ℝ ℂ)) L0 R) := by
    rw [hWR]; exact hfeas
  -- the order the design realises
  have hbC : bC ≠ 0 := by
    intro h
    apply hb
    apply Subtype.ext
    apply phi_eq_zero
    have hv := congrArg Subtype.val h
    simpa [hbC] using hv
  have ht : t (W0 A (N.map (algebraMap ℝ ℂ)) L0) (WR A (N.map (algebraMap ℝ ℂ)) L0 R)
      = Module.finrank ℝ ↥U + 1
        - Module.finrank ℂ ↥(W0 A (N.map (algebraMap ℝ ℂ)) L0) := by
    rw [t_eq_finrank_sub hW0le, hWR, hWC,
      graphExt_finrank (UC U) (GcU U Gm hG) bC hbC, finrank_UC U]
  -- hence `DEC_c` at that order, and `t_min^ℝ` is below it
  have hdec : DecOrder C A L0 (Module.finrank ℝ ↥U + 1
      - Module.finrank ℂ ↥(W0 A (N.map (algebraMap ℝ ℂ)) L0)) := by
    rw [← ht]
    exact feasible_to_decC C A L0 N hN hW0le hfeasR
  exact (tMinC_le_iff_decC C A L0 N hN _).mpr hdec


/-- `t_min^ℝ` is below the order of any real design. -/
theorem tMinC_le_of_mem {A : Matrix (Fin n) (Fin n) ℝ} {N : Matrix (Fin n) (Fin k) ℝ}
    {L0 : Matrix (Fin r0) (Fin n) ℝ} {m : ℕ} (hm : m ∈ tMinCSet A N L0) :
    tMinC A N L0 ≤ (m : WithTop ℕ) := by
  by_cases hne : (tMinCSet A N L0).Nonempty
  · rw [tMinC, dif_pos hne]
    exact WithTop.coe_le_coe.mpr (Nat.sInf_le hm)
  · exact absurd ⟨_, hm⟩ hne

/-- **Prop 3, the `(⇒)` direction for the paper's real designs.**  If the minimum order over
real designs saturates, `t_min^ℝ = a + 1 − s₀`, then the complex tightness data exist: a
feasible `W` in the sandwich whose projection is `U₀+V₀`, realised as a graph `W(G,b)`. -/
theorem exists_graph_of_tMinC_eq {p : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (hN : (N.map (algebraMap ℝ ℂ)).mulVecLin.range
      = (Matrix.fromRows ((C.map (algebraMap ℝ ℂ)) * (A.map (algebraMap ℝ ℂ)))
          (C.map (algebraMap ℝ ℂ))).mulVecLin.ker)
    (hsa : Module.finrank ℂ ↥(W0 A (N.map (algebraMap ℝ ℂ)) L0)
      ≤ Module.finrank ℂ ↥(Q1Subspace.pi1 (W0 A (N.map (algebraMap ℝ ℂ)) L0)
          ⊔ Q1Subspace.pi2 (W0 A (N.map (algebraMap ℝ ℂ)) L0)))
    (heq : tMinC A N L0
      = ((Module.finrank ℂ ↥(Q1Subspace.pi1 (W0 A (N.map (algebraMap ℝ ℂ)) L0)
            ⊔ Q1Subspace.pi2 (W0 A (N.map (algebraMap ℝ ℂ)) L0))
          + 1 - Module.finrank ℂ ↥(W0 A (N.map (algebraMap ℝ ℂ)) L0) : ℕ) : WithTop ℕ)) :
    ∃ (V : Submodule ℂ ((Fin k → ℂ) × (Fin k → ℂ)))
      (G : ↥(Q1Subspace.pi1 V) →ₗ[ℂ] ↥(Q1Subspace.pi1 V))
      (b : ↥(Q1Subspace.pi1 V)),
      W0 A (N.map (algebraMap ℝ ℂ)) L0 ≤ V ∧ V ≤ TR A (N.map (algebraMap ℝ ℂ)) ∧
        IsFeasible V ∧ b ≠ 0 ∧ V = graphExt (Q1Subspace.pi1 V) G b ∧
        Q1Subspace.pi1 V
          = Q1Subspace.pi1 (W0 A (N.map (algebraMap ℝ ℂ)) L0)
            ⊔ Q1Subspace.pi2 (W0 A (N.map (algebraMap ℝ ℂ)) L0) ∧
        (∀ lam : ℂ,
          finrank ℂ ↥(Submodule.map (graphPencil (Q1Subspace.pi1 V) G lam) ⊤
            ⊔ Submodule.span ℂ {((b : ↥(Q1Subspace.pi1 V)) : Fin k → ℂ)})
            = finrank ℂ ↥(Q1Subspace.pi1 V)) := by
  classical
  set r : ℕ := Module.finrank ℂ ↥(Q1Subspace.pi1 (W0 A (N.map (algebraMap ℝ ℂ)) L0)
      ⊔ Q1Subspace.pi2 (W0 A (N.map (algebraMap ℝ ℂ)) L0))
    + 1 - Module.finrank ℂ ↥(W0 A (N.map (algebraMap ℝ ℂ)) L0) with hr
  -- the decision predicate holds at the saturated order
  have hdec : DecOrder C A L0 r :=
    (tMinC_le_iff_decC C A L0 N hN r).mp (by rw [hr]; exact le_of_eq heq)
  obtain ⟨R, hW0R, hWTR, hfeasR, htR⟩ :=
    decC_to_feasible_design (C := C) (A := A) (L0 := L0) (N := N.map (algebraMap ℝ ℂ)) hN hdec
  -- its order is exactly `r`
  have hmem : t (W0 A (N.map (algebraMap ℝ ℂ)) L0) (WR A (N.map (algebraMap ℝ ℂ)) L0 R)
      ∈ tMinCSet A N L0 := ⟨_, R, hW0R, hfeasR, rfl⟩
  have hle : tMinC A N L0
      ≤ ((t (W0 A (N.map (algebraMap ℝ ℂ)) L0)
          (WR A (N.map (algebraMap ℝ ℂ)) L0 R) : ℕ) : WithTop ℕ) :=
    tMinC_le_of_mem hmem
  have hle' : (r : WithTop ℕ)
      ≤ ((t (W0 A (N.map (algebraMap ℝ ℂ)) L0)
          (WR A (N.map (algebraMap ℝ ℂ)) L0 R) : ℕ) : WithTop ℕ) := by
    rw [← heq]
    exact hle
  have ht : t (W0 A (N.map (algebraMap ℝ ℂ)) L0) (WR A (N.map (algebraMap ℝ ℂ)) L0 R) = r :=
    le_antisymm htR (WithTop.coe_le_coe.mp hle')
  -- the quotient dimension is `a + 1`
  have hdim : Module.finrank ℂ ↥(WR A (N.map (algebraMap ℝ ℂ)) L0 R)
      = Module.finrank ℂ ↥(Q1Subspace.pi1 (W0 A (N.map (algebraMap ℝ ℂ)) L0)
          ⊔ Q1Subspace.pi2 (W0 A (N.map (algebraMap ℝ ℂ)) L0)) + 1 := by
    have hsub := t_eq_finrank_sub hW0R
    have hmono := Submodule.finrank_mono hW0R
    omega
  have hpi := pi1_eq_sup_of_finrank A (N.map (algebraMap ℝ ℂ)) L0 hW0R hfeasR hdim
  have hdim' : Module.finrank ℂ ↥(WR A (N.map (algebraMap ℝ ℂ)) L0 R)
      = Module.finrank ℂ ↥(Q1Subspace.pi1 (WR A (N.map (algebraMap ℝ ℂ)) L0 R)) + 1 := by
    rw [hpi]
    exact hdim
  obtain ⟨b, hb, G, hWV⟩ := exists_graph_representation
    (WR A (N.map (algebraMap ℝ ℂ)) L0 R) hfeasR hdim'
  refine ⟨_, G, b, hW0R, hWTR, hfeasR, hb, hWV, hpi, ?_⟩
  intro lam
  have hpen := graphExt_piLam (Q1Subspace.pi1 (WR A (N.map (algebraMap ℝ ℂ)) L0 R)) G b lam
  have hspec := hfeasR.2 lam
  rw [hWV] at hspec
  rw [hpen, graphExt_pi1] at hspec
  exact hspec


/-- `Φ` and the coordinatewise complexification agree with `phiPair`. -/
theorem phiPair_eq (x : (Fin k → ℝ) × (Fin k → ℝ)) :
    phiPair x = Φ (K := ℂ) (phi (Fin (k + k)) ((Φ (K := ℝ)).symm x)) := by
  have h1 : (fun j : Fin k => (Φ (K := ℝ)).symm x (finSumFinEquiv (Sum.inl j))) = x.1 := by
    have h := (Φ_apply ((Φ (K := ℝ)).symm x)).symm.trans
      (LinearEquiv.apply_symm_apply (Φ (K := ℝ)) x)
    exact congrArg Prod.fst h
  have h2 : (fun j : Fin k => (Φ (K := ℝ)).symm x (finSumFinEquiv (Sum.inr j))) = x.2 := by
    have h := (Φ_apply ((Φ (K := ℝ)).symm x)).symm.trans
      (LinearEquiv.apply_symm_apply (Φ (K := ℝ)) x)
    exact congrArg Prod.snd h
  apply Prod.ext
  · funext j
    show phi (Fin k) x.1 j
      = (phi (Fin (k + k))) ((Φ (K := ℝ)).symm x) (finSumFinEquiv (Sum.inl j))
    rw [phi_apply, phi_apply, congrFun h1 j]
  · funext j
    show phi (Fin k) x.2 j
      = (phi (Fin (k + k))) ((Φ (K := ℝ)).symm x) (finSumFinEquiv (Sum.inr j))
    rw [phi_apply, phi_apply, congrFun h2 j]

/-- **Complexification preserves the dimension of a real pair space.** -/
theorem finrank_span_phiPair {X : Submodule ℝ ((Fin k → ℝ) × (Fin k → ℝ))} :
    Module.finrank ℂ ↥(Submodule.span ℂ (phiPair '' (X : Set ((Fin k → ℝ) × (Fin k → ℝ)))))
      = Module.finrank ℝ ↥X := by
  set Y : Submodule ℝ (Fin (k + k) → ℝ) := Submodule.map (Φ (K := ℝ)).symm.toLinearMap X with hY
  have hYrank : Module.finrank ℝ ↥Y = Module.finrank ℝ ↥X :=
    LinearEquiv.finrank_map_eq (Φ (K := ℝ)).symm X
  have hset : (phiPair '' (X : Set ((Fin k → ℝ) × (Fin k → ℝ))))
      = (Φ (K := ℂ)) '' ((phi (Fin (k + k))) '' (Y : Set (Fin (k + k) → ℝ))) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨phi (Fin (k + k)) ((Φ (K := ℝ)).symm x),
        ⟨(Φ (K := ℝ)).symm x, ⟨x, hx, rfl⟩, rfl⟩, (phiPair_eq x).symm⟩
    · rintro ⟨g, ⟨y, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      exact ⟨x, hx, phiPair_eq x⟩
  have hspan : Submodule.span ℂ ((Φ (K := ℂ)) '' ((phi (Fin (k + k))) '' (Y : Set (Fin (k + k) → ℝ))))
      = Submodule.map (Φ (K := ℂ)).toLinearMap (UC Y) := by
    have h := Submodule.map_span (f := (Φ (K := ℂ)).toLinearMap)
      (s := ((phi (Fin (k + k))) '' (Y : Set (Fin (k + k) → ℝ))))
    exact h.symm
  rw [hset, hspan, LinearEquiv.finrank_map_eq (Φ (K := ℂ)) (UC Y), finrank_UC Y, hYrank]


/-- The first projection commutes with complexification. -/
theorem pi1_span_phiPair (X : Submodule ℝ ((Fin k → ℝ) × (Fin k → ℝ))) :
    Q1Subspace.pi1 (Submodule.span ℂ (phiPair '' (X : Set ((Fin k → ℝ) × (Fin k → ℝ)))))
      = Submodule.span ℂ (phi (Fin k) '' (Q1Subspace.pi1 X : Set (Fin k → ℝ))) := by
  rw [Q1Subspace.pi1, Q1Subspace.pi1, Submodule.map_span, Set.image_image]
  congr 1
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- The second projection commutes with complexification. -/
theorem pi2_span_phiPair (X : Submodule ℝ ((Fin k → ℝ) × (Fin k → ℝ))) :
    Q1Subspace.pi2 (Submodule.span ℂ (phiPair '' (X : Set ((Fin k → ℝ) × (Fin k → ℝ)))))
      = Submodule.span ℂ (phi (Fin k) '' (Q1Subspace.pi2 X : Set (Fin k → ℝ))) := by
  rw [Q1Subspace.pi2, Q1Subspace.pi2, Submodule.map_span, Set.image_image]
  congr 1
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- The pencil projection commutes with complexification. -/
theorem piLam_span_phiPair (X : Submodule ℝ ((Fin k → ℝ) × (Fin k → ℝ))) (lam : ℝ) :
    Q1Subspace.piLam (K := ℂ) (lam : ℂ)
        (Submodule.span ℂ (phiPair '' (X : Set ((Fin k → ℝ) × (Fin k → ℝ)))))
      = Submodule.span ℂ (phi (Fin k) '' (Q1Subspace.piLam (K := ℝ) lam X : Set (Fin k → ℝ))) := by
  have hcomp : ∀ x : (Fin k → ℝ) × (Fin k → ℝ),
      ((lam : ℂ) • LinearMap.fst ℂ (Fin k → ℂ) (Fin k → ℂ)
          - LinearMap.snd ℂ (Fin k → ℂ) (Fin k → ℂ)) (phiPair x)
        = phi (Fin k) ((lam • LinearMap.fst ℝ (Fin k → ℝ) (Fin k → ℝ)
            - LinearMap.snd ℝ (Fin k → ℝ) (Fin k → ℝ)) x) := by
    intro x
    funext j
    show (lam : ℂ) * (phi (Fin k) x.1) j - (phi (Fin k) x.2) j
      = (phi (Fin k) ((lam • LinearMap.fst ℝ (Fin k → ℝ) (Fin k → ℝ)
          - LinearMap.snd ℝ (Fin k → ℝ) (Fin k → ℝ)) x)) j
    rw [phi_apply, phi_apply, phi_apply]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    push_cast
    ring
  rw [Q1Subspace.piLam, Q1Subspace.piLam, Submodule.map_span, Set.image_image]
  congr 1
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, (hcomp x).symm⟩
  · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, hcomp x⟩


/-- Real part, coordinatewise, as a real-linear map. -/
noncomputable def reFun : (Fin k → ℂ) →ₗ[ℝ] (Fin k → ℝ) where
  toFun z i := (z i).re
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

/-- Imaginary part, coordinatewise, as a real-linear map. -/
noncomputable def imFun : (Fin k → ℂ) →ₗ[ℝ] (Fin k → ℝ) where
  toFun z i := (z i).im
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

@[simp] theorem reFun_phi (x : Fin k → ℝ) : reFun (phi (Fin k) x) = x := by
  ext i
  simp [reFun, phi_apply]

@[simp] theorem imFun_phi (x : Fin k → ℝ) : imFun (phi (Fin k) x) = 0 := by
  ext i
  simp [imFun, phi_apply]

/-- **Real and imaginary parts of a complex combination of real vectors stay in the span.**
This is the "real points" fact: the real part of an element of `span ℂ (phi '' Y)` lies in `Y`. -/
theorem re_im_mem_of_mem_span (Y : Submodule ℝ (Fin k → ℝ)) {z : Fin k → ℂ}
    (hz : z ∈ Submodule.span ℂ ((phi (Fin k)) '' (Y : Set (Fin k → ℝ)))) :
    reFun z ∈ Y ∧ imFun z ∈ Y := by
  refine Submodule.span_induction (p := fun z _ => reFun z ∈ Y ∧ imFun z ∈ Y) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨y, hy, rfl⟩
    rw [reFun_phi, imFun_phi]
    exact ⟨hy, Y.zero_mem⟩
  · rw [map_zero, map_zero]
    exact ⟨Y.zero_mem, Y.zero_mem⟩
  · intro a b _ _ ha hb
    rw [map_add, map_add]
    exact ⟨Y.add_mem ha.1 hb.1, Y.add_mem ha.2 hb.2⟩
  · intro c a _ ha
    have hre : reFun (c • a) = (c.re : ℝ) • reFun a - (c.im : ℝ) • imFun a := by
      ext i
      simp [reFun, imFun, Pi.sub_apply, Pi.smul_apply, Complex.mul_re]
    have him : imFun (c • a) = (c.re : ℝ) • imFun a + (c.im : ℝ) • reFun a := by
      ext i
      simp [reFun, imFun, Pi.add_apply, Pi.smul_apply, Complex.mul_im]
    rw [hre, him]
    exact ⟨Y.sub_mem (Y.smul_mem _ ha.1) (Y.smul_mem _ ha.2),
      Y.add_mem (Y.smul_mem _ ha.2) (Y.smul_mem _ ha.1)⟩

/-- **The real points of `span ℂ (phi '' Y)` are exactly `Y`.** -/
theorem mem_of_phi_mem_span (Y : Submodule ℝ (Fin k → ℝ)) {x : Fin k → ℝ}
    (h : phi (Fin k) x ∈ Submodule.span ℂ ((phi (Fin k)) '' (Y : Set (Fin k → ℝ)))) :
    x ∈ Y := by
  have h' := (re_im_mem_of_mem_span Y h).1
  rwa [reFun_phi] at h'


/-- **Complex feasibility descends to the real pair space.** -/
theorem isFeasible_real_of_span_phiPair
    {X : Submodule ℝ ((Fin k → ℝ) × (Fin k → ℝ))}
    (h : IsFeasible (Submodule.span ℂ (phiPair '' (X : Set ((Fin k → ℝ) × (Fin k → ℝ)))))) :
    IsFeasible X := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have h2 : phi (Fin k) x
        ∈ Q1Subspace.pi2 (Submodule.span ℂ (phiPair '' (X : Set ((Fin k → ℝ) × (Fin k → ℝ))))) := by
      rw [pi2_span_phiPair]
      exact Submodule.subset_span ⟨x, hx, rfl⟩
    have h3 : phi (Fin k) x
        ∈ Q1Subspace.pi1 (Submodule.span ℂ (phiPair '' (X : Set ((Fin k → ℝ) × (Fin k → ℝ))))) :=
      h.1 h2
    rw [pi1_span_phiPair] at h3
    exact mem_of_phi_mem_span (Q1Subspace.pi1 X) h3
  · intro lam
    have h2 := h.2 (lam : ℂ)
    rw [piLam_span_phiPair X lam, pi1_span_phiPair X] at h2
    rw [show Submodule.span ℂ ((phi (Fin k)) '' (Q1Subspace.piLam (K := ℝ) lam X : Set (Fin k → ℝ)))
        = UC (Q1Subspace.piLam (K := ℝ) lam X) from rfl,
      show Submodule.span ℂ ((phi (Fin k)) '' (Q1Subspace.pi1 X : Set (Fin k → ℝ)))
        = UC (Q1Subspace.pi1 X) from rfl] at h2
    rw [← finrank_UC (Q1Subspace.piLam (K := ℝ) lam X), ← finrank_UC (Q1Subspace.pi1 X)]
    exact h2


/-- **Real graph data for a saturating real minimum order.**  If `t_min^ℝ = a + 1 − s₀`, some
real design `R` realises a real subspace `W_ℝ` that is a graph `W(G,b)` with `b ≠ 0`, whose
complexification is feasible. -/
theorem exists_real_graph_of_tMinC_eq {p : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (hN : (N.map (algebraMap ℝ ℂ)).mulVecLin.range
      = (Matrix.fromRows ((C.map (algebraMap ℝ ℂ)) * (A.map (algebraMap ℝ ℂ)))
          (C.map (algebraMap ℝ ℂ))).mulVecLin.ker)
    (hsa : Module.finrank ℂ ↥(W0 A (N.map (algebraMap ℝ ℂ)) L0)
      ≤ Module.finrank ℂ ↥(Q1Subspace.pi1 (W0 A (N.map (algebraMap ℝ ℂ)) L0)
          ⊔ Q1Subspace.pi2 (W0 A (N.map (algebraMap ℝ ℂ)) L0)))
    (heq : tMinC A N L0
      = ((Module.finrank ℂ ↥(Q1Subspace.pi1 (W0 A (N.map (algebraMap ℝ ℂ)) L0)
            ⊔ Q1Subspace.pi2 (W0 A (N.map (algebraMap ℝ ℂ)) L0))
          + 1 - Module.finrank ℂ ↥(W0 A (N.map (algebraMap ℝ ℂ)) L0) : ℕ) : WithTop ℕ)) :
    ∃ (R : Matrix (Fin (Module.finrank ℂ ↥(Q1Subspace.pi1 (W0 A (N.map (algebraMap ℝ ℂ)) L0)
            ⊔ Q1Subspace.pi2 (W0 A (N.map (algebraMap ℝ ℂ)) L0))
          + 1 - Module.finrank ℂ ↥(W0 A (N.map (algebraMap ℝ ℂ)) L0))) (Fin n) ℝ)
      (U : Submodule ℝ (Fin k → ℝ)) (G : ↥U →ₗ[ℝ] ↥U) (b : ↥U),
      WRreal A N L0 R = graphExt U G b ∧ b ≠ 0 ∧
        Module.finrank ℝ ↥U
          = Module.finrank ℂ ↥(Q1Subspace.pi1 (W0 A (N.map (algebraMap ℝ ℂ)) L0)
              ⊔ Q1Subspace.pi2 (W0 A (N.map (algebraMap ℝ ℂ)) L0)) ∧
        W0 A (N.map (algebraMap ℝ ℂ)) L0 ≤ WR A (N.map (algebraMap ℝ ℂ)) L0 R ∧
        WR A (N.map (algebraMap ℝ ℂ)) L0 R ≤ TR A (N.map (algebraMap ℝ ℂ)) ∧
        IsFeasible (Submodule.span ℂ
          (phiPair '' (WRreal A N L0 R : Set ((Fin k → ℝ) × (Fin k → ℝ))))) := by
  classical
  set r : ℕ := Module.finrank ℂ ↥(Q1Subspace.pi1 (W0 A (N.map (algebraMap ℝ ℂ)) L0)
      ⊔ Q1Subspace.pi2 (W0 A (N.map (algebraMap ℝ ℂ)) L0))
    + 1 - Module.finrank ℂ ↥(W0 A (N.map (algebraMap ℝ ℂ)) L0) with hr
  have hdec : DecOrder C A L0 r :=
    (tMinC_le_iff_decC C A L0 N hN r).mp (by rw [hr]; exact le_of_eq heq)
  obtain ⟨R, hW0R, hWTR, hfeasR, htR⟩ :=
    decC_to_feasible_design (C := C) (A := A) (L0 := L0) (N := N.map (algebraMap ℝ ℂ)) hN hdec
  have hmem : t (W0 A (N.map (algebraMap ℝ ℂ)) L0) (WR A (N.map (algebraMap ℝ ℂ)) L0 R)
      ∈ tMinCSet A N L0 := ⟨_, R, hW0R, hfeasR, rfl⟩
  have hle : tMinC A N L0
      ≤ ((t (W0 A (N.map (algebraMap ℝ ℂ)) L0)
          (WR A (N.map (algebraMap ℝ ℂ)) L0 R) : ℕ) : WithTop ℕ) :=
    tMinC_le_of_mem hmem
  have hle' : (r : WithTop ℕ)
      ≤ ((t (W0 A (N.map (algebraMap ℝ ℂ)) L0)
          (WR A (N.map (algebraMap ℝ ℂ)) L0 R) : ℕ) : WithTop ℕ) := by
    rw [← heq]
    exact hle
  have ht : t (W0 A (N.map (algebraMap ℝ ℂ)) L0) (WR A (N.map (algebraMap ℝ ℂ)) L0 R) = r :=
    le_antisymm htR (WithTop.coe_le_coe.mp hle')
  have hdimW : Module.finrank ℂ ↥(WR A (N.map (algebraMap ℝ ℂ)) L0 R)
      = Module.finrank ℂ ↥(Q1Subspace.pi1 (W0 A (N.map (algebraMap ℝ ℂ)) L0)
          ⊔ Q1Subspace.pi2 (W0 A (N.map (algebraMap ℝ ℂ)) L0)) + 1 := by
    have hsub := t_eq_finrank_sub hW0R
    have hmono := Submodule.finrank_mono hW0R
    omega
  have hpi := pi1_eq_sup_of_finrank A (N.map (algebraMap ℝ ℂ)) L0 hW0R hfeasR hdimW
  have hXfeas : IsFeasible (Submodule.span ℂ
      (phiPair '' (WRreal A N L0 R : Set ((Fin k → ℝ) × (Fin k → ℝ))))) := by
    rw [← WR_eq_span_phiPair_WRreal]
    exact hfeasR
  have hXreal : IsFeasible (WRreal A N L0 R) := isFeasible_real_of_span_phiPair hXfeas
  have hdimX : Module.finrank ℝ ↥(WRreal A N L0 R)
      = Module.finrank ℝ ↥(Q1Subspace.pi1 (WRreal A N L0 R)) + 1 := by
    have h1 : Module.finrank ℝ ↥(WRreal A N L0 R)
        = Module.finrank ℂ ↥(WR A (N.map (algebraMap ℝ ℂ)) L0 R) := by
      rw [WR_eq_span_phiPair_WRreal, finrank_span_phiPair]
    have h2 : Module.finrank ℝ ↥(Q1Subspace.pi1 (WRreal A N L0 R))
        = Module.finrank ℂ ↥(Q1Subspace.pi1 (WR A (N.map (algebraMap ℝ ℂ)) L0 R)) := by
      rw [← finrank_UC (Q1Subspace.pi1 (WRreal A N L0 R))]
      show Module.finrank ℂ ↥(Submodule.span ℂ
          ((phi (Fin k)) '' (Q1Subspace.pi1 (WRreal A N L0 R) : Set (Fin k → ℝ))))
        = Module.finrank ℂ ↥(Q1Subspace.pi1 (WR A (N.map (algebraMap ℝ ℂ)) L0 R))
      rw [← pi1_span_phiPair (WRreal A N L0 R), ← WR_eq_span_phiPair_WRreal]
    rw [h1, h2, hpi]
    exact hdimW
  have hU : Module.finrank ℝ ↥(Q1Subspace.pi1 (WRreal A N L0 R))
      = Module.finrank ℂ ↥(Q1Subspace.pi1 (W0 A (N.map (algebraMap ℝ ℂ)) L0)
          ⊔ Q1Subspace.pi2 (W0 A (N.map (algebraMap ℝ ℂ)) L0)) := by
    rw [← finrank_UC (Q1Subspace.pi1 (WRreal A N L0 R))]
    show Module.finrank ℂ ↥(Submodule.span ℂ
        ((phi (Fin k)) '' (Q1Subspace.pi1 (WRreal A N L0 R) : Set (Fin k → ℝ))))
      = Module.finrank ℂ ↥(Q1Subspace.pi1 (W0 A (N.map (algebraMap ℝ ℂ)) L0)
          ⊔ Q1Subspace.pi2 (W0 A (N.map (algebraMap ℝ ℂ)) L0))
    rw [← pi1_span_phiPair (WRreal A N L0 R), ← WR_eq_span_phiPair_WRreal, hpi]
  obtain ⟨b, hb, G, hXG⟩ := exists_graph_representation (WRreal A N L0 R) hXreal hdimX
  exact ⟨R, Q1Subspace.pi1 (WRreal A N L0 R), G, b, hXG, hb, hU, hW0R, hWTR, hXfeas⟩


end Q1Paper.PaperII
