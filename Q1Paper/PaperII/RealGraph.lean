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

end Q1Paper.PaperII
