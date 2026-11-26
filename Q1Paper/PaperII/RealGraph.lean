/-
Q1Paper/PaperII/RealGraph.lean

Paper II, Proposition `prop:tight`: the complexification of a real graph extension.

A real linear map `G` on `U ≤ (Fin k → ℝ)` that preserves `U`, together with `b ∈ U`, has a
graph `W(G,b) ⊆ (Fin k → ℝ) × (Fin k → ℝ)`; the paper's real-design criterion speaks of its
image in the complex pair space.  This module builds that image:

* `Gfun`     -- the complexified matrix as a ℂ-linear map on the ambient space;
* `GcU`      -- its restriction to a ℂ-linear endomorphism of `UC U`;
* `GcU_phi`  -- its value on `phi u` is `phi (G u)`.
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

end Q1Paper.PaperII
