/-
Q1Paper/HyperplanePrescribed.lean

The prescribed-row lemmas of the hyperplane-layer paper (Lemma 4).

Two consequences of `V₀ ⊆ V` are separated in the paper:

* the direction must annihilate the prescribed rows: `v ∈ E_μ^0` means `L₀ v = 0` and
  `L₀ (A v) = 0`, which is exactly `V₀ ⊆ (span{v, A v})ᗮ`;
* modulo `D_v` the fibre must contain the prescribed rows, and the identity
  `V₀ ⊓ D_v = V₀ ⊓ K₀` is what makes `δ = dim V₀ - dim (V₀ ⊓ K₀)` independent of the direction.

Both are pure submodule identities.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal

namespace Q1Paper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Paper Lemma 4, automatic orthogonality.**  If every row of `V₀` annihilates both `v` and
`A v` — which is what `v ∈ E_μ^0` says — then `V₀ ⊆ (span{v, A v})ᗮ`, with no further hypothesis
and uniformly in the direction. -/
theorem le_orthogonal_span_pair {A : E →ₗ[ℝ] E} {v : E} {V0 : Submodule ℝ E}
    (h1 : ∀ x ∈ V0, inner ℝ x v = 0) (h2 : ∀ x ∈ V0, inner ℝ x (A v) = 0) :
    V0 ≤ (Submodule.span ℝ ({v, A v} : Set E))ᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro y hy
  exact Submodule.span_induction (p := fun y _ => inner ℝ y x = 0)
    (fun y hy' => by
      rcases hy' with rfl | rfl
      · rw [real_inner_comm]
        exact h1 x hx
      · rw [real_inner_comm]
        exact h2 x hx)
    (by simp)
    (fun a b _ _ ha hb => by rw [inner_add_left, ha, hb, add_zero])
    (fun r a _ ha => by rw [real_inner_smul_left, ha, mul_zero])
    hy

/-- **Paper Lemma 4, independence of `δ`.**  With `D_v = K₀ ⊓ U_vᗮ` and `V₀ ≤ U_vᗮ`,
`V₀ ⊓ D_v = V₀ ⊓ K₀`.  Hence `δ = dim V₀ - dim (V₀ ⊓ K₀)` does not depend on the direction. -/
theorem inf_inf_orthogonal_eq {V0 K U : Submodule ℝ E} (hU : V0 ≤ Uᗮ) :
    V0 ⊓ (K ⊓ Uᗮ) = V0 ⊓ K := by
  refine le_antisymm ?_ ?_
  · exact inf_le_inf_left V0 inf_le_left
  · exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hU))

end Q1Paper
