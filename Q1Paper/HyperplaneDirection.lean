/-
Q1Paper/HyperplaneDirection.lean

The direction theorem of the hyperplane-layer paper (Theorem 3).

In the hyperplane layer (c = k - ω = 1) the two functionals on `K = K₀`

    u ↦ inner ℝ u v        and        u ↦ inner ℝ u (A v)

are proportional.  Splitting `A v = w + z` with `w ∈ K` (this is the compression `M v`) and
`z ∈ Kᗮ` (the `A₂₁` component), proportionality is *equivalent* to `w = μ • v`, i.e. to `v`
being an eigenvector of the compression.  These are pure inner-product-space statements: no
matrices, no finiteness, no choice of coordinates.

Paper item: Theorem 3.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal

namespace Q1Paper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The functional `u ↦ ⟪u, v⟫`. -/
def innerLeft (v : E) : E →ₗ[ℝ] ℝ where
  toFun := fun u => inner ℝ u v
  map_add' := by intro x y; rw [inner_add_left]
  map_smul' := by intro r x; rw [real_inner_smul_left]; simp

@[simp] theorem innerLeft_apply (v u : E) : innerLeft v u = inner ℝ u v := rfl

section direction

variable (K : Submodule ℝ E) {A : E →ₗ[ℝ] E} {v w z : E} {μ : ℝ}

/-- **Paper Theorem 3, `⟹` direction.**  If `A v = w + z` with `w ∈ K`, `z ∈ Kᗮ`, and the
functional `u ↦ ⟪u, A v⟫` restricted to `K` is `μ` times `u ↦ ⟪u, v⟫`, then the `K`-component
of `A v` is `μ • v`: the direction is an eigenvector of the compression. -/
theorem compression_eq_of_proportional
    (hv : v ∈ K) (hw : w ∈ K) (hz : z ∈ Kᗮ) (hsplit : A v = w + z)
    (hprop : ∀ u ∈ K, inner ℝ u (A v) = μ * inner ℝ u v) : w = μ • v := by
  have hmem : w - μ • v ∈ K := K.sub_mem hw (K.smul_mem μ hv)
  have horth : w - μ • v ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hzw : inner ℝ u z = 0 := Submodule.inner_right_of_mem_orthogonal hu hz
    have h2 : inner ℝ u (A v) = inner ℝ u w := by
      rw [hsplit, inner_add_right, hzw, add_zero]
    have h3 : inner ℝ u w = μ * inner ℝ u v := by
      rw [← h2]
      exact hprop u hu
    have h4 : inner ℝ u (w - μ • v) = inner ℝ u w - μ * inner ℝ u v := by
      rw [inner_sub_right, inner_smul_right]
    rw [h4, h3, sub_self]
  have hbot : w - μ • v ∈ (⊥ : Submodule ℝ E) := by
    rw [← K.inf_orthogonal_eq_bot]
    exact ⟨hmem, horth⟩
  have hzero : w - μ • v = 0 := by simpa using hbot
  exact sub_eq_zero.mp hzero

/-- **Paper Theorem 3, `⟸` direction.** -/
theorem proportional_of_compression
    (hz : z ∈ Kᗮ) (hsplit : A v = w + z) (hcomp : w = μ • v) :
    ∀ u ∈ K, inner ℝ u (A v) = μ * inner ℝ u v := by
  intro u hu
  have hzw : inner ℝ u z = 0 := Submodule.inner_right_of_mem_orthogonal hu hz
  rw [hsplit, inner_add_right, hzw, add_zero, hcomp, inner_smul_right]

/-- **Paper Theorem 3, invariant form.**  The two functionals on `K` are proportional with factor
`μ` if and only if the compression sends `v` to `μ • v`. -/
theorem direction_iff
    (hv : v ∈ K) (hw : w ∈ K) (hz : z ∈ Kᗮ) (hsplit : A v = w + z) :
    (∀ u ∈ K, inner ℝ u (A v) = μ * inner ℝ u v) ↔ w = μ • v :=
  ⟨compression_eq_of_proportional K hv hw hz hsplit,
   fun h => proportional_of_compression K hz hsplit h⟩

end direction

end Q1Paper
