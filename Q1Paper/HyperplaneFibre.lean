/-
Q1Paper/HyperplaneFibre.lean

The fibre of the hyperplane-layer paper at a fixed direction (Lemma 2, numerical part).

With `D_v = K ⊓ span{v, A v}ᗮ` and the two functionals proportional (`φ_Av = μ • φ_v` on `K`),
`D_v` is the kernel of the functional `u ↦ ⟪u, v⟫` restricted to `K`.  Since `v ≠ 0` that
functional is nonzero, so `D_v` is a hyperplane of `K`:

    finrank ℝ D_v + 1 = finrank ℝ K .

Paper item: Lemma 2 (the dimension `k - 1` of the fibre's common kernel).
-/

import Q1Paper.HyperplaneDirection
import Q1Paper.HyperplanePrescribed
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Module

namespace Q1Paper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Membership in the orthogonal of `span{v, A v}`.**  A vector is orthogonal to the span of the
two directions if and only if it annihilates both. -/
theorem mem_orthogonal_span_pair_iff {A : E →ₗ[ℝ] E} {v w : E} :
    w ∈ (Submodule.span ℝ ({v, A v} : Set E))ᗮ ↔ inner ℝ w v = 0 ∧ inner ℝ w (A v) = 0 := by
  have hmemv : v ∈ Submodule.span ℝ ({v, A v} : Set E) := Submodule.subset_span (by simp)
  have hmemAv : (A v) ∈ Submodule.span ℝ ({v, A v} : Set E) := Submodule.subset_span (by simp)
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [real_inner_comm]
      exact Submodule.inner_right_of_mem_orthogonal hmemv h
    · rw [real_inner_comm]
      exact Submodule.inner_right_of_mem_orthogonal hmemAv h
  · rintro ⟨h1, h2⟩
    refine le_orthogonal_span_pair (V0 := Submodule.span ℝ ({w} : Set E)) ?_ ?_
      (Submodule.mem_span_singleton_self w)
    · intro x hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
      rw [← hc, real_inner_smul_left, h1, mul_zero]
    · intro x hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
      rw [← hc, real_inner_smul_left, h2, mul_zero]

/-- **Paper Lemma 2, structural form.**  Under proportionality, `D_v = K ⊓ span{v, A v}ᗮ` is the
kernel of the functional `u ↦ ⟪u, v⟫` on `K`. -/
theorem Dv_eq_ker (K : Submodule ℝ E) {A : E →ₗ[ℝ] E} {v : E} {μ : ℝ}
    (hprop : ∀ u ∈ K, inner ℝ u (A v) = μ * inner ℝ u v) :
    K ⊓ (Submodule.span ℝ ({v, A v} : Set E))ᗮ
      = (LinearMap.ker ((innerLeft v).comp K.subtype)).map K.subtype := by
  ext x
  constructor
  · rintro ⟨hxK, hxorth⟩
    obtain ⟨h1, _⟩ := mem_orthogonal_span_pair_iff.mp hxorth
    exact ⟨⟨x, hxK⟩, by simpa using h1, rfl⟩
  · rintro ⟨x', hx', rfl⟩
    have h1 : inner ℝ (x' : E) v = 0 := by simpa using hx'
    refine ⟨x'.2, ?_⟩
    refine mem_orthogonal_span_pair_iff.mpr ⟨h1, ?_⟩
    show inner ℝ (x' : E) (A v) = 0
    rw [hprop (x' : E) x'.2, h1, mul_zero]

/-- **Paper Lemma 2, numerical form.**  If `v ∈ K`, `v ≠ 0` and the two functionals on `K` are
proportional, then `D_v` is a hyperplane of `K`: `finrank ℝ D_v + 1 = finrank ℝ K`. -/
theorem finrank_Dv [FiniteDimensional ℝ E] (K : Submodule ℝ E) {A : E →ₗ[ℝ] E} {v : E} {μ : ℝ}
    (hv : v ∈ K) (hne : v ≠ 0) (hprop : ∀ u ∈ K, inner ℝ u (A v) = μ * inner ℝ u v) :
    finrank ℝ ↥(K ⊓ (Submodule.span ℝ ({v, A v} : Set E))ᗮ) + 1 = finrank ℝ K := by
  have heq := Dv_eq_ker K hprop
  have hφ : (innerLeft v).comp K.subtype ≠ 0 := by
    intro h
    have h0 : inner ℝ (v : E) v = 0 := by
      have h1 := congrArg (fun g => g ⟨v, hv⟩) h
      simpa using h1
    exact hne (inner_self_eq_zero.mp h0)
  have hinj : Function.Injective K.subtype := Submodule.subtype_injective K
  have hfin : finrank ℝ ((LinearMap.ker ((innerLeft v).comp K.subtype)).map K.subtype)
      = finrank ℝ (LinearMap.ker ((innerLeft v).comp K.subtype)) :=
    (Submodule.equivMapOfInjective K.subtype hinj
      (LinearMap.ker ((innerLeft v).comp K.subtype))).finrank_eq.symm
  rw [heq, hfin]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero hφ

end Q1Paper
