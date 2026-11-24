/-
Q1Paper/Strata.lean

Paper item: Proposition 5 of `paper/current/paper_III_hyperplane.tex`, labels `sec3:prop:strata`,
`sec3:lem:eigen`, `sec3:lem:dimU`, `sec3:rem:rankcases` — "Eigen and non-eigen directions".

Paper statement (verbatim).  Let `μ ∈ Spec_ℝ(M)` and `v ∈ E_μ \ {0}`.  Then:

 (i) `A v ∈ span(v) ↔ A₂₁ v = 0`; the *eigen directions* form the subspace
     `E_μ^eig = E_μ ∩ ker A₂₁`, whose projectivization `P(E_μ^eig) ⊆ P(E_μ)` is a projective
     subspace, while the *non-eigen directions* form its complement, a nonempty Zariski-open
     subset whenever `E_μ^eig ≠ E_μ`;
(ii) if `A₂₁ v = 0` then `U_v = span(v)` and `dim U_v = 1`, whereas if `A₂₁ v ≠ 0` then `v, A v`
     are independent and `dim U_v = 2`; accordingly `dim U_v^⊥ = n - 1` or `n - 2`;
(iii) with prescribed rows the two branches are `B_μ^eig = P(E_μ^0 ∩ ker A₂₁)` and
     `B_μ^non = P(E_μ^0) \ B_μ^eig`, which are disjoint and cover `P(E_μ^0)`; according to
     `rank(A₂₁|_{E_μ^0})` the second is empty (rank zero), the first is empty (full rank), or both
     are nonempty — the first screening step of Section 4.

Dictionary: `K₀` is a submodule `K` of the real inner product space `E` (`E = ℝⁿ`), `A : E →ₗ E`;
the paper's compression `M = π_{K₀} A` is `compressionPart K A` (an endomorphism of `E` once
composed with `K₀.subtype`: `compressionEnd K A`), and `A₂₁ = π_{K₀ᗮ} A` is `normalComp K A`;
`E_μ = ker(M - μ I)` is `compressionEigenspace K A μ`, `U_v = span{v, A v}` is
`directionSpan A v`.  The subspace `E⁰` of (iii) is an arbitrary `E0 : Submodule ℝ E`; it is the
paper's `E_μ^0` when instantiated at `E0 = compressionEigenspace K A μ ⊓ ker L₀ ⊓ ker (L₀ ∘ A)`.

Scope.  Parts (i) (the equivalence, and "eigen directions form a submodule"), (ii) (both values of
`dim U_v` and of `dim U_vᗮ`) and (iii) (disjointness, exhaustiveness, the description of the eigen
branch as the complement of the concrete condition `A₂₁ v ≠ 0`, and the rank criterion deciding
which branch is empty) are proved below.  The projectivisation `P(·)` and the Zariski-topology
half of the paper's claims are *not* formalised: the library has no projective-space or
Zariski-topology API, and the Grassmann-bundle statements built on this stratification
(`sec3:lem:constantrank`, `sec3:thm:param`) are paper-level in `LEAN_GAPS.md`.
-/

import Q1Paper.HyperplaneDirection
import Q1Paper.HyperplaneFibre
import Q1Paper.HyperplanePrescribed
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Module

set_option linter.unusedSectionVars false

namespace Q1Paper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The compression `M` and the normal component `A₂₁` -/

section splitting

variable [FiniteDimensional ℝ E]

/-- The `K₀`-component of `A`, i.e. the paper's compression `M = π_{K₀} A`, as a map into `K₀`. -/
noncomputable def compressionPart (K : Submodule ℝ E) (A : E →ₗ[ℝ] E) : E →ₗ[ℝ] K :=
  (K.projectionOnto Kᗮ K.isCompl_orthogonal).comp A

/-- The `K₀ᗮ`-component of `A`, i.e. the paper's `A₂₁ = π_{K₀ᗮ} A`, as a map into `K₀ᗮ`.

The paper defines `A₂₁` on `K₀` only; on all of `E` the same formula is used here so that kernels
and ranks are those of a linear map. -/
noncomputable def normalComp (K : Submodule ℝ E) (A : E →ₗ[ℝ] E) : E →ₗ[ℝ] Kᗮ :=
  ((Kᗮ).projectionOnto K K.isCompl_orthogonal.symm).comp A

/-- `M` as an endomorphism of `E`: the compression, read in the ambient space. -/
noncomputable def compressionEnd (K : Submodule ℝ E) (A : E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  K.subtype.comp (compressionPart K A)

/-- The compression component lies in `K₀`. -/
theorem compressionPart_mem (K : Submodule ℝ E) (A : E →ₗ[ℝ] E) (v : E) :
    ((compressionPart K A v : K) : E) ∈ K := (compressionPart K A v).2

/-- The normal component lies in `K₀ᗮ`. -/
theorem normalComp_mem (K : Submodule ℝ E) (A : E →ₗ[ℝ] E) (v : E) :
    ((normalComp K A v : Kᗮ) : E) ∈ Kᗮ := (normalComp K A v).2

/-- The splitting of the paper's proof: `A v = M v + A₂₁ v`. -/
theorem compressionPart_add_normalComp (K : Submodule ℝ E) (A : E →ₗ[ℝ] E) (v : E) :
    ((compressionPart K A v : K) : E) + ((normalComp K A v : Kᗮ) : E) = A v := by
  have h := Submodule.projection_add_projection_eq_self (p := K) (q := Kᗮ)
    K.isCompl_orthogonal (A v)
  simpa [compressionPart, normalComp] using h

/-- `A₂₁ v = 0` if and only if `A v ∈ K₀`: the normal component is exactly the obstruction to
staying inside the compression layer. -/
theorem normalComp_eq_zero_iff (K : Submodule ℝ E) (A : E →ₗ[ℝ] E) (v : E) :
    normalComp K A v = 0 ↔ A v ∈ K := by
  change ((Kᗮ).projectionOnto K K.isCompl_orthogonal.symm) (A v) = 0 ↔ A v ∈ K
  exact Submodule.projectionOnto_apply_eq_zero_iff _

/-! ### Paper Proposition 5 (i): `A v ∈ span(v) ⟺ A₂₁ v = 0` -/

/-- The eigenspace `E_μ = ker(M - μ I)` of the compression, intersected with `K₀` (the paper's
`E_μ` lies in `K₀` by construction). -/
noncomputable def compressionEigenspace (K : Submodule ℝ E) (A : E →ₗ[ℝ] E) (μ : ℝ) :
    Submodule ℝ E :=
  LinearMap.ker (compressionEnd K A - μ • LinearMap.id) ⊓ K

/-- Membership in `E_μ`. -/
theorem mem_compressionEigenspace_iff {K : Submodule ℝ E} {A : E →ₗ[ℝ] E} {μ : ℝ} {v : E} :
    v ∈ compressionEigenspace K A μ ↔
      v ∈ K ∧ ((compressionPart K A v : K) : E) = μ • v := by
  rw [compressionEigenspace, Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · rintro ⟨hker, hK⟩
    exact ⟨hK, by simpa [compressionEnd, sub_eq_zero] using hker⟩
  · rintro ⟨hK, hcomp⟩
    exact ⟨by simpa [compressionEnd, sub_eq_zero] using hcomp, hK⟩

/-- **Paper Proposition 5 (i), forward half** (no eigenspace hypothesis needed): if `A v` is a
multiple of `v`, then `A₂₁ v = 0`. -/
theorem normalComp_eq_zero_of_mem_span_singleton (K : Submodule ℝ E) {A : E →ₗ[ℝ] E} {v : E}
    (hv : v ∈ K) (h : A v ∈ Submodule.span ℝ ({v} : Set E)) : normalComp K A v = 0 := by
  rw [normalComp_eq_zero_iff]
  exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv)) h

/-- **Paper Proposition 5 (i).**  For a direction `v` in the eigenspace `E_μ`,
`A v` is a multiple of `v` if and only if the normal component `A₂₁ v` vanishes. -/
theorem mem_span_singleton_iff_normalComp_eq_zero {K : Submodule ℝ E} {A : E →ₗ[ℝ] E} {μ : ℝ}
    {v : E} (hv : v ∈ compressionEigenspace K A μ) :
    A v ∈ Submodule.span ℝ ({v} : Set E) ↔ normalComp K A v = 0 := by
  refine ⟨normalComp_eq_zero_of_mem_span_singleton K
    (mem_compressionEigenspace_iff.mp hv).1, fun h => ?_⟩
  obtain ⟨_, hcomp⟩ := mem_compressionEigenspace_iff.mp hv
  have hAv : A v = μ • v := by
    rw [← compressionPart_add_normalComp K A v, h]
    simpa using hcomp
  rw [hAv]
  exact Submodule.smul_mem _ μ (Submodule.subset_span (Set.mem_singleton v))

/-! ### The two strata -/

/-- The **eigen stratum** `E_μ^eig = E_μ ∩ ker A₂₁` of the paper, for an arbitrary subspace
`E0` in place of `E_μ` (so that (iii) with prescribed rows is the case
`E0 = E_μ ⊓ ker L₀ ⊓ ker (L₀ ∘ A)`). -/
noncomputable def eigenStratum (K : Submodule ℝ E) (A : E →ₗ[ℝ] E) (E0 : Submodule ℝ E) :
    Submodule ℝ E :=
  E0 ⊓ LinearMap.ker (normalComp K A)

/-- The **non-eigen directions**: the points of `E0` on which `A₂₁` does not vanish.  This is the
paper's complement stratum, the concrete condition being `A₂₁ v ≠ 0`. -/
def nonEigenStratum (K : Submodule ℝ E) (A : E →ₗ[ℝ] E) (E0 : Submodule ℝ E) : Set E :=
  {v | v ∈ E0 ∧ normalComp K A v ≠ 0}

/-- Membership in the eigen stratum. -/
@[simp] theorem mem_eigenStratum_iff {K : Submodule ℝ E} {A : E →ₗ[ℝ] E} {E0 : Submodule ℝ E}
    {v : E} : v ∈ eigenStratum K A E0 ↔ v ∈ E0 ∧ normalComp K A v = 0 := by
  rw [eigenStratum, Submodule.mem_inf, LinearMap.mem_ker]

/-- Membership in the non-eigen stratum (definitional). -/
theorem mem_nonEigenStratum_iff {K : Submodule ℝ E} {A : E →ₗ[ℝ] E} {E0 : Submodule ℝ E}
    {v : E} : v ∈ nonEigenStratum K A E0 ↔ v ∈ E0 ∧ normalComp K A v ≠ 0 := Iff.rfl

/-- The eigen stratum is a subspace of `E0`: its projectivisation is a projective subspace of
`P(E0)` (the projectivisation itself is paper-level, see the module docstring). -/
theorem eigenStratum_le (K : Submodule ℝ E) (A : E →ₗ[ℝ] E) (E0 : Submodule ℝ E) :
    eigenStratum K A E0 ≤ E0 := inf_le_left

/-- The eigen directions inside `E_μ` are exactly the points of `E_μ` at which `A v` is a multiple
of `v` — the paper's `E_μ^eig = E_μ ∩ ker A₂₁` in geometric form. -/
theorem mem_eigenStratum_iff_mem_span {K : Submodule ℝ E} {A : E →ₗ[ℝ] E} {μ : ℝ} {v : E} :
    v ∈ eigenStratum K A (compressionEigenspace K A μ) ↔
      v ∈ compressionEigenspace K A μ ∧ A v ∈ Submodule.span ℝ ({v} : Set E) := by
  rw [mem_eigenStratum_iff]
  constructor
  · rintro ⟨hμ, h0⟩
    exact ⟨hμ, (mem_span_singleton_iff_normalComp_eq_zero hμ).mpr h0⟩
  · rintro ⟨hμ, hspan⟩
    exact ⟨hμ, (mem_span_singleton_iff_normalComp_eq_zero hμ).mp hspan⟩

/-- The eigen stratum is a cone (a union of lines): it is closed under scalar multiplication. -/
theorem eigenStratum_smul_mem {K : Submodule ℝ E} {A : E →ₗ[ℝ] E} {E0 : Submodule ℝ E} {v : E}
    (c : ℝ) (hv : v ∈ eigenStratum K A E0) : c • v ∈ eigenStratum K A E0 :=
  (eigenStratum K A E0).smul_mem c hv

/-- The non-eigen stratum is a cone as well: scaling by a nonzero scalar preserves it. -/
theorem nonEigenStratum_smul_mem_iff {K : Submodule ℝ E} {A : E →ₗ[ℝ] E} {E0 : Submodule ℝ E}
    {v : E} {c : ℝ} (hc : c ≠ 0) :
    c • v ∈ nonEigenStratum K A E0 ↔ v ∈ nonEigenStratum K A E0 := by
  constructor
  · rintro ⟨hmem, hne⟩
    refine ⟨?_, ?_⟩
    · have := E0.smul_mem c⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    · intro h0
      apply hne
      rw [map_smul, h0, smul_zero]
  · rintro ⟨hmem, hne⟩
    exact ⟨E0.smul_mem c hmem, by rw [map_smul]; exact smul_ne_zero hc hne⟩

/-- **Paper Proposition 5 (iii), disjointness.**  No direction is both eigen and non-eigen. -/
theorem eigenStratum_disjoint_nonEigenStratum (K : Submodule ℝ E) (A : E →ₗ[ℝ] E)
    (E0 : Submodule ℝ E) : ∀ v, v ∈ eigenStratum K A E0 → v ∉ nonEigenStratum K A E0 := by
  intro v hv hnv
  exact (mem_nonEigenStratum_iff.mp hnv).2 (mem_eigenStratum_iff.mp hv).2

/-- **Paper Proposition 5 (iii), exhaustiveness.**  Every direction of `E0` is eigen or non-eigen. -/
theorem mem_eigenStratum_or_nonEigenStratum (K : Submodule ℝ E) (A : E →ₗ[ℝ] E)
    (E0 : Submodule ℝ E) (v : E) :
    v ∈ E0 ↔ v ∈ eigenStratum K A E0 ∨ v ∈ nonEigenStratum K A E0 := by
  classical
  by_cases h : normalComp K A v = 0 <;> simp [eigenStratum, nonEigenStratum, h]

/-- **Paper Proposition 5 (iii), complement form.**  Inside `E0` the eigen directions are the
complement of the concrete condition `A₂₁ v ≠ 0`. -/
theorem nonEigenStratum_eq_sdiff (K : Submodule ℝ E) (A : E →ₗ[ℝ] E) (E0 : Submodule ℝ E) :
    nonEigenStratum K A E0 = (E0 : Set E) \ eigenStratum K A E0 := by
  ext v
  simp only [mem_nonEigenStratum_iff, Set.mem_sdiff, SetLike.mem_coe, mem_eigenStratum_iff]
  tauto

/-- **Paper Proposition 5 (i), subspace half.**  The non-eigen stratum is nonempty as soon as the
eigen stratum is a proper subspace of `E0` (the paper's "nonempty whenever `E_μ^eig ≠ E_μ`"). -/
theorem exists_nonEigenStratum_of_eigenStratum_ne (K : Submodule ℝ E) (A : E →ₗ[ℝ] E)
    (E0 : Submodule ℝ E) (h : eigenStratum K A E0 ≠ E0) :
    ∃ v, v ∈ nonEigenStratum K A E0 := by
  by_contra hc
  apply h
  refine le_antisymm inf_le_left ?_
  intro v hv
  by_cases hzero : normalComp K A v = 0
  · exact ⟨hv, hzero⟩
  · exact False.elim (hc ⟨v, ⟨hv, hzero⟩⟩)

/-! ### Paper Proposition 5 (ii): the dimension of `U_v = span{v, A v}` -/

/-- The paper's `U_v = span{v, A v}`. -/
def directionSpan (A : E →ₗ[ℝ] E) (v : E) : Submodule ℝ E :=
  Submodule.span ℝ ({v, A v} : Set E)

/-- **Paper Proposition 5 (ii), eigen branch.**  If `A₂₁ v = 0` then `U_v = span(v)`. -/
theorem directionSpan_eq_span_singleton {K : Submodule ℝ E} {A : E →ₗ[ℝ] E} {μ : ℝ} {v : E}
    (hv : v ∈ compressionEigenspace K A μ) (h : normalComp K A v = 0) :
    directionSpan A v = Submodule.span ℝ ({v} : Set E) := by
  obtain ⟨_, hcomp⟩ := mem_compressionEigenspace_iff.mp hv
  have hAv : A v = μ • v := by
    rw [← compressionPart_add_normalComp K A v, h]
    simpa using hcomp
  refine le_antisymm ?_ (Submodule.span_mono (Set.singleton_subset_iff.mpr ?_))
  · refine Submodule.span_le.mpr ?_
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact Submodule.subset_span (by simp)
    · rw [hx, hAv]
      exact Submodule.smul_mem _ μ (Submodule.subset_span (by simp))
  · exact Set.mem_insert_iff.mpr (Or.inl rfl)

/-- **Paper Proposition 5 (ii), eigen branch.**  If `A₂₁ v = 0` then `dim U_v = 1`. -/
theorem finrank_directionSpan_eigen {K : Submodule ℝ E} {A : E →ₗ[ℝ] E} {μ : ℝ} {v : E}
    (hvne : v ≠ 0) (hv : v ∈ compressionEigenspace K A μ) (h : normalComp K A v = 0) :
    finrank ℝ (directionSpan A v) = 1 := by
  rw [directionSpan_eq_span_singleton hv h]
  exact finrank_span_singleton hvne

/-- **Paper Proposition 5 (ii), non-eigen branch.**  If `A₂₁ v ≠ 0` then `v` and `A v` are
linearly independent. -/
theorem linearIndependent_pair_of_normalComp_ne_zero {K : Submodule ℝ E} {A : E →ₗ[ℝ] E}
    {v : E} (hv : v ∈ K) (hne : normalComp K A v ≠ 0) : LinearIndependent ℝ ![v, A v] := by
  have hvne : v ≠ 0 := by
    rintro rfl
    exact hne (map_zero _)
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hspan : A v ∉ Submodule.span ℝ ({v} : Set E) := fun h =>
    hne (normalComp_eq_zero_of_mem_span_singleton K hv h)
  have ht : t = 0 := by
    by_contra ht
    apply hspan
    refine Submodule.mem_span_singleton.mpr ⟨-(t⁻¹ * s), ?_⟩
    have h1 : t • A v = -(s • v) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hst
    calc (-(t⁻¹ * s)) • v = -((t⁻¹ * s) • v) := by rw [neg_smul]
      _ = -(t⁻¹ • (s • v)) := by rw [smul_smul]
      _ = t⁻¹ • (-(s • v)) := by rw [← smul_neg]
      _ = t⁻¹ • (t • A v) := by rw [h1]
      _ = A v := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
  rw [ht, zero_smul, add_zero] at hst
  refine ⟨?_, ht⟩
  rcases smul_eq_zero.mp hst with h | h
  · exact h
  · exact absurd h hvne

/-- **Paper Proposition 5 (ii), non-eigen branch.**  If `A₂₁ v ≠ 0` then `dim U_v = 2`. -/
theorem finrank_directionSpan_nonEigen {K : Submodule ℝ E} {A : E →ₗ[ℝ] E} {v : E}
    (hv : v ∈ K) (hne : normalComp K A v ≠ 0) : finrank ℝ (directionSpan A v) = 2 := by
  have hind := linearIndependent_pair_of_normalComp_ne_zero hv hne
  have hcard := finrank_span_eq_card (R := ℝ) hind
  have hrange : Set.range ![v, A v] = ({v, A v} : Set E) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  rw [directionSpan, ← hrange, hcard, Fintype.card_fin]

/-- The dimension of `U_vᗮ` is `n - dim U_v`. -/
theorem finrank_orthogonal_directionSpan (A : E →ₗ[ℝ] E) (v : E) :
    finrank ℝ (directionSpan A v)ᗮ = finrank ℝ E - finrank ℝ (directionSpan A v) := by
  have h := Submodule.finrank_add_finrank_orthogonal (directionSpan A v)
  omega

/-- **Paper Proposition 5 (ii).**  On the eigen branch `dim U_vᗮ = n - 1`. -/
theorem finrank_orthogonal_directionSpan_eigen {K : Submodule ℝ E} {A : E →ₗ[ℝ] E} {μ : ℝ}
    {v : E} (hvne : v ≠ 0) (hv : v ∈ compressionEigenspace K A μ)
    (h : normalComp K A v = 0) :
    finrank ℝ (directionSpan A v)ᗮ = finrank ℝ E - 1 := by
  rw [finrank_orthogonal_directionSpan, finrank_directionSpan_eigen hvne hv h]

/-- **Paper Proposition 5 (ii).**  On the non-eigen branch `dim U_vᗮ = n - 2`. -/
theorem finrank_orthogonal_directionSpan_nonEigen {K : Submodule ℝ E} {A : E →ₗ[ℝ] E} {v : E}
    (hv : v ∈ K) (hne : normalComp K A v ≠ 0) :
    finrank ℝ (directionSpan A v)ᗮ = finrank ℝ E - 2 := by
  rw [finrank_orthogonal_directionSpan, finrank_directionSpan_nonEigen hv hne]

/-! ### Paper Proposition 5 (iii): the rank criterion for the two branches -/

/-- The restriction `A₂₁|_{E⁰} : E⁰ → K₀ᗮ` whose rank decides which stratum is empty. -/
noncomputable def normalRestrict (K : Submodule ℝ E) (A : E →ₗ[ℝ] E) (E0 : Submodule ℝ E) :
    E0 →ₗ[ℝ] Kᗮ :=
  (normalComp K A).comp E0.subtype

/-- The restriction is evaluation of the normal component. -/
theorem normalRestrict_apply (K : Submodule ℝ E) (A : E →ₗ[ℝ] E) (E0 : Submodule ℝ E)
    (x : E0) : normalRestrict K A E0 x = normalComp K A (x : E) := rfl

/-- Vanishing of the restricted `A₂₁` makes the whole of `E0` eigen (rank zero case). -/
theorem eigenStratum_eq_of_normalRestrict_eq_zero (K : Submodule ℝ E) (A : E →ₗ[ℝ] E)
    (E0 : Submodule ℝ E) (h : normalRestrict K A E0 = 0) : eigenStratum K A E0 = E0 := by
  refine le_antisymm inf_le_left ?_
  intro v hv
  refine ⟨hv, ?_⟩
  have := congrArg (fun f : E0 →ₗ[ℝ] Kᗮ => f ⟨v, hv⟩) h
  simpa [normalRestrict] using this

/-- `A₂₁` vanishes on `E0` exactly when every direction of `E0` is eigen. -/
theorem normalRestrict_eq_zero_iff_eigenStratum_eq_top (K : Submodule ℝ E) (A : E →ₗ[ℝ] E)
    (E0 : Submodule ℝ E) : normalRestrict K A E0 = 0 ↔ eigenStratum K A E0 = E0 := by
  refine ⟨eigenStratum_eq_of_normalRestrict_eq_zero K A E0, fun h => ?_⟩
  refine LinearMap.ext fun x => ?_
  have hx : (x : E) ∈ eigenStratum K A E0 := by rw [h]; exact x.2
  simpa [normalRestrict] using (mem_eigenStratum_iff.mp hx).2

/-- **Paper Proposition 5 (iii), rank zero case.**  If `rank(A₂₁|_{E⁰}) = 0` the non-eigen
stratum is empty. -/
theorem nonEigenStratum_eq_empty_iff (K : Submodule ℝ E) (A : E →ₗ[ℝ] E) (E0 : Submodule ℝ E) :
    nonEigenStratum K A E0 = ∅ ↔ normalRestrict K A E0 = 0 := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨v, hv⟩ : ∃ v : E0, normalRestrict K A E0 v ≠ 0 := by
      by_contra hc
      apply hne
      refine LinearMap.ext fun x => ?_
      by_contra hx
      exact hc ⟨x, hx⟩
    have hmem : (v : E) ∈ nonEigenStratum K A E0 := ⟨v.2, by simpa [normalRestrict] using hv⟩
    rw [h] at hmem
    exact hmem
  · intro h
    refine Set.eq_empty_iff_forall_notMem.mpr fun v hv => ?_
    have := congrArg (fun f : E0 →ₗ[ℝ] Kᗮ => f ⟨v, hv.1⟩) h
    exact hv.2 (by simpa [normalRestrict] using this)

/-- **Paper Proposition 5 (iii), rank zero case in rank form.**  The non-eigen stratum is empty
exactly when `rank(A₂₁|_{E⁰}) = 0`. -/
theorem nonEigenStratum_eq_empty_iff_finrank_range (K : Submodule ℝ E) (A : E →ₗ[ℝ] E)
    (E0 : Submodule ℝ E) :
    nonEigenStratum K A E0 = ∅ ↔
      finrank ℝ (LinearMap.range (normalRestrict K A E0)) = 0 := by
  rw [nonEigenStratum_eq_empty_iff, ← LinearMap.range_eq_bot, ← Submodule.finrank_eq_zero]

/-- `E_μ^eig = ⊥` (the eigen branch empty) iff `A₂₁|_{E⁰}` is injective. -/
theorem eigenStratum_eq_bot_iff_injective (K : Submodule ℝ E) (A : E →ₗ[ℝ] E)
    (E0 : Submodule ℝ E) :
    eigenStratum K A E0 = ⊥ ↔ Function.Injective (normalRestrict K A E0) := by
  constructor
  · intro h x y hxy
    have hmem : (x : E) - (y : E) ∈ eigenStratum K A E0 := by
      refine ⟨E0.sub_mem x.2 y.2, ?_⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      have hxy' : normalComp K A (x : E) = normalComp K A (y : E) := hxy
      rw [map_sub, hxy', sub_self]
    have hzero : (x : E) - (y : E) = 0 := by
      have hbot := h ▸ hmem
      simpa using hbot
    exact Subtype.ext (sub_eq_zero.mp hzero)
  · intro hinj
    refine le_antisymm ?_ bot_le
    intro v hv
    obtain ⟨hE0, hker⟩ := mem_eigenStratum_iff.mp hv
    have hsub : (⟨v, hE0⟩ : E0) = 0 := by
      apply hinj
      show normalComp K A v = normalComp K A ((0 : E0) : E)
      rw [hker]
      simp
    have hzero : v = 0 := by simpa using congrArg (fun z : E0 => (z : E)) hsub
    simpa using hzero

/-- Rank-nullity for the restricted normal component. -/
theorem finrank_range_normalRestrict_add_finrank_ker (K : Submodule ℝ E) (A : E →ₗ[ℝ] E)
    (E0 : Submodule ℝ E) :
    finrank ℝ (LinearMap.range (normalRestrict K A E0))
        + finrank ℝ (LinearMap.ker (normalRestrict K A E0)) = finrank ℝ E0 :=
  LinearMap.finrank_range_add_finrank_ker _

/-- **Paper Proposition 5 (iii), full rank case.**  `E_μ^eig = ⊥` (the eigen branch empty) iff
`rank(A₂₁|_{E⁰}) = dim E⁰`. -/
theorem eigenStratum_eq_bot_iff_finrank_range (K : Submodule ℝ E) (A : E →ₗ[ℝ] E)
    (E0 : Submodule ℝ E) :
    eigenStratum K A E0 = ⊥ ↔
      finrank ℝ (LinearMap.range (normalRestrict K A E0)) = finrank ℝ E0 := by
  rw [eigenStratum_eq_bot_iff_injective, ← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  constructor
  · intro h0
    have h := finrank_range_normalRestrict_add_finrank_ker K A E0
    omega
  · intro h
    have h := finrank_range_normalRestrict_add_finrank_ker K A E0
    omega

/-- **Paper Proposition 5 (iii), intermediate case.**  If `0 < rank(A₂₁|_{E⁰}) < dim E⁰` then both
strata are nonempty: a nonzero eigen direction and a non-eigen direction exist. -/
theorem exists_eigen_and_nonEigen_of_rank_between (K : Submodule ℝ E) (A : E →ₗ[ℝ] E)
    (E0 : Submodule ℝ E)
    (h0 : 0 < finrank ℝ (LinearMap.range (normalRestrict K A E0)))
    (h1 : finrank ℝ (LinearMap.range (normalRestrict K A E0)) < finrank ℝ E0) :
    (∃ v, v ∈ eigenStratum K A E0 ∧ v ≠ 0) ∧ (∃ v, v ∈ nonEigenStratum K A E0) := by
  have hbot : eigenStratum K A E0 ≠ ⊥ := by
    intro h
    have := (eigenStratum_eq_bot_iff_finrank_range K A E0).mp h
    omega
  have htop : eigenStratum K A E0 ≠ E0 := by
    intro h
    have hz : normalRestrict K A E0 = 0 :=
      (normalRestrict_eq_zero_iff_eigenStratum_eq_top K A E0).mpr h
    have : finrank ℝ (LinearMap.range (normalRestrict K A E0)) = 0 := by
      rw [hz]; simp
    omega
  refine ⟨Submodule.ne_bot_iff _ |>.mp hbot, ?_⟩
  by_contra hc
  apply htop
  refine le_antisymm inf_le_left ?_
  intro v hv
  by_cases hzero : normalComp K A v = 0
  · exact ⟨hv, hzero⟩
  · exact False.elim (hc ⟨v, ⟨hv, hzero⟩⟩)

end splitting

end Q1Paper
