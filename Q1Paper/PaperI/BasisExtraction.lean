/-
Q1Paper/PaperI/BasisExtraction.lean

Two finite-dimensional linear-algebra tools for the rank/minors bridge:

* `exists_injective_linearIndependent`: from a finite family `v : ι → V` whose
  span has dimension `ω`, extract an injective `κ : Fin ω → ι` such that the
  subfamily `v ∘ κ` is linearly independent.  The proof uses a *maximal*
  linearly independent subfamily (Mathlib's `exists_maximal_linearIndepOn`);
  maximality forces it to span the same space, so its cardinality is `ω`.

* `exists_invertible_cols`: a full-row-rank `ω × n` matrix has `ω` columns
  forming an invertible square submatrix.  The columns span a space of
  dimension `rank = ω`; the first lemma extracts `ω` independent ones, and
  `Matrix.linearIndependent_col_iff` + `Matrix.nonsingular_iff_det_ne_zero`
  turn column independence into a nonzero determinant.

Neither proof uses Cauchy–Binet.
-/

import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.Rank

namespace Q1Paper.PaperI

open Submodule

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- **Basis extraction.**  A finite family spanning a space of dimension `ω`
contains `ω` linearly independent members. -/
theorem exists_injective_linearIndependent {ι : Type*} [Fintype ι] {ω : ℕ}
    (v : ι → V) (hω : Module.finrank K (Submodule.span K (Set.range v)) = ω) :
    ∃ κ : Fin ω → ι, Function.Injective κ ∧ LinearIndependent K (v ∘ κ) := by
  classical
  obtain ⟨s, hsind, hsmax⟩ := exists_maximal_linearIndepOn K v
  have himg : (v '' s) = Set.range (fun x : s => v x) := by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
  have hspan : Submodule.span K (Set.range (fun x : s => v x)) =
      Submodule.span K (Set.range v) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      exact Submodule.subset_span ⟨x.1, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases hi : i ∈ s
      · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
      · obtain ⟨a, ha, ha'⟩ := hsmax i hi
        rw [himg] at ha'
        have hv : v i = a⁻¹ • (a • v i) := by
          rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
        rw [hv]
        exact Submodule.smul_mem _ _ ha'
  have hcard : Fintype.card s = ω := by
    rw [← hω, ← hspan]
    exact (finrank_span_eq_card hsind.linearIndependent).symm
  let e : s ≃ Fin ω := Fintype.equivFinOfCardEq hcard
  refine ⟨fun j => (e.symm j).1, ?_, ?_⟩
  · intro j j' h
    have h' : e.symm j = e.symm j' := Subtype.ext h
    exact e.symm.injective h'
  · have h := hsind.linearIndependent.comp (fun j : Fin ω => e.symm j) e.symm.injective
    have hfun : (v ∘ (fun j : Fin ω => (e.symm j : s).1)) =
        ((fun x : s => v x) ∘ (fun j => e.symm j)) := rfl
    rw [hfun]
    exact h

/-- **Full row rank gives an invertible column submatrix.** -/
theorem exists_invertible_cols {ω n : ℕ} (W : Matrix (Fin ω) (Fin n) K)
    (h : W.rank = ω) :
    ∃ κ : Fin ω → Fin n, Function.Injective κ ∧ (W.submatrix id κ).det ≠ 0 := by
  have hω : Module.finrank K (Submodule.span K (Set.range W.col)) = ω := by
    rw [← Matrix.rank_eq_finrank_span_cols]
    exact h
  obtain ⟨κ, hκ, hLI⟩ := exists_injective_linearIndependent (v := W.col) hω
  refine ⟨κ, hκ, ?_⟩
  have hcol : (W.submatrix id κ).col = W.col ∘ κ := by
    funext j i
    rfl
  have hLI' : LinearIndependent K (W.submatrix id κ).col := by
    rw [hcol]
    exact hLI
  exact Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.linearIndependent_col_iff.mp hLI')

end Q1Paper.PaperI
