/-
Q1Paper/PaperI/Claim4Converse.lean

The **converse** of Claim 4 (`lem:sandwich`) of Paper I.

`PaperI/Claims38.lean` proves the forward implications: for `L = [L₀; R]`,
`row(L₀ M) ⊆ row(L M) ⊆ row M` and `dim row(L M) ≤ dim row(L₀ M) + r`.
This file proves the converse: every subspace `W` with
`row(L₀ M) ⊆ W ⊆ row M` and `dim W ≤ dim row(L₀ M) + r` is `row([L₀;R] M)` for
some `R` with exactly `r` rows.

Route (no `sorry`, no new axioms):

* take a complement `V` of `W₀ = row(L₀ M)` in the ambient space and set
  `U = W ⊓ V`; then `W₀ ⊔ U = W` and `W₀ ⊓ U = ⊥` (elementwise argument, no
  modularity lemma needed);
* `Submodule.finrank_sup_add_finrank_inf_eq` gives
  `dim W = dim W₀ + dim U`, so `dim U ≤ r` by the hypothesis;
* take a basis `b` of `U`; every `b i` lies in `W ⊆ row M`, hence
  `b i = u i * M` (`Q1Subspace.mem_rowSpan_iff_exists_vecMul`); the rows `u i`
  are stacked into `R` and padded with zero rows to exactly `r` rows
  (`Q1Paper.exists_rows_mul_eq` of `Claims38`);
* `row([L₀;R] M) = row(L₀ M) ⊔ row(R M) = W₀ ⊔ U = W`
  (`Matrix.fromRows_mul`, `Q1Subspace.rowSpace_fromRows`).

Reuses: `Q1Subspace.rowSpace`, `Q1Subspace.rowSpace_fromRows`,
`Q1Subspace.mem_rowSpan_iff_exists_vecMul` (`Q1RowSpace.lean`, `Q1Subspace.lean`),
`Q1Paper.exists_rows_mul_eq` (`PaperI/Claims38.lean`), `Submodule.exists_isCompl`,
`Submodule.finrank_sup_add_finrank_inf_eq`, `Module.finBasis`, `Basis.sum_repr`.
-/
import Q1Paper.PaperI.Claims38

set_option linter.unusedSectionVars false

open Module LinearMap
open Matrix

namespace Q1Paper

variable {K : Type*} [Field K]

/-- **Claim 4, converse (`lem:sandwich`, reverse direction).**  Let
`W₀ = row(L₀ M)` and `𝒯 = row M`.  Every subspace `W` with `W₀ ⊆ W ⊆ 𝒯` and
`dim W ≤ dim W₀ + r` is the row space of `[L₀; R] * M` for some matrix `R` with
exactly `r` rows.

This is the missing converse of `Q1Paper.claim4_sandwich`: that theorem gives
`row(L₀ M) ⊆ row([L₀;R] M) ⊆ row M` and
`dim row([L₀;R] M) ≤ dim row(L₀ M) + r` for every `R`. -/
theorem claim4_converse {r0 r n m : ℕ} (L0 : Matrix (Fin r0) (Fin n) K)
    (M : Matrix (Fin n) (Fin m) K) (W : Submodule K (Fin m → K))
    (hW0 : Q1Subspace.rowSpace (L0 * M) ≤ W)
    (hWT : W ≤ Q1Subspace.rowSpace M)
    (hdim : Module.finrank K W ≤ Module.finrank K (Q1Subspace.rowSpace (L0 * M)) + r) :
    ∃ R : Matrix (Fin r) (Fin n) K,
      Q1Subspace.rowSpace (Matrix.fromRows L0 R * M) = W := by
  classical
  -- A complement `V` of `W₀ = row(L₀ M)` in the ambient space `K^m`.
  obtain ⟨V, hV⟩ := Submodule.exists_isCompl (Q1Subspace.rowSpace (L0 * M))
  -- `U = W ⊓ V` is a complement of `W₀` inside `W`.
  have hdisj : Q1Subspace.rowSpace (L0 * M) ⊓ (W ⊓ V) = ⊥ := by
    refine le_antisymm ?_ bot_le
    refine le_trans (inf_le_inf_left _ inf_le_right) ?_
    exact le_of_eq (disjoint_iff.mp hV.disjoint)
  have hsup : Q1Subspace.rowSpace (L0 * M) ⊔ (W ⊓ V) = W := by
    refine le_antisymm (sup_le hW0 inf_le_left) ?_
    intro x hx
    -- `W ⊆ W₀ ⊔ V` because `W₀ ⊔ V = ⊤`.
    have hx' : x ∈ Q1Subspace.rowSpace (L0 * M) ⊔ V := by
      rw [codisjoint_iff.mp hV.codisjoint]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx'
    have hbW : b ∈ W := by
      have h : b = (a + b) - a := by abel
      rw [h]
      exact Submodule.sub_mem W hx (hW0 ha)
    exact Submodule.add_mem_sup ha (Submodule.mem_inf.mpr ⟨hbW, hb⟩)
  -- Dimension count: `dim W = dim W₀ + dim U`, hence `dim U ≤ r`.
  have hfin : Module.finrank K W
      = Module.finrank K (Q1Subspace.rowSpace (L0 * M)) + Module.finrank K ↥(W ⊓ V) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Q1Subspace.rowSpace (L0 * M)) (W ⊓ V)
    rw [hsup, hdisj] at h
    simpa using h
  have hdr : Module.finrank K ↥(W ⊓ V) ≤ r := by omega
  -- A basis of `U` gives at most `r` extra rows.
  let d := Module.finrank K ↥(W ⊓ V)
  have hdr' : d ≤ r := hdr
  let b : Basis (Fin d) K ↥(W ⊓ V) := Module.finBasis K ↥(W ⊓ V)
  -- The `r` row vectors: the first `d` are the basis vectors of `U`, the rest `0`.
  let w : Fin r → (Fin m → K) := fun i =>
    if h : (i : ℕ) < d then ((b ⟨i, h⟩) : Fin m → K) else 0
  have hw : ∀ i : Fin r, w i ∈ Q1Subspace.rowSpace M := by
    intro i
    by_cases h : (i : ℕ) < d
    · have hmem : ((b ⟨i, h⟩) : Fin m → K) ∈ W :=
        (Submodule.mem_inf.mp (b ⟨i, h⟩).2).1
      simpa [w, h] using hWT hmem
    · simp [w, h]
  -- Realise them by free rows and stack those into `R : Matrix (Fin r) (Fin n) K`.
  obtain ⟨R, hR⟩ := exists_rows_mul_eq M w hw
  refine ⟨R, ?_⟩
  -- The compressed rows of `R` span exactly `U = W ⊓ V`.
  have hRU : Q1Subspace.rowSpace (R * M) = W ⊓ V := by
    refine le_antisymm ?_ ?_
    · -- each row of `R * M` is a basis vector of `U`, or zero
      rw [Q1Subspace.rowSpace, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      change (R * M) i ∈ (W ⊓ V)
      rw [hR i]
      by_cases h : (i : ℕ) < d
      · simpa [w, h] using (b ⟨i, h⟩).2
      · simp [w, h]
    · -- every basis vector of `U` is a row of `R * M`
      have himg : ⇑(W ⊓ V).subtype '' (Set.range ⇑b)
          = Set.range (fun i : Fin d => ((b i) : Fin m → K)) := by
        ext x
        constructor
        · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨_, ⟨i, rfl⟩, rfl⟩
      have hspan : Submodule.span K
          (Set.range (fun i : Fin d => ((b i) : Fin m → K))) = W ⊓ V := by
        have h := congrArg (Submodule.map (W ⊓ V).subtype) b.span_eq
        rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, himg] at h
        exact h
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      change ((b i) : Fin m → K) ∈ Q1Subspace.rowSpace (R * M)
      have hi : (i : ℕ) < r := lt_of_lt_of_le i.isLt hdr'
      have hrow : (R * M) ⟨i, hi⟩ = ((b i) : Fin m → K) := by
        rw [hR]
        simp [w, i.isLt]
      rw [← hrow]
      exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  -- Assemble: `row([L₀;R] M) = row(L₀ M) ⊔ row(R M) = W₀ ⊔ U = W`.
  rw [Matrix.fromRows_mul, Q1Subspace.rowSpace_fromRows, hRU, hsup]

/-- The `r = 0` case of `claim4_converse`: the only subspace between `W₀` and
`𝒯` of dimension `≤ dim W₀` is `W₀` itself, and it is `row([L₀; 0] M)`. -/
theorem claim4_converse_zero {r0 n m : ℕ} (L0 : Matrix (Fin r0) (Fin n) K)
    (M : Matrix (Fin n) (Fin m) K) (W : Submodule K (Fin m → K))
    (hW0 : Q1Subspace.rowSpace (L0 * M) ≤ W)
    (hWT : W ≤ Q1Subspace.rowSpace M)
    (hdim : Module.finrank K W ≤ Module.finrank K (Q1Subspace.rowSpace (L0 * M))) :
    ∃ R : Matrix (Fin 0) (Fin n) K,
      Q1Subspace.rowSpace (Matrix.fromRows L0 R * M) = W :=
  claim4_converse L0 M W hW0 hWT (by simpa using hdim)


end Q1Paper
