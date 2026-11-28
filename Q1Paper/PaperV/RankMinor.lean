import Mathlib

/-!
Q1Paper/PaperV/RankMinor.lean

§III, the rank-minor bridge.

Paper usage: the criterion says that a pencil has rank `d'` at `λ` exactly when some `d'`-minor is
nonzero at `λ`. This module proves the algebraic direction needed, over any field: rank at least `d`
forces a nonzero `d × d` minor. Combined with `FamilyGcd.exists_eval_ne_zero_of_isUnit_gcd` it gives
"gcd one ⟹ full rank at every `λ`".

The proof extracts a basis from a spanning set twice (`Submodule.exists_fun_fin_finrank_span_eq`):
once from the rows, then from the columns of the resulting full-row-rank matrix. This version of
Mathlib has no direct `exists_submatrix_det_ne_zero` lemma.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

set_option maxHeartbeats 800000

namespace Q1Paper.PaperV

/-- In a matrix over a field, rank at least `d` means some `d × d` submatrix has nonzero
determinant. -/
theorem exists_submatrix_det_ne_zero_of_le_rank {K : Type*} [Field K] {q k d : ℕ}
    (M : Matrix (Fin q) (Fin k) K) (hd : d ≤ M.rank) :
    ∃ e : Fin d → Fin q, ∃ f : Fin d → Fin k, (M.submatrix e f).det ≠ 0 := by
  classical
  have hfr : Module.finrank K (Submodule.span K (Set.range M.row)) = M.rank := by
    rw [← Matrix.rank_eq_finrank_span_row (A := M)]
  have hdr : d ≤ Module.finrank K (Submodule.span K (Set.range M.row)) := by
    rw [hfr]
    exact hd
  obtain ⟨g, hgmem, -, hgind⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (K := K) (s := Set.range M.row)
  have hg : ∀ i : Fin d, ∃ j : Fin q, M.row j = g (Fin.castLE hdr i) :=
    fun i => Set.mem_range.mp (hgmem (Fin.castLE hdr i))
  choose e he using hg
  have hfun : (fun i : Fin d => M.row (e i)) = fun i : Fin d => g (Fin.castLE hdr i) := by
    funext i
    exact he i
  have hrowind : LinearIndependent K (fun i : Fin d => M.row (e i)) := by
    have h2 : LinearIndependent K (fun i : Fin d => g (Fin.castLE hdr i)) :=
      hgind.comp (Fin.castLE hdr) (Fin.castLE_injective hdr)
    rw [hfun]
    exact h2
  have hrow_eq : (M.submatrix e id).row = fun i : Fin d => M.row (e i) := rfl
  have hind : LinearIndependent K (M.submatrix e id).row := by
    rw [hrow_eq]
    exact hrowind
  have hNrank : (M.submatrix e id).rank = d := by
    have h := LinearIndependent.rank_matrix (M := M.submatrix e id) hind
    rw [h, Fintype.card_fin]
  have hfr2 : Module.finrank K (Submodule.span K (Set.range (M.submatrix e id).col)) = d := by
    rw [← Matrix.rank_eq_finrank_span_cols (A := M.submatrix e id), hNrank]
  obtain ⟨h, hhmem, -, hhind⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (K := K) (s := Set.range (M.submatrix e id).col)
  have hmem : ∀ i : Fin d, ∃ j : Fin k,
      (M.submatrix e id).col j = h (Fin.cast hfr2.symm i) :=
    fun i => Set.mem_range.mp (hhmem (Fin.cast hfr2.symm i))
  choose f hf using hmem
  have hfun2 : (fun i : Fin d => (M.submatrix e id).col (f i))
      = fun i : Fin d => h (Fin.cast hfr2.symm i) := by
    funext i
    exact hf i
  have hcolind : LinearIndependent K (fun i : Fin d => (M.submatrix e id).col (f i)) := by
    have h2 : LinearIndependent K (fun i : Fin d => h (Fin.cast hfr2.symm i)) :=
      hhind.comp (Fin.cast hfr2.symm) (Fin.cast_injective hfr2.symm)
    rw [hfun2]
    exact h2
  refine ⟨e, f, ?_⟩
  have hcol : (M.submatrix e f).col = fun i : Fin d => (M.submatrix e id).col (f i) := rfl
  have hind' : LinearIndependent K (M.submatrix e f).col := by
    rw [hcol]
    exact hcolind
  exact Matrix.nonsingular_iff_det_ne_zero.mp
    (Matrix.Nonsingular.of_linearIndependent_col hind')

/-- The converse: a nonzero `d × d` minor forces rank at least `d`. Together with
`exists_submatrix_det_ne_zero_of_le_rank` this gives "rank ≥ d ↔ some `d`-minor is nonzero",
which is what lets the gcd criterion of Theorem 4 be read pointwise. -/
theorem le_rank_of_det_submatrix_ne_zero {K : Type*} [Field K] {q k d : ℕ}
    (M : Matrix (Fin q) (Fin k) K) (e : Fin d → Fin q) (f : Fin d → Fin k)
    (h : (M.submatrix e f).det ≠ 0) : d ≤ M.rank := by
  have hunit : IsUnit (M.submatrix e f) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr h
  have hrank : (M.submatrix e f).rank = d := by
    simpa using Matrix.rank_of_isUnit (M.submatrix e f) hunit
  have hle : (M.submatrix e f).rank ≤ M.rank := Matrix.rank_submatrix_le M e f
  rw [hrank] at hle
  exact hle


end Q1Paper.PaperV
