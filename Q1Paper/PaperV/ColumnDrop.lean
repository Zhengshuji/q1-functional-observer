import Mathlib

/-!
Q1Paper/PaperV/ColumnDrop.lean

§IV, Proposition 14 — the linear-algebra kernel of **column drop**.

Paper statement (verbatim, with the support condition):

  *If for some `λ₀` and some set `J` of columns with `|J| > k - d'` and
  `J ∩ supp(T) = ∅` the identity `(H Z'')_{:,j} = λ₀ H_{:,j}` holds for `j ∈ J`, then `U` is bad.*

The rank step is this file: a matrix with `|J|` vanishing columns has rank at most
`k - |J|`.  The rest of the proposition is the evaluation at `λ₀` (the columns of `P(λ₀)`
vanish because `G'` vanishes on the support of `T`), which is bookkeeping rather than
linear algebra.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

open Matrix

namespace Q1Paper.PaperV

/-- **Proposition 14 (rank step).** If every column indexed by `J` vanishes, then
`rank M ≤ card n - card J`; hence a matrix with `|J| > k - d'` vanishing columns has rank
below `d'`. -/
theorem rank_le_card_compl_of_cols_zero {K : Type*} [Field K]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n K) (J : Finset n) (h : ∀ j ∈ J, ∀ i, M i j = 0) :
    M.rank ≤ Fintype.card n - J.card := by
  classical
  set T : Finset (n → K) := Jᶜ.image (fun j => (Pi.single j (1 : K) : n → K)) with hT
  have hsingle : ∀ (j : n) (a : K),
      (Pi.single j a : n → K) = a • (Pi.single j (1 : K) : n → K) := by
    intro j a
    funext k
    by_cases hk : k = j
    · rw [hk]; simp
    · simp [Pi.single_eq_of_ne hk]
  have hsum : ∀ i, (∑ j ∈ Jᶜ, (Pi.single j (M i j) : n → K)) = M.row i := by
    intro i
    rw [Finset.sum_subset (Finset.subset_univ Jᶜ) (fun x _ hx => by
      simp only [Finset.mem_compl, not_not] at hx
      simp [h x hx i])]
    exact Finset.univ_sum_single (M.row i)
  have hrow : ∀ i, M.row i ∈ Submodule.span K (T : Set (n → K)) := by
    intro i
    rw [← hsum i]
    refine Submodule.sum_mem _ (fun j hj => ?_)
    rw [hsingle j (M i j)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
  have hle : Submodule.span K (Set.range M.row) ≤ Submodule.span K (T : Set (n → K)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hrow i
  calc M.rank = Module.finrank K ↥(Submodule.span K (Set.range M.row)) :=
        Matrix.rank_eq_finrank_span_row M
    _ ≤ Module.finrank K ↥(Submodule.span K (T : Set (n → K))) := Submodule.finrank_mono hle
    _ ≤ T.card := finrank_span_finset_le_card T
    _ ≤ Jᶜ.card := by rw [hT]; exact Finset.card_image_le
    _ = Fintype.card n - J.card := Finset.card_compl J

/-- **Proposition 14 (conclusion step).** If the columns in `J` vanish and `k - |J| < d'`, then
the rank at that `λ` is below `d'`, so `(5b)` fails there for every point of the fibre. -/
theorem rank_lt_of_cols_zero {K : Type*} [Field K] {q k : ℕ} (P : Matrix (Fin q) (Fin k) K)
    (J : Finset (Fin k)) (h : ∀ j ∈ J, ∀ i, P i j = 0) {d : ℕ}
    (hd : Fintype.card (Fin k) - J.card < d) : P.rank < d :=
  lt_of_le_of_lt (rank_le_card_compl_of_cols_zero P J h) hd

end Q1Paper.PaperV
