import Q1Paper.PaperI.RankFactorization

/-!
Q1Paper/PaperI/FinReindex.lean

Two independent "last mile" tools for the `r = 0` case of the `DEC` statements.

## §1  The reindexing `Fin a ⊕ Fin 0 ≃ Fin a`

`Matrix.fromRows` produces a matrix whose row index is `Fin r0 ⊕ Fin r`.  At `r = 0`
the row index is `Fin r0 ⊕ Fin 0`, and specialising a `DEC` statement to `r = 0`
requires identifying that row type with `Fin r0`.

* `finSumFinZero a : Fin a ⊕ Fin 0 ≃ Fin a`, obtained from Mathlib's
  `finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)` composed with
  `finCongr (Nat.add_zero a)`;
* `finSumFinZero_apply_inl a i : finSumFinZero a (Sum.inl i) = i`;
* `finSumFinZero_symm_apply a i : (finSumFinZero a).symm i = Sum.inl i`
  (the inverse is the embedding `Sum.inl`);
* `rank_reindex_finSumFinZero`: reindexing the rows of an
  `(Fin a ⊕ Fin 0) × Fin m` matrix along `(finSumFinZero a).symm` does not
  change the rank.

Direction of the reindexing: `M.submatrix r id` needs `r : Fin a → Fin a ⊕ Fin 0`,
so a matrix whose row type is the *sum* is reindexed along `(finSumFinZero a).symm`
(which by `finSumFinZero_symm_apply` is `Sum.inl`).  The literal
`M.submatrix (finSumFinZero a) id` is ill-typed for such an `M` (its row map would
have to go `Fin a ⊕ Fin 0 → Fin a`); the companion
`rank_reindex_finSumFinZero_fin` records the analogous statement for a matrix that
already has `Fin a` rows, where the literal form does typecheck.

## §2  The rank-deficient compressed block

For a compressed block `H : Matrix (Fin q) (Fin k) ℚ` of rank `ω`, the pivot
columns of a nonvanishing `ω × ω` minor (a left factor `H'` of rank `ω`) together
with the coefficient matrix `S` of the remaining columns give `H' * S = H`, with
`S.rank = ω`.  The construction is
`Q1Paper.PaperI.RankFactorization.exists_rank_factorization_of_rank`, which
already returns such `X, B` together with one-sided inverses
(`XL * X = 1`, `B * BR = 1`); the two rank identities are read off from those
inverses via `Matrix.rank_mul_le_left` / `Matrix.rank_mul_le_right` and the
bounds `Matrix.rank_le_width` / `Matrix.rank_le_height`.
-/


open Matrix

namespace Q1Paper

/-! ## §1  `Fin a ⊕ Fin 0 ≃ Fin a` -/

/-- The reindexing `Fin a ⊕ Fin 0 ≃ Fin a` used to specialise `Matrix.fromRows`
statements to the case `r = 0`. -/
def finSumFinZero (a : ℕ) : Fin a ⊕ Fin 0 ≃ Fin a :=
  finSumFinEquiv.trans (finCongr (Nat.add_zero a))

/-- On the left summand, `finSumFinZero` is the identity. -/
theorem finSumFinZero_apply_inl (a : ℕ) (i : Fin a) :
    finSumFinZero a (Sum.inl i) = i := by
  rw [finSumFinZero, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply]
  exact Fin.ext rfl

/-- The inverse of `finSumFinZero` is the embedding `Sum.inl` (possible because
`Fin 0` is empty). -/
theorem finSumFinZero_symm_apply (a : ℕ) (i : Fin a) :
    (finSumFinZero a).symm i = Sum.inl i := by
  rw [Equiv.symm_apply_eq]
  exact (finSumFinZero_apply_inl a i).symm

/-- Reindexing the rows of a matrix with row type `Fin a ⊕ Fin 0` to `Fin a`
preserves the rank. -/
theorem rank_reindex_finSumFinZero {a m : ℕ}
    (M : Matrix (Fin a ⊕ Fin 0) (Fin m) ℚ) :
    (M.submatrix (finSumFinZero a).symm id).rank = M.rank := by
  apply le_antisymm
  · exact Matrix.rank_submatrix_le M (finSumFinZero a).symm id
  · have h := Matrix.rank_submatrix_le (M.submatrix (finSumFinZero a).symm id)
      ((finSumFinZero a).symm.symm) id
    have heq : (M.submatrix (finSumFinZero a).symm id).submatrix
        ((finSumFinZero a).symm.symm) id = M := by
      ext i j
      simp
    rwa [heq] at h

/-- The companion form in which the reindexing is literally `finSumFinZero a`,
i.e. for a matrix that already has `Fin a` rows and is viewed as an
`(Fin a ⊕ Fin 0) × Fin m` matrix. -/
theorem rank_reindex_finSumFinZero_fin {a m : ℕ}
    (M : Matrix (Fin a) (Fin m) ℚ) :
    (M.submatrix (finSumFinZero a) id).rank = M.rank := by
  apply le_antisymm
  · exact Matrix.rank_submatrix_le M (finSumFinZero a) id
  · have h := Matrix.rank_submatrix_le (M.submatrix (finSumFinZero a) id)
      ((finSumFinZero a).symm) id
    have heq : (M.submatrix (finSumFinZero a) id).submatrix
        (finSumFinZero a).symm id = M := by
      ext i j
      simp
    rwa [heq] at h

/-! ## §2  The rank-deficient compressed block -/

/-- **Pivot columns plus coefficients.**  A `q × k` matrix `H` of rank `ω` factors
as `H' * S`, where `H'` is the `q × ω` block of pivot columns of a nonvanishing
`ω × ω` minor (so `H'.rank = ω`, i.e. `H'` has full column rank) and `S` is the
`ω × k` coefficient matrix of the columns of `H` in the pivot columns.

Since `H' * S = H`, every row of `H` is a linear combination of the rows of `S`;
together with `rank S = ω = rank H` this makes the row space of `S` the row space
of `H`. -/
theorem exists_fullColumn_block {q k : ℕ} (H : Matrix (Fin q) (Fin k) ℚ)
    (ω : ℕ) (hω : H.rank = ω) :
    ∃ (H' : Matrix (Fin q) (Fin ω) ℚ) (S : Matrix (Fin ω) (Fin k) ℚ),
      H'.rank = ω ∧ H' * S = H ∧ S.rank = ω := by
  obtain ⟨X, S, XL, BR, hXS, hXL, hBR⟩ :=
    Q1Paper.PaperI.RankFactorization.exists_rank_factorization_of_rank (K := ℚ) H hω
  have hone : (1 : Matrix (Fin ω) (Fin ω) ℚ).rank = ω := by
    rw [Matrix.rank_one]
    simp
  refine ⟨X, S, ?_, hXS, ?_⟩
  · -- `X.rank = ω`: `XL * X = 1` gives `ω ≤ X.rank`, and `X` has `ω` columns.
    apply le_antisymm
    · exact Matrix.rank_le_width X
    · calc ω = (1 : Matrix (Fin ω) (Fin ω) ℚ).rank := hone.symm
        _ = (XL * X).rank := by rw [hXL]
        _ ≤ X.rank := Matrix.rank_mul_le_right XL X
  · -- `S.rank = ω`: `S * BR = 1` gives `ω ≤ S.rank`, and `S` has `ω` rows.
    apply le_antisymm
    · exact Matrix.rank_le_height S
    · calc ω = (1 : Matrix (Fin ω) (Fin ω) ℚ).rank := hone.symm
        _ = (S * BR).rank := by rw [hBR]
        _ ≤ S.rank := Matrix.rank_mul_le_left S BR

end Q1Paper
