
import Q1Paper.PaperI.Claim8Wire
import Q1Paper.G5GramRank

/-!
Q1Paper/PaperI/Claim8Literal.lean

**Claim 8 in the paper's literal form: the disjunction for `Γ' = M Mᵀ + c cᵀ`.**

`PaperI/Claim8Ej.lean` defines `elemSymm M j` (sum of the principal `j × j` minors of
`Γ = M * Mᵀ`) for `M : Matrix (Fin m) (Fin n) ℝ`, i.e. with the column index fixed to `Fin n`,
and proves

  `elemSymm_pos_iff_rank_ge      :  0 < elemSymm M j ↔ j ≤ M.rank`,
  `elemSymm_eq_zero_iff_rank_lt  :  elemSymm M j = 0 ↔ M.rank < j`.

`PaperI/Claim8Wire.lean` proves the disjunction for a single Gram matrix and records the gap:
the paper's second Gram matrix is `Γ' = M Mᵀ + c cᵀ = [M  c] * [M  c]ᵀ`, whose column index type
is `Fin n ⊕ Fin 1`, so `elemSymm` (fixed to `Fin n`) cannot be applied to it.

This file closes the gap, in three steps.

## 1.  `elemSymmGen`: `elemSymm` for an arbitrary finite column type

`elemSymmGen M j` is defined *literally* as the sum of the principal `j × j` minors of
`Γ = M * Mᵀ` over the `j`-element sets of rows — the same object as `elemSymm`, written without
any reference to an ordering of the column index type:

  `elemSymmGen M j = ∑_{|S| = j} det ((M * Mᵀ)_{S,S})`.

It agrees with `elemSymm` after reindexing the columns by `Fintype.equivFin ι`
(`elemSymmGen_eq_elemSymm`), which is the bridge that lets the whole existing proof in
`Claim8Ej.lean` be reused.  The main results transfer verbatim:

  `elemSymmGen_pos_iff_rank_ge      :  0 < elemSymmGen M j ↔ j ≤ M.rank`,
  `elemSymmGen_eq_zero_iff_rank_lt  :  elemSymmGen M j = 0 ↔ M.rank < j`.

(The Cauchy–Binet lemma `Matrix.det_mul_transpose_eq_sum_det_submatrix` of
`PaperI/CauchyBinet.lean` is already general in the column index `ι`, but it requires a
`LinearOrder ι` for the enumeration `orderEmbOfFin`; the reindexing route avoids having to
transport the order and reuses `Claim8Ej.lean` unchanged.)

## 2.  The second Gram matrix

Naming trap in the pinned Mathlib: `Matrix.fromRows` **stacks rows**
(`Matrix m₁ n R → Matrix m₂ n R → Matrix (m₁ ⊕ m₂) n R`), so the column append `[M  c]`
described in the task is `Matrix.fromCols`, and `Q1Paper.augment` (`G5GramRank.lean`) is
exactly `M.fromCols (colMatrix c) : Matrix (Fin m) (Fin n ⊕ Fin 1) ℝ`.  We therefore work with
`withCol M c := Matrix.fromCols M (colMatrix c)`, which is definitionally `Q1Paper.augment M c`,
and prove

  `withCol_mul_transpose : withCol M c * (withCol M c)ᵀ = M * Mᵀ + Matrix.vecMulVec c c`

(the paper's `Γ'`; this is `Q1Paper.augment_mul_transpose`), together with
`withCol_rank_eq_augment : (withCol M c).rank = (Q1Paper.augment M c).rank` and
`rank_le_rank_withCol : M.rank ≤ (withCol M c).rank`.

## 3.  The literal disjunction (`claim8_disjunction`)

  `(∃ b, M.mulVec b = c) ↔ ∃ t, 0 < elemSymmGen M t ∧ elemSymmGen M (t+1) = 0
                                        ∧ elemSymmGen (withCol M c) (t+1) = 0`.

Route.  `→`: take `t = M.rank`; solvability gives `rank (withCol M c) = rank M` via
`Q1Paper.exists_mulVec_eq_iff_rank_gram` (Gram ranks agree iff solvable) and the two Gram
identities, hence `elemSymmGen (withCol M c) (rank M + 1) = 0`.
`←`: the first two conjuncts force `rank M = t` (`elemSymmGen_pos_iff_rank_ge`,
`elemSymmGen_eq_zero_iff_rank_lt`), the third gives `rank (withCol M c) ≤ t`, and
`rank M ≤ rank (withCol M c)` is automatic (the block `M` sits inside `[M  c]`), so the ranks
agree and `Q1Paper.exists_mulVec_eq_iff_rank_gram` yields the solution.

No `sorry`, no `admit`, no new axioms.  Check with
  lake env lean Q1Paper/PaperI/Claim8Literal.lean
-/


open Matrix

namespace Q1Paper.PaperI.Claim8Literal

open Q1Paper.PaperI.Claim8Ej

/-! ## 1.  `elemSymm` for an arbitrary finite column type -/

/-- **The `j`-th elementary symmetric function of `Γ = M * Mᵀ` for an arbitrary finite column
type `ι`**: the sum of the principal `j × j` minors of `M * Mᵀ`.  This is `elemSymm` of
`PaperI/Claim8Ej.lean` written without fixing the column index to `Fin n` and without choosing
an enumeration of the columns. -/
noncomputable def elemSymmGen {m : ℕ} {ι : Type*} [Fintype ι]
    (M : Matrix (Fin m) ι ℝ) (j : ℕ) : ℝ :=
  ∑ S : Set.powersetCard (Fin m) j,
    ((M * Mᵀ).submatrix (Q1Paper.PaperI.rowEmb S) (Q1Paper.PaperI.rowEmb S)).det

/-- Reindexing the columns of `M` by `Fintype.equivFin ι` leaves the Gram matrix `M * Mᵀ`
unchanged (the column index only labels the sum). -/
theorem gram_submatrix_equivFin {m : ℕ} {ι : Type*} [Fintype ι]
    (M : Matrix (Fin m) ι ℝ) :
    (M.submatrix id (Fintype.equivFin ι).symm) * (M.submatrix id (Fintype.equivFin ι).symm)ᵀ
      = M * Mᵀ := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, id_eq]
  exact Fintype.sum_equiv (Fintype.equivFin ι).symm _ _ (fun x => rfl)

/-- Reindexing the columns by an equivalence does not change the rank. -/
theorem rank_submatrix_equivFin {m : ℕ} {ι : Type*} [Fintype ι]
    (M : Matrix (Fin m) ι ℝ) :
    (M.submatrix id (Fintype.equivFin ι).symm).rank = M.rank := by
  simpa using Matrix.rank_submatrix M (Equiv.refl (Fin m)) ((Fintype.equivFin ι).symm)

/-- **`elemSymmGen` is `elemSymm` after reindexing the columns to `Fin (card ι)`.**  This is the
bridge that reuses the whole proof of `PaperI/Claim8Ej.lean`. -/
theorem elemSymmGen_eq_elemSymm {m : ℕ} {ι : Type*} [Fintype ι]
    (M : Matrix (Fin m) ι ℝ) (j : ℕ) :
    elemSymmGen M j = elemSymm (M.submatrix id (Fintype.equivFin ι).symm) j := by
  rw [elemSymmGen, elemSymm]
  exact Finset.sum_congr rfl (fun S _ => by
    rw [Q1Paper.PaperI.Claim8Wire.gramBlock_eq_gram_submatrix
      (M.submatrix id (Fintype.equivFin ι).symm) S, gram_submatrix_equivFin])

/-- **The general-rank-positivity criterion.**  The `j`-th elementary symmetric function of the
Gram matrix `M * Mᵀ` is positive iff `j ≤ rank M`, for any finite column type. -/
theorem elemSymmGen_pos_iff_rank_ge {m : ℕ} {ι : Type*} [Fintype ι]
    (M : Matrix (Fin m) ι ℝ) (j : ℕ) : 0 < elemSymmGen M j ↔ j ≤ M.rank := by
  have h := elemSymm_pos_iff_rank_ge (M.submatrix id (Fintype.equivFin ι).symm) j
  rw [rank_submatrix_equivFin M] at h
  rw [elemSymmGen_eq_elemSymm]
  exact h

/-- **The general-rank-vanishing criterion.**  The `j`-th elementary symmetric function of the
Gram matrix `M * Mᵀ` vanishes iff `rank M < j`, for any finite column type. -/
theorem elemSymmGen_eq_zero_iff_rank_lt {m : ℕ} {ι : Type*} [Fintype ι]
    (M : Matrix (Fin m) ι ℝ) (j : ℕ) : elemSymmGen M j = 0 ↔ M.rank < j := by
  have h := elemSymm_eq_zero_iff_rank_lt (M.submatrix id (Fintype.equivFin ι).symm) j
  rw [rank_submatrix_equivFin M] at h
  rw [elemSymmGen_eq_elemSymm]
  exact h

/-! ## 2.  The paper's second Gram matrix `Γ' = M Mᵀ + c cᵀ` -/

/-- **The augmented matrix `[M  c]`** (the paper's `[M  c]`): `M` with the column `c` appended;
column index `Fin n ⊕ Fin 1`.  In the pinned Mathlib `Matrix.fromRows` stacks *rows*, so the
column append is `Matrix.fromCols`; this is definitionally `Q1Paper.augment`. -/
def withCol {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) :
    Matrix (Fin m) (Fin n ⊕ Fin 1) ℝ :=
  M.fromCols (Q1Paper.colMatrix c)

/-- `withCol M c` is `Q1Paper.augment M c`. -/
theorem withCol_eq_augment {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) :
    withCol M c = Q1Paper.augment M c := rfl

/-- The rank of `withCol M c` is the rank of `Q1Paper.augment M c`. -/
theorem withCol_rank_eq_augment {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) :
    (withCol M c).rank = (Q1Paper.augment M c).rank := rfl

/-- **`Γ' = M Mᵀ + c cᵀ` is the Gram matrix of `[M  c]`.**  This is the paper's second Gram
matrix of Claim 8. -/
theorem withCol_mul_transpose {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) :
    withCol M c * (withCol M c)ᵀ = M * Mᵀ + Matrix.vecMulVec c c :=
  Q1Paper.augment_mul_transpose M c

/-- The block of the `Fin n` columns of `[M  c]` is `M`. -/
theorem withCol_submatrix_inl {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) :
    (withCol M c).submatrix id Sum.inl = M := by
  ext i j
  simp [withCol, Matrix.fromCols_apply_inl]

/-- Adjoining a column cannot lower the rank: `rank M ≤ rank [M  c]`. -/
theorem rank_le_rank_withCol {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) :
    M.rank ≤ (withCol M c).rank := by
  have hmat : (withCol M c).submatrix id Sum.inl = M := withCol_submatrix_inl M c
  calc M.rank = ((withCol M c).submatrix id Sum.inl).rank := by rw [hmat]
    _ ≤ (withCol M c).rank := Matrix.rank_submatrix_le (withCol M c) id Sum.inl

/-! ## 3.  Claim 8, the paper's literal disjunction -/

/-- **Claim 8 in the paper's literal form.**  For `M : Matrix (Fin m) (Fin n) ℝ` and
`c : Fin m → ℝ`, the system `M b = c` is solvable iff the disjunction

  `∨_t [ e_t(Γ) > 0 ∧ e_{t+1}(Γ) = 0 ∧ e_{t+1}(Γ') = 0 ]`,

with `Γ = M * Mᵀ` and `Γ' = M Mᵀ + c cᵀ = [M  c] * [M  c]ᵀ`, holds; the witness is
`t = rank M`.  (`elemSymmGen` is the `j`-th elementary symmetric function of the Gram matrix,
i.e. the sum of its principal `j × j` minors.) -/
theorem claim8_disjunction {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) :
    (∃ b : Fin n → ℝ, M.mulVec b = c) ↔
      ∃ t : ℕ, 0 < elemSymmGen M t ∧ elemSymmGen M (t + 1) = 0 ∧
        elemSymmGen (withCol M c) (t + 1) = 0 := by
  constructor
  · -- `→`: the switch point of `e_·(Γ)` is `t = rank M`, and adjoining a solvable column
    -- does not raise the rank, so `e_{rank M + 1}(Γ')` vanishes as well.
    rintro ⟨b, hb⟩
    refine ⟨M.rank, ?_, ?_, ?_⟩
    · exact (elemSymmGen_pos_iff_rank_ge M M.rank).mpr le_rfl
    · exact (elemSymmGen_eq_zero_iff_rank_lt M (M.rank + 1)).mpr (Nat.lt_succ_self M.rank)
    · have hrank : (withCol M c).rank = M.rank := by
        -- solvable ⟹ the two Gram ranks agree ⟹ `rank [M c] = rank M`
        have hg := (Q1Paper.exists_mulVec_eq_iff_rank_gram M c).mp ⟨b, hb⟩
        rw [Matrix.rank_self_mul_transpose M, ← Q1Paper.augment_mul_transpose M c,
          Matrix.rank_self_mul_transpose (Q1Paper.augment M c)] at hg
        exact hg.symm
      exact (elemSymmGen_eq_zero_iff_rank_lt (withCol M c) (M.rank + 1)).mpr
        (by rw [hrank]; exact Nat.lt_succ_self M.rank)
  · -- `←`: the first two conjuncts pin `rank M = t`; the third bounds
    -- `rank [M c] ≤ t`; `rank M ≤ rank [M c]` is automatic, so the ranks agree.
    rintro ⟨t, hpos, hzero, hzero'⟩
    have ht : t ≤ M.rank := (elemSymmGen_pos_iff_rank_ge M t).mp hpos
    have hlt : M.rank < t + 1 := (elemSymmGen_eq_zero_iff_rank_lt M (t + 1)).mp hzero
    have hMt : M.rank = t := by omega
    have heq : (withCol M c).rank = M.rank := by
      have haut : (withCol M c).rank ≤ t := by
        have h := (elemSymmGen_eq_zero_iff_rank_lt (withCol M c) (t + 1)).mp hzero'
        omega
      exact le_antisymm (by omega) (rank_le_rank_withCol M c)
    have hgram : (M * Mᵀ).rank = (M * Mᵀ + Matrix.vecMulVec c c).rank := by
      rw [Matrix.rank_self_mul_transpose M, ← Q1Paper.augment_mul_transpose M c,
        Matrix.rank_self_mul_transpose (Q1Paper.augment M c)]
      exact heq.symm
    exact (Q1Paper.exists_mulVec_eq_iff_rank_gram M c).mpr hgram

/-! ## 4.  Axiom audit and signature checks -/


#check @elemSymmGen
#check @elemSymmGen_pos_iff_rank_ge
#check @elemSymmGen_eq_zero_iff_rank_lt
#check @claim8_disjunction
#check @withCol
#check @withCol_mul_transpose
#check @rank_le_rank_withCol

end Q1Paper.PaperI.Claim8Literal
