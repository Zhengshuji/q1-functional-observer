/-
Q1Paper/PaperI/Claim8Wire.lean

**Claim 8 (rank consistency): the disjunctive form.**  This file wires the paper's
disjunction

  `∨_t [ e_t(Γ) > 0 ∧ e_{t+1}(Γ) = 0 ∧ e_{t+1}(Γ') = 0 ]`,     `Γ = M * Mᵀ`,

to `Q1Paper.ScratchClaim8Ej.elemSymm_pos_iff_rank_ge` / `elemSymm_eq_zero_iff_rank_lt`
(`PaperI/Claim8Ej.lean`) and to `Q1Paper.claim8_rank_consistency`
(`PaperI/Claims38.lean`).

Here `elemSymm M j` is the `j`-th elementary symmetric function of the row Gram matrix
`Γ = M * Mᵀ`, defined as the sum of the principal `j × j` minors of `Γ`
(`Q1Paper.ScratchClaim8Ej.elemSymm`).  The two facts from `Claim8Ej.lean` used below are

  `elemSymm_pos_iff_rank_ge :  0 < elemSymm M j  ↔  j ≤ M.rank`,
  `elemSymm_eq_zero_iff_rank_lt :  elemSymm M j = 0  ↔  M.rank < j`.

What is proved here (each docstring names the part of the paper's disjunction it captures):

1. `exists_rank_disjunct`        — the disjunct `t = M.rank` is nonempty ("the rank is a
                                   vanishing switch point of `e_·(Γ)`").
2. `rank_eq_of_elemSymm_pattern` — maximality / uniqueness: any `t` with `e_t > 0` and
                                   `e_{t+1} = 0` must equal `M.rank`.
3. `gramBlock_eq_of_gram_eq`, `elemSymm_eq_of_gram_eq`, `rank_eq_of_elemSymm_eq`,
   `rank_eq_of_gram_eq`         — the row Gram matrix `M * Mᵀ` determines the *whole*
                                   `elemSymm` pattern and hence the rank (the paper's
                                   "rank consistency").
4. `exists_rank_disjunct_of_elemSymm_eq`, `exists_rank_disjunct_pair` — the disjunction
                                   written with both Gram matrices `Γ = M * Mᵀ` and
                                   `Γ' = M' * M'ᵀ`.

Not wired: the paper's Claim 8 uses `Γ' = Γ + c cᵀ`, the Gram matrix of the *augmented*
matrix `[M  c]`.  `Q1Paper.augment` (in `G5GramRank.lean`) lives on the column index type
`Fin n ⊕ Fin 1`, while `elemSymm` in `Claim8Ej.lean` is stated for column index `Fin n`;
applying `elemSymm` to `[M  c]` therefore needs either a reindexing `Fin n ⊕ Fin 1 ≃ Fin (n+1)`
or an `elemSymm` generalised to an arbitrary column index type.  See the closing comment for
the exact statement that is missing.

No `sorry`, no `admit`, no new axioms.  Check with
  lake env lean Q1Paper/PaperI/Claim8Wire.lean
-/

import Q1Paper.PaperI.Claim8Ej

open Matrix

namespace Q1Paper.ScratchClaim8Wire

open Q1Paper.PaperI
open Q1Paper.ScratchClaim8Ej

variable {m n : ℕ}

/-! ## 1.  The principal Gram block is a principal minor of `Γ = M * Mᵀ`

This is the only place where the definition of `gramBlock` (via `rowBlock`) is unfolded;
everything below only refers to the Gram matrix `M * Mᵀ`. -/

/-- `gramBlock M S` is the principal minor `Γ_{S,S}` of the row Gram matrix `Γ = M * Mᵀ`. -/
theorem gramBlock_eq_gram_submatrix (M : Matrix (Fin m) (Fin n) ℝ) {j : ℕ}
    (S : Set.powersetCard (Fin m) j) :
    gramBlock M S = ((M * Mᵀ).submatrix (rowEmb S) (rowEmb S)).det := by
  have h : rowBlock M S * (rowBlock M S)ᵀ =
      (M * Mᵀ).submatrix (rowEmb S) (rowEmb S) := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, rowBlock,
      id_eq]
  rw [gramBlock, h]

/-! ## 2.  Equal row Gram matrices give the same pattern -/

/-- **Equal row Gram matrices give equal principal minors.**  Both matrices have `m` rows, so
the principal index set `S` is the same for the two of them. -/
theorem gramBlock_eq_of_gram_eq {m n₁ n₂ : ℕ} (M : Matrix (Fin m) (Fin n₁) ℝ)
    (M' : Matrix (Fin m) (Fin n₂) ℝ) (h : M * Mᵀ = M' * M'ᵀ) {j : ℕ}
    (S : Set.powersetCard (Fin m) j) : gramBlock M S = gramBlock M' S := by
  rw [gramBlock_eq_gram_submatrix M S, gramBlock_eq_gram_submatrix M' S, h]

/-- **Equal row Gram matrices give identical elementary symmetric functions.**  This is the
"same pattern of vanishing" half of the paper's rank consistency. -/
theorem elemSymm_eq_of_gram_eq {m n₁ n₂ : ℕ} (M : Matrix (Fin m) (Fin n₁) ℝ)
    (M' : Matrix (Fin m) (Fin n₂) ℝ) (h : M * Mᵀ = M' * M'ᵀ) (j : ℕ) :
    elemSymm M j = elemSymm M' j := by
  simp only [elemSymm]
  exact Finset.sum_congr rfl (fun S _ => gramBlock_eq_of_gram_eq M M' h S)

/-! ## 3.  The `t`-th disjunct characterises the rank -/

/-- **Item 1: the disjunct at `t = M.rank` holds.**  The paper's disjunction
`∨_t [ e_t(Γ) > 0 ∧ e_{t+1}(Γ) = 0 ∧ … ]` is nonempty, with the switch point at `t = rank M`:
`e_t > 0` for all `t ≤ rank M` and `e_{t+1} = 0` from `t = rank M` on. -/
theorem exists_rank_disjunct (M : Matrix (Fin m) (Fin n) ℝ) :
    ∃ t : ℕ, 0 < elemSymm M t ∧ elemSymm M (t + 1) = 0 := by
  refine ⟨M.rank, ?_, ?_⟩
  · exact (elemSymm_pos_iff_rank_ge M M.rank).mpr le_rfl
  · exact (elemSymm_eq_zero_iff_rank_lt M (M.rank + 1)).mpr (Nat.lt_succ_self M.rank)

/-- **Item 2: maximality / uniqueness of the switch point.**  If `e_t(Γ) > 0` and
`e_{t+1}(Γ) = 0`, then `t` is exactly `rank M`; i.e. `rank M` is the largest `t` with
`e_t > 0`.  Equivalently, any disjunct of the paper's disjunction pins the rank down. -/
theorem rank_eq_of_elemSymm_pattern (M : Matrix (Fin m) (Fin n) ℝ) (t : ℕ)
    (hpos : 0 < elemSymm M t) (hzero : elemSymm M (t + 1) = 0) : M.rank = t := by
  have hle : t ≤ M.rank := (elemSymm_pos_iff_rank_ge M t).mp hpos
  have hlt : M.rank < t + 1 := (elemSymm_eq_zero_iff_rank_lt M (t + 1)).mp hzero
  omega

/-- **The `elemSymm` pattern alone determines the rank.**  This abstracts Item 3 below:
whatever produces the pattern equality (equal Gram matrices, or more generally any pair of
matrices whose elementary symmetric functions agree) gives equal ranks. -/
theorem rank_eq_of_elemSymm_eq {m n₁ n₂ : ℕ} (M : Matrix (Fin m) (Fin n₁) ℝ)
    (M' : Matrix (Fin m) (Fin n₂) ℝ) (hpat : ∀ j, elemSymm M j = elemSymm M' j) :
    M.rank = M'.rank := by
  have hpos : 0 < elemSymm M' M.rank := by
    rw [← hpat M.rank]
    exact (elemSymm_pos_iff_rank_ge M M.rank).mpr le_rfl
  have hzero : elemSymm M' (M.rank + 1) = 0 := by
    rw [← hpat (M.rank + 1)]
    exact (elemSymm_eq_zero_iff_rank_lt M (M.rank + 1)).mpr (Nat.lt_succ_self M.rank)
  exact (rank_eq_of_elemSymm_pattern M' M.rank hpos hzero).symm

/-- **Item 3: rank consistency for the row Gram matrix.**  If two matrices over `ℝ` (same
number of rows, possibly different numbers of columns) have the same Gram matrix `M * Mᵀ`,
then their ranks agree: the row Gram matrix determines the rank.

Note that `M * Mᵀ` and `M' * M'ᵀ` are both `m × m`, so the hypothesis typechecks even when the
column counts `n₁`, `n₂` differ. -/
theorem rank_eq_of_gram_eq {m n₁ n₂ : ℕ} (M : Matrix (Fin m) (Fin n₁) ℝ)
    (M' : Matrix (Fin m) (Fin n₂) ℝ) (h : M * Mᵀ = M' * M'ᵀ) : M.rank = M'.rank :=
  rank_eq_of_elemSymm_eq M M' (fun j => elemSymm_eq_of_gram_eq M M' h j)

/-! ## 4.  The disjunction as written for the two Gram matrices -/

/-- **The paper's disjunction for two matrices with the same `elemSymm` pattern**:
`∨_t [ e_t(Γ) > 0 ∧ e_{t+1}(Γ) = 0 ∧ e_{t+1}(Γ') = 0 ]`.  The witness is `t = rank M`. -/
theorem exists_rank_disjunct_of_elemSymm_eq {m n₁ n₂ : ℕ} (M : Matrix (Fin m) (Fin n₁) ℝ)
    (M' : Matrix (Fin m) (Fin n₂) ℝ) (hpat : ∀ j, elemSymm M j = elemSymm M' j) :
    ∃ t : ℕ, 0 < elemSymm M t ∧ elemSymm M (t + 1) = 0 ∧ elemSymm M' (t + 1) = 0 := by
  refine ⟨M.rank, ?_, ?_, ?_⟩
  · exact (elemSymm_pos_iff_rank_ge M M.rank).mpr le_rfl
  · exact (elemSymm_eq_zero_iff_rank_lt M (M.rank + 1)).mpr (Nat.lt_succ_self M.rank)
  · rw [← hpat (M.rank + 1)]
    exact (elemSymm_eq_zero_iff_rank_lt M (M.rank + 1)).mpr (Nat.lt_succ_self M.rank)

/-- **The disjunction `∨_t [ e_t(Γ) > 0 ∧ e_{t+1}(Γ) = 0 ∧ e_{t+1}(Γ') = 0 ]` for
`Γ = M * Mᵀ`, `Γ' = M' * M'ᵀ`.**  When the two Gram matrices are equal the third conjunct is
implied by the second, so this is the honest form of the paper's disjunction that the existing
pieces support. -/
theorem exists_rank_disjunct_pair {m n₁ n₂ : ℕ} (M : Matrix (Fin m) (Fin n₁) ℝ)
    (M' : Matrix (Fin m) (Fin n₂) ℝ) (h : M * Mᵀ = M' * M'ᵀ) :
    ∃ t : ℕ, 0 < elemSymm M t ∧ elemSymm M (t + 1) = 0 ∧ elemSymm M' (t + 1) = 0 :=
  exists_rank_disjunct_of_elemSymm_eq M M' (fun j => elemSymm_eq_of_gram_eq M M' h j)

/-! ## 5.  Sanity checks: no `sorry`, no extra axioms -/

#check @exists_rank_disjunct
#check @rank_eq_of_elemSymm_pattern
#check @rank_eq_of_gram_eq


/-! ## 6.  What is missing for the paper's literal `Γ' = Γ + c cᵀ` (not proved here)

The paper's Claim 8 takes `Γ' = M Mᵀ + c cᵀ`, the Gram matrix of the augmented matrix
`[M  c] = Q1Paper.augment M c`.  `augment M c` has column index `Fin n ⊕ Fin 1`, whereas
`elemSymm` (`PaperI/Claim8Ej.lean`) is stated for column index `Fin n`.  So the literal
disjunct `e_{t+1}(Γ') = 0` cannot be written with `elemSymm` without one of

* a reindexing `e : Fin n ⊕ Fin 1 ≃ Fin (n+1)` together with
  `U := (augment M c).submatrix id e.symm`, for which `U * Uᵀ = (augment M c) * (augment M c)ᵀ`
  (entrywise) and `Matrix.rank_reindex` gives `U.rank = (augment M c).rank`; or
* an `elemSymm` generalised to an arbitrary finite column index type `ι`.  (The underlying
  Cauchy–Binet lemma `Matrix.det_mul_transpose_eq_sum_det_submatrix` of
  `PaperI/CauchyBinet.lean` is already stated for a general `ι`; only `Claim8Ej.lean`
  specialises the column index to `Fin n`.)

With either of these, the paper's Claim 8 in disjunctive form would read

  `(∃ b, M.mulVec b = c) ↔ ∃ t, 0 < elemSymm M t ∧ elemSymm M (t + 1) = 0 ∧ e_{t+1}(Γ') = 0`,

whose `→` direction is `exists_rank_disjunct` plus "solvable ⟹ `rank [M c] = rank M`" and
whose `←` direction is `rank_eq_of_elemSymm_pattern` plus `Q1Paper.rank_augment_eq_iff`
(`G5GramRank.lean`).  That equivalence is **not** formalised here: it is recorded only to pin
down the missing ingredient, and it is not claimed as verified. -/

end Q1Paper.ScratchClaim8Wire
