import Q1Paper.PaperI.S03_Certificate.MinorRank
import Q1Paper.LeftInverseAdjugate
/-!
Q1Paper/PaperI/S02_Subspace/RankFactorization.lean

**Rank factorisation with explicit one-sided inverses.**

For a matrix `H` over a field with `H.rank = ω`, we produce

* `X : Matrix ι (Fin ω) K`   (the pivot columns of a nonvanishing `ω × ω` minor),
* `B : Matrix (Fin ω) (Fin k) K`  (the "coordinates" of the columns of `H` in those
  pivot columns),
* `XL : Matrix (Fin ω) ι K`   (a left inverse of `X`),
* `BR : Matrix (Fin k) (Fin ω) K` (a right inverse of `B`),

with `X * B = H`, `XL * X = 1`, `B * BR = 1`.

Main construction: pick, from `exists_det_submatrix_ne_zero_of_rank`, injective
`ρ : Fin ω → Fin m`, `κ : Fin ω → Fin k` with `M := H.submatrix ρ κ` invertible
(`M.det ≠ 0`).  Put

  `X  = H.submatrix id κ`,          `Minv = M.det⁻¹ • M.adjugate`,
  `B  = Minv * H.submatrix ρ id`,   `XL = Minv * rowSel ρ`,
  `BR = colSel κ`.

Then

* `X * B = H`: the column spaces of `X` and `H` agree (`X` consists of columns of
  `H`, and both spans have dimension `ω`), so `H` factors through the pivot columns,
  `H = X * B` (`exists_factor_through_cols`).  Slicing that factorisation at the
  pivot rows gives `M * B = H.submatrix ρ id`, hence
  `B = Minv * M * B = Minv * H.submatrix ρ id`, and therefore
  `X * B = X * (Minv * H.submatrix ρ id) = H`.
* `B.submatrix id κ = 1` follows from `B = Minv * H.submatrix ρ id` and `Minv * M = 1`;
  consequently `B * BR = B * colSel κ = B.submatrix id κ = 1`.
* `XL * X = Minv * (rowSel ρ * X) = Minv * M = 1`.

The same statement for an arbitrary finite row type is obtained by reindexing
(`exists_rank_factorization_arb`).

Fully proved: no placeholders and no new axioms, over an arbitrary field.
-/


namespace Q1Paper.PaperI.RankFactorization

open Matrix
open Q1Paper.PaperI (exists_det_submatrix_ne_zero_of_rank)

variable {K : Type*} [Field K]

/-! ## Selecting columns: the matrix `colSel κ` and its two basic identities -/

/-- `colSel κ` is the `k × ω` matrix whose `j`-th column is the `κ j`-th unit vector;
multiplying on the right selects the columns `κ`. -/
def colSel {k ω : ℕ} (κ : Fin ω → Fin k) : Matrix (Fin k) (Fin ω) K :=
  Matrix.of fun i j => if κ j = i then (1 : K) else 0

/-- Right multiplication by `colSel κ` selects the columns `κ`. -/
theorem submatrix_cols_eq_mul {m k ω : ℕ} (H : Matrix (Fin m) (Fin k) K) (κ : Fin ω → Fin k) :
    H.submatrix id κ = H * colSel (K := K) κ := by
  ext i j
  rw [Matrix.submatrix_apply, id, Matrix.mul_apply]
  rw [Finset.sum_eq_single (κ j)]
  · simp [colSel]
  · intro b _ hb
    simp [colSel, Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ (κ j)) h

/-- The `κ`-columns of `B * colSel κ` are those of `B`. -/
theorem mul_colSel {k ω : ℕ} (B : Matrix (Fin ω) (Fin k) K) (κ : Fin ω → Fin k) :
    B * colSel (K := K) κ = B.submatrix id κ := by
  ext i j
  rw [Matrix.mul_apply, Matrix.submatrix_apply, id]
  rw [Finset.sum_eq_single (κ j)]
  · simp [colSel]
  · intro b _ hb
    simp [colSel, Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ (κ j)) h

/-! ## Factoring `H` through its pivot columns -/

/-- **A matrix of rank `ω` factors through any set of `ω` columns of rank `ω`.**
The columns of `H.submatrix id κ` span the same space as the columns of `H`, so each
column of `H` is a combination of the former. -/
theorem exists_factor_through_cols {m k ω : ℕ} (H : Matrix (Fin m) (Fin k) K)
    (κ : Fin ω → Fin k) (hrank : H.rank = ω) (hrankκ : (H.submatrix id κ).rank = ω) :
    ∃ B : Matrix (Fin ω) (Fin k) K, H.submatrix id κ * B = H := by
  classical
  -- the two column spaces agree
  have hle : (H.submatrix id κ).mulVecLin.range ≤ H.mulVecLin.range := by
    rintro v ⟨c, rfl⟩
    refine ⟨colSel (K := K) κ *ᵥ c, ?_⟩
    simp only [Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec, ← submatrix_cols_eq_mul]
  have hfin : Module.finrank K ↥((H.submatrix id κ).mulVecLin.range)
      = Module.finrank K ↥(H.mulVecLin.range) := by
    have h1 : (H.submatrix id κ).rank
        = Module.finrank K ↥((H.submatrix id κ).mulVecLin.range) := rfl
    have h2 : H.rank = Module.finrank K ↥(H.mulVecLin.range) := rfl
    rw [← h1, ← h2, hrankκ, hrank]
  have hrange : (H.submatrix id κ).mulVecLin.range = H.mulVecLin.range :=
    Submodule.eq_of_le_of_finrank_eq hle hfin
  -- every column of `H` is a combination of the `κ`-columns
  have hex : ∀ j : Fin k, ∃ c : Fin ω → K,
      (H.submatrix id κ) *ᵥ c = H *ᵥ Pi.single j 1 := by
    intro j
    have hmem : H *ᵥ Pi.single j 1 ∈ (H.submatrix id κ).mulVecLin.range := by
      rw [hrange]
      exact LinearMap.mem_range.mpr ⟨Pi.single j 1, by simp⟩
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, by simpa using hc⟩
  choose c hc using hex
  refine ⟨Matrix.of fun i j => c j i, ?_⟩
  ext i j
  have hbridge : ((H.submatrix id κ) * (Matrix.of fun i j => c j i)) i j
      = ((H.submatrix id κ) *ᵥ fun l => c j l) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hbridge, hc j, Matrix.mulVec_single]
  simp

/-! ## The rank factorisation with explicit inverses -/

/-- **Rank factorisation with explicit left/right inverses.**
For `H : Matrix (Fin m) (Fin k) K` of rank `ω` there are
`X : Matrix (Fin m) (Fin ω) K`, `B : Matrix (Fin ω) (Fin k) K`,
`XL : Matrix (Fin ω) (Fin m) K`, `BR : Matrix (Fin k) (Fin ω) K` with
`X * B = H`, `XL * X = 1` and `B * BR = 1`.  (No positivity of `ω` is needed.) -/
theorem exists_rank_factorization_of_rank {m k ω : ℕ} (H : Matrix (Fin m) (Fin k) K)
    (hrank : H.rank = ω) :
    ∃ (X : Matrix (Fin m) (Fin ω) K) (B : Matrix (Fin ω) (Fin k) K)
      (XL : Matrix (Fin ω) (Fin m) K) (BR : Matrix (Fin k) (Fin ω) K),
      X * B = H ∧ XL * X = 1 ∧ B * BR = 1 := by
  classical
  -- an invertible `ω × ω` minor
  obtain ⟨ρ, κ, hρ, hκ, hdet⟩ := exists_det_submatrix_ne_zero_of_rank H hrank
  set M : Matrix (Fin ω) (Fin ω) K := H.submatrix ρ κ with hM
  have hdetM : M.det ≠ 0 := hdet
  -- the inverse of `M`, written with the adjugate
  set Minv : Matrix (Fin ω) (Fin ω) K := (M.det)⁻¹ • M.adjugate with hMinv
  have hMinvM : Minv * M = 1 := by
    rw [hMinv, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, inv_mul_cancel₀ hdetM,
      one_smul]
  -- the pivot-column block has rank `ω`
  have hminor : (H.submatrix id κ).submatrix ρ id = M := by
    ext i j
    simp [hM]
  have hMrank : M.rank = ω := by
    rw [Matrix.rank_of_det_ne_zero hdetM]
    simp
  have hrankκ : (H.submatrix id κ).rank = ω := by
    apply le_antisymm
    · calc (H.submatrix id κ).rank ≤ H.rank := Matrix.rank_submatrix_le H id κ
        _ = ω := hrank
    · have h := Matrix.rank_submatrix_le (H.submatrix id κ) ρ id
      rwa [hminor, hMrank] at h
  -- factor `H` through the pivot columns
  obtain ⟨B, hHB⟩ := exists_factor_through_cols H κ hrank hrankκ
  -- the `ρ`-row slice of the factorisation
  have hMB : M * B = H.submatrix ρ id := by
    ext i j
    have h := congrFun (congrFun hHB (ρ i)) j
    rw [Matrix.mul_apply] at h
    rw [hM, Matrix.mul_apply]
    simp only [Matrix.submatrix_apply, id]
    exact h
  -- hence `B` is `Minv * (pivot rows)`
  have hB_eq : B = Minv * H.submatrix ρ id := by
    rw [← Matrix.one_mul B, ← hMinvM, Matrix.mul_assoc, hMB]
  -- the `κ`-columns of `B` are the identity
  have hBκ : B.submatrix id κ = 1 := by
    rw [hB_eq]
    ext i j
    rw [Matrix.submatrix_apply, id]
    have h1 : (Minv * H.submatrix ρ id) i (κ j) = (Minv * M) i j := by
      simp [Matrix.mul_apply, hM]
    rw [h1, hMinvM]
  refine ⟨H.submatrix id κ, B, Minv * Q1Paper.rowSel ρ, colSel (K := K) κ, ?_, ?_, ?_⟩
  · have h := hHB
    rw [hB_eq] at h
    rw [hB_eq]
    exact h
  · rw [Matrix.mul_assoc, Q1Paper.rowSel_mul, hminor]
    exact hMinvM
  · rw [mul_colSel]
    exact hBκ

/-- **The requested form**, with the hypothesis `1 ≤ ω` (which the construction does
not actually use; see `exists_rank_factorization_of_rank`). -/
theorem exists_rank_factorization {m k ω : ℕ} (H : Matrix (Fin m) (Fin k) K)
    (hrank : H.rank = ω) (_hω : 1 ≤ ω) :
    ∃ (X : Matrix (Fin m) (Fin ω) K) (B : Matrix (Fin ω) (Fin k) K)
      (XL : Matrix (Fin ω) (Fin m) K) (BR : Matrix (Fin k) (Fin ω) K),
      X * B = H ∧ XL * X = 1 ∧ B * BR = 1 :=
  exists_rank_factorization_of_rank H hrank

/-! ## An arbitrary finite row type -/

/-- **The same result for an arbitrary finite row type `ι`**, by reindexing along a
bijection `Fin (card ι) ≃ ι`. -/
theorem exists_rank_factorization_arb {ι : Type*} [Fintype ι] {k ω : ℕ}
    (H : Matrix ι (Fin k) K) (hrank : H.rank = ω) :
    ∃ (X : Matrix ι (Fin ω) K) (B : Matrix (Fin ω) (Fin k) K)
      (XL : Matrix (Fin ω) ι K) (BR : Matrix (Fin k) (Fin ω) K),
      X * B = H ∧ XL * X = 1 ∧ B * BR = 1 := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  -- rank of the reindexed matrix
  have hle : (H.submatrix (e : Fin (Fintype.card ι) → ι) id).rank ≤ H.rank :=
    Matrix.rank_submatrix_le H (e : Fin (Fintype.card ι) → ι) id
  have hge : H.rank ≤ (H.submatrix (e : Fin (Fintype.card ι) → ι) id).rank := by
    have h := Matrix.rank_submatrix_le (H.submatrix (e : Fin (Fintype.card ι) → ι) id)
      (e.symm : ι → Fin (Fintype.card ι)) id
    have hEq : (H.submatrix (e : Fin (Fintype.card ι) → ι) id).submatrix
        (e.symm : ι → Fin (Fintype.card ι)) id = H := by
      ext i j
      simp
    rw [hEq] at h
    exact h
  have hH' : (H.submatrix (e : Fin (Fintype.card ι) → ι) id).rank = ω := by
    apply le_antisymm
    · calc (H.submatrix (e : Fin (Fintype.card ι) → ι) id).rank ≤ H.rank := hle
        _ = ω := hrank
    · exact hrank ▸ hge
  obtain ⟨X', B, XL', BR, hXB, hXL, hBR⟩ :=
    exists_rank_factorization_of_rank (H.submatrix (e : Fin (Fintype.card ι) → ι) id) hH'
  -- the selection matrix for the rows `e`
  let S : Matrix (Fin (Fintype.card ι)) ι K :=
    Matrix.of fun i j => if (e : Fin (Fintype.card ι) → ι) i = j then 1 else 0
  have hSX : S * X'.submatrix (e.symm : ι → Fin (Fintype.card ι)) id = X' := by
    ext i j
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (e i)]
    · simp [S]
    · intro b _ hb
      have hne : (e : Fin (Fintype.card ι) → ι) i ≠ b := Ne.symm hb
      simp [S, hne]
    · intro h
      exact absurd (Finset.mem_univ (e i)) h
  refine ⟨X'.submatrix (e.symm : ι → Fin (Fintype.card ι)) id, B, XL' * S, BR, ?_, ?_, ?_⟩
  · -- `X * B = H`
    ext i j
    have h := congrFun (congrFun hXB (e.symm i)) j
    rw [Matrix.mul_apply] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.submatrix_apply, id] at h ⊢
    rw [h]
    simp
  · -- `XL * X = 1`
    rw [Matrix.mul_assoc, hSX]
    exact hXL
  · -- `B * BR = 1`
    exact hBR

end Q1Paper.PaperI.RankFactorization
