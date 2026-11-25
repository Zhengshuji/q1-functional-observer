
import Q1Paper.PaperI.S03_Certificate.MinorRank
import Q1Paper.PaperI.S02_Subspace.SolveCriterion

/-!
Q1Paper/PaperI/S04_Rationality/RatDescent.lean

**A rational linear system solvable over `ℝ` is solvable over `ℚ`.**

This is the general linear-algebra fact needed by Claim 16 of the paper.

Main results:

* `rank_map_ratReal_arb` : `rank (M.map (algebraMap ℚ ℝ)) = rank M` for
  arbitrary finite index types (the `ℚ → ℝ` analogue of
  `Q1Paper.Thm5.rank_map_ofReal_arb`, proved the same way: rank = largest
  nonzero minor, and `algebraMap ℚ ℝ` is injective);
* `exists_rat_solution_of_exists_real_solution_arb` : the main theorem for
  arbitrary finite index types;
* `exists_rat_solution_of_exists_real_solution` : the same statement for
  `Fin m` / `Fin n` (the exact shape requested);
* `exists_mulVec_rat_solution_of_exists_mulVec_real_solution` : the
  `Matrix.mulVec` phrasing.

Route.  A real solution satisfies the rank criterion over `ℝ`
(`Q1Subspace.exists_mulVec_eq_iff_rank_fromRows`), i.e. the augmented matrix
`[A b]` (written `fromRows Aᵀ b`) and `A` have the same rank after scalar
extension to `ℝ`.  Scalar extension along `ℚ → ℝ` preserves the rank
(`rank_map_ratReal_arb`), so `rank [A b] = rank A` already holds over `ℚ`;
the rank criterion over `ℚ` then produces a rational solution.

No unfinished proofs and no new axioms.
-/


open scoped BigOperators
open Matrix

/-! ## Rank is preserved by scalar extension `ℚ → ℝ` -/

/-- Scalar extension along `ℚ → ℝ` commutes with taking submatrices. -/
theorem map_submatrix_ratReal {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) {ω : ℕ}
    (ρ : Fin ω → Fin m) (κ : Fin ω → Fin n) :
    (M.map (algebraMap ℚ ℝ)).submatrix ρ κ = (M.submatrix ρ κ).map (algebraMap ℚ ℝ) := by
  ext i j
  rfl

/-- Scalar extension along `ℚ → ℝ` commutes with the determinant. -/
theorem det_map_ratReal {ω : ℕ} (A : Matrix (Fin ω) (Fin ω) ℚ) :
    (A.map (algebraMap ℚ ℝ)).det = algebraMap ℚ ℝ A.det := by
  have h := RingHom.map_det (algebraMap ℚ ℝ) A
  rw [show (algebraMap ℚ ℝ).mapMatrix A = A.map (algebraMap ℚ ℝ) from rfl] at h
  exact h.symm

/-- `rank M_ℝ ≤ rank M`: a nonzero minor of `M_ℝ` comes from a nonzero minor of `M`. -/
theorem rank_map_ratReal_le {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) :
    (M.map (algebraMap ℚ ℝ)).rank ≤ M.rank := by
  obtain ⟨ρ, κ, _, _, hdet⟩ :=
    Q1Paper.PaperI.exists_det_submatrix_ne_zero_of_rank (M.map (algebraMap ℚ ℝ)) rfl
  have h1 : (M.submatrix ρ κ).det ≠ 0 := by
    intro h0
    apply hdet
    rw [map_submatrix_ratReal, det_map_ratReal, h0, map_zero]
  exact Q1Paper.PaperI.rank_le_of_det_maximalMinor_ne_zero M ρ κ h1

/-- `rank M ≤ rank M_ℝ`: scalar-extending a nonzero minor keeps it nonzero. -/
theorem rank_le_map_ratReal {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) :
    M.rank ≤ (M.map (algebraMap ℚ ℝ)).rank := by
  obtain ⟨ρ, κ, _, _, hdet⟩ :=
    Q1Paper.PaperI.exists_det_submatrix_ne_zero_of_rank M rfl
  have h1 : ((M.map (algebraMap ℚ ℝ)).submatrix ρ κ).det ≠ 0 := by
    rw [map_submatrix_ratReal, det_map_ratReal]
    intro h0
    exact hdet ((algebraMap ℚ ℝ).injective (by rw [h0, map_zero]))
  exact Q1Paper.PaperI.rank_le_of_det_maximalMinor_ne_zero
    (M.map (algebraMap ℚ ℝ)) ρ κ h1

/-- Scalar extension along `ℚ → ℝ` does not change the rank (`Fin`-indexed form). -/
theorem rank_map_ratReal {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) :
    (M.map (algebraMap ℚ ℝ)).rank = M.rank :=
  le_antisymm (rank_map_ratReal_le M) (rank_le_map_ratReal M)

/-- Scalar extension along `ℚ → ℝ` does not change the rank (arbitrary finite
index types), obtained from the `Fin`-indexed form by reindexing. -/
theorem rank_map_ratReal_arb {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℚ) :
    (M.map (algebraMap ℚ ℝ)).rank = M.rank := by
  classical
  let em : m ≃ Fin (Fintype.card m) := Fintype.equivFin m
  let en : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  have hre : ((M.map (algebraMap ℚ ℝ)).reindex em en)
      = (M.reindex em en).map (algebraMap ℚ ℝ) := by
    ext i j
    simp [Matrix.reindex_apply, Matrix.map_apply]
  calc (M.map (algebraMap ℚ ℝ)).rank
      = ((M.map (algebraMap ℚ ℝ)).reindex em en).rank :=
        (Matrix.rank_reindex em en _).symm
    _ = ((M.reindex em en).map (algebraMap ℚ ℝ)).rank := by rw [hre]
    _ = (M.reindex em en).rank := rank_map_ratReal _
    _ = M.rank := Matrix.rank_reindex em en M

/-! ## The main theorem -/

/-- **A rational linear system solvable over `ℝ` is solvable over `ℚ`**
(arbitrary finite index types). -/
theorem exists_rat_solution_of_exists_real_solution_arb
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) (b : m → ℚ)
    (h : ∃ x : n → ℝ, ∀ i, ∑ j, (A i j : ℝ) * x j = (b i : ℝ)) :
    ∃ y : n → ℚ, ∀ i, ∑ j, A i j * y j = b i := by
  classical
  -- The augmented matrix `[A b]`, written as the row augmentation `[Aᵀ; b]`.
  set N : Matrix (n ⊕ PUnit.{1}) m ℚ :=
    Matrix.fromRows A.transpose (fun _ : PUnit.{1} => b) with hN
  -- The same augmentation after scalar extension to `ℝ`.
  set Nreal : Matrix (n ⊕ PUnit.{1}) m ℝ :=
    Matrix.fromRows (A.map (algebraMap ℚ ℝ)).transpose
      (fun _ : PUnit.{1} => fun i => algebraMap ℚ ℝ (b i)) with hNreal
  -- The real system in `mulVec` form.
  have hreal : ∃ x : n → ℝ,
      (A.map (algebraMap ℚ ℝ)).mulVec x = fun i => algebraMap ℚ ℝ (b i) := by
    obtain ⟨x, hx⟩ := h
    refine ⟨x, ?_⟩
    funext i
    simpa [Matrix.mulVec_apply_eq_sum, Matrix.map_apply] using hx i
  -- The rank criterion over `ℝ`.
  have hrank_real : Nreal.rank = (A.map (algebraMap ℚ ℝ)).rank := by
    have hcrit :
        (Matrix.fromRows (A.map (algebraMap ℚ ℝ)).transpose
          (fun _ : PUnit.{1} => fun i => algebraMap ℚ ℝ (b i))).rank
          = (A.map (algebraMap ℚ ℝ)).rank :=
      (Q1Subspace.exists_mulVec_eq_iff_rank_fromRows
        (A.map (algebraMap ℚ ℝ)) (fun i => algebraMap ℚ ℝ (b i))).mp hreal
    simpa [hNreal] using hcrit
  -- Scalar extension of `N` is `Nreal`.
  have hNmap : Nreal = N.map (algebraMap ℚ ℝ) := by
    ext i j
    cases i with
    | inl i => rfl
    | inr u => rfl
  have hrank_real' : (N.map (algebraMap ℚ ℝ)).rank
      = (A.map (algebraMap ℚ ℝ)).rank := by
    rw [← hNmap]
    exact hrank_real
  -- Transport the rank equality back to `ℚ`.
  have hrank : N.rank = A.rank := by
    rw [← rank_map_ratReal_arb N, ← rank_map_ratReal_arb A]
    exact hrank_real'
  -- The rank criterion over `ℚ`.
  obtain ⟨y, hy⟩ : ∃ y : n → ℚ, A.mulVec y = b := by
    refine (Q1Subspace.exists_mulVec_eq_iff_rank_fromRows A b).mpr ?_
    simpa [hN] using hrank
  exact ⟨y, fun i => by simpa [Matrix.mulVec_apply_eq_sum] using congrFun hy i⟩

/-- **The requested statement.**  A rational linear system
`A y = b` that has a real solution has a rational solution. -/
theorem exists_rat_solution_of_exists_real_solution
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (h : ∃ x : Fin n → ℝ, ∀ i, ∑ j, (A i j : ℝ) * x j = (b i : ℝ)) :
    ∃ y : Fin n → ℚ, ∀ i, ∑ j, A i j * y j = b i :=
  exists_rat_solution_of_exists_real_solution_arb A b h

/-- **`Matrix.mulVec` phrasing**: a rational system that has a real solution has
a rational solution. -/
theorem exists_mulVec_rat_solution_of_exists_mulVec_real_solution
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) (b : m → ℚ)
    (h : ∃ x : n → ℝ,
      (A.map (algebraMap ℚ ℝ)).mulVec x = fun i => algebraMap ℚ ℝ (b i)) :
    ∃ y : n → ℚ, A.mulVec y = b := by
  classical
  obtain ⟨x, hx⟩ := h
  have h' : ∃ x : n → ℝ, ∀ i, ∑ j, (A i j : ℝ) * x j = (b i : ℝ) := by
    refine ⟨x, fun i => ?_⟩
    simpa [Matrix.mulVec_apply_eq_sum, Matrix.map_apply] using congrFun hx i
  obtain ⟨y, hy⟩ := exists_rat_solution_of_exists_real_solution_arb A b h'
  exact ⟨y, by funext i; simpa [Matrix.mulVec_apply_eq_sum] using hy i⟩
