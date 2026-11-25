/-
Q1Paper/PaperII/Realification.lean

Bridges for the real-compression lemma (the upgrade of the complex-design results
to the paper's real-design specification `DECℂ`).

The pair row space `row[H  H_A]` is encoded in `K^{k+k}` by stacking the two blocks
of each row (`pairRows`); the column split `Φ` reads that encoding as row pairs.
Complexifying a real matrix commutes with this encoding, and the dimension of the
pair row space is the rank of the encoded matrix, so `rank_map_ofReal` gives
`dim_ℂ W = dim_ℝ V` for a real design — the identity the compression needs.

Contents.
* `pairRows` — the encoded matrix `row ↦ (row of H, row of H_A)`.
* `Φ_pairRows` — `Φ` reads it as the row pair.
* `pairRowSpace_eq_map_pairRows` — `row[H H_A]` is the `Φ`-image of its row space.
* `finrank_pairRowSpace_eq_rank` — its dimension is the rank of the encoded matrix.
* `pairRows_map` — encoding commutes with complexification.

Next step: the compression itself — a real design of `r` rows re-realised with
`t = dim (W/W₀)` rows by applying Paper I's `claim4_converse` over `ℝ` to the real
row space and complexifying.
-/

import Q1Paper.PaperII.Saturate
import Q1Paper.PaperI.S08_ChartEquivalence.DecComplex

open Module Matrix

namespace Q1Paper.PaperII

variable {K : Type*} [Field K] {k : ℕ}

/-- The encoded matrix whose rows are the pairs `(H i, H_A i)`. -/
def pairRows {q : Type*} {k : ℕ} (H : Matrix q (Fin k) K) (HA : Matrix q (Fin k) K) :
    Matrix q (Fin (k + k)) K :=
  fun i => Fin.addCases (fun j => H i j) (fun j => HA i j)

/-- `Φ` reads an encoded row as the row pair. -/
theorem Φ_pairRows {q : Type*} {k : ℕ} (H : Matrix q (Fin k) K) (HA : Matrix q (Fin k) K)
    (i : q) : Φ (K := K) (pairRows H HA i) = (H i, HA i) := by
  rw [Φ_apply]
  apply Prod.ext <;> funext j
  · show pairRows H HA i (finSumFinEquiv (Sum.inl j)) = H i j
    rw [finSumFinEquiv_apply_left]
    exact Fin.addCases_left j
  · show pairRows H HA i (finSumFinEquiv (Sum.inr j)) = HA i j
    rw [finSumFinEquiv_apply_right]
    exact Fin.addCases_right j

/-- **The pair row space is the `Φ`-image of the encoded row space.** -/
theorem pairRowSpace_eq_map_pairRows {q : Type*} [Fintype q] {k : ℕ}
    (H : Matrix q (Fin k) K) (HA : Matrix q (Fin k) K) :
    Q1Paper.pairRowSpace H HA
      = Submodule.map (Φ (K := K)).toLinearMap
        (Q1Subspace.rowSpace (pairRows H HA)) := by
  rw [Q1Paper.pairRowSpace, Q1Subspace.rowSpace, Submodule.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨pairRows H HA i, ⟨i, rfl⟩, Φ_pairRows H HA i⟩
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (Φ_pairRows H HA i).symm⟩

/-- **The dimension of a pair row space is the rank of the encoded matrix.** -/
theorem finrank_pairRowSpace_eq_rank {q : Type*} [Fintype q] {k : ℕ}
    (H : Matrix q (Fin k) K) (HA : Matrix q (Fin k) K) :
    finrank K ↥(Q1Paper.pairRowSpace H HA) = Matrix.rank (pairRows H HA) := by
  rw [pairRowSpace_eq_map_pairRows]
  rw [LinearEquiv.finrank_map_eq (Φ (K := K)) (Q1Subspace.rowSpace (pairRows H HA))]
  exact (Q1Subspace.rank_eq_finrank_rowSpace (pairRows H HA)).symm

/-- **Encoding commutes with complexification.** -/
theorem pairRows_map {q : Type*} {k : ℕ}
    (H : Matrix q (Fin k) ℝ) (HA : Matrix q (Fin k) ℝ) :
    pairRows (H.map (algebraMap ℝ ℂ)) (HA.map (algebraMap ℝ ℂ))
      = (pairRows H HA).map (algebraMap ℝ ℂ) := by
  ext i t
  refine Fin.addCases (motive := fun t =>
    pairRows (H.map (algebraMap ℝ ℂ)) (HA.map (algebraMap ℝ ℂ)) i t
      = (pairRows H HA).map (algebraMap ℝ ℂ) i t) ?_ ?_ t
  · intro j
    show Fin.addCases (fun j => (H.map (algebraMap ℝ ℂ)) i j)
        (fun j => (HA.map (algebraMap ℝ ℂ)) i j) (Fin.castAdd k j)
      = (algebraMap ℝ ℂ) (Fin.addCases (fun j => H i j) (fun j => HA i j) (Fin.castAdd k j))
    rw [Fin.addCases_left, Fin.addCases_left]
    rfl
  · intro j
    show Fin.addCases (fun j => (H.map (algebraMap ℝ ℂ)) i j)
        (fun j => (HA.map (algebraMap ℝ ℂ)) i j) (Fin.natAdd k j)
      = (algebraMap ℝ ℂ) (Fin.addCases (fun j => H i j) (fun j => HA i j) (Fin.natAdd k j))
    rw [Fin.addCases_right, Fin.addCases_right]
    rfl


/-- Multiplication commutes with the row encoding. -/
theorem mul_pairRows {q : Type*} [Fintype q] {n k : ℕ}
    (X : Matrix q (Fin n) K) (H : Matrix (Fin n) (Fin k) K) (HA : Matrix (Fin n) (Fin k) K) :
    X * pairRows H HA = pairRows (X * H) (X * HA) := by
  ext i t
  refine Fin.addCases (motive := fun t =>
    (X * pairRows H HA) i t = pairRows (X * H) (X * HA) i t) ?_ ?_ t
  · intro j
    rw [Matrix.mul_apply]
    rw [show pairRows (X * H) (X * HA) i (Fin.castAdd k j) = (X * H) i j from
      Fin.addCases_left j]
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show pairRows H HA l (Fin.castAdd k j) = H l j from Fin.addCases_left j]
  · intro j
    rw [Matrix.mul_apply]
    rw [show pairRows (X * H) (X * HA) i (Fin.natAdd k j) = (X * HA) i j from
      Fin.addCases_right j]
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show pairRows H HA l (Fin.natAdd k j) = HA l j from Fin.addCases_right j]


/-- **`W` is the `Φ`-image of the complexified real row space.** -/
theorem WR_eq_map_complex {r0 n k r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (R : Matrix (Fin r) (Fin n) ℝ) :
    WR A (N.map (algebraMap ℝ ℂ)) L0 R
      = Submodule.map (Φ (K := ℂ)).toLinearMap
        (Q1Subspace.rowSpace
          ((Matrix.fromRows L0 R * pairRows N (A * N)).map (algebraMap ℝ ℂ))) := by
  have hL : Lc L0 R = (Matrix.fromRows L0 R).map (algebraMap ℝ ℂ) := by
    rw [← fromRows_Lc]
    exact Q1Paper.Thm5.fromRows_map_ofReal L0 R
  have hN : (N.map (algebraMap ℝ ℂ)) = (N.map (algebraMap ℝ ℂ)) := rfl
  have hA : Ac A * N.map (algebraMap ℝ ℂ) = (A * N).map (algebraMap ℝ ℂ) := by
    rw [Ac, Matrix.map_mul]
  have h1 : Lc L0 R * N.map (algebraMap ℝ ℂ)
      = ((Matrix.fromRows L0 R) * N).map (algebraMap ℝ ℂ) := by
    rw [hL]
    exact Matrix.map_mul.symm
  have h2 : Lc L0 R * (Ac A * N.map (algebraMap ℝ ℂ))
      = ((Matrix.fromRows L0 R) * (A * N)).map (algebraMap ℝ ℂ) := by
    rw [hA, hL]
    exact Matrix.map_mul.symm
  calc WR A (N.map (algebraMap ℝ ℂ)) L0 R
      = Submodule.map (Φ (K := ℂ)).toLinearMap
          (Q1Subspace.rowSpace (pairRows (Lc L0 R * N.map (algebraMap ℝ ℂ))
            (Lc L0 R * (Ac A * N.map (algebraMap ℝ ℂ))))) := by
        rw [WR, pairRowSpace_eq_map_pairRows]
    _ = Submodule.map (Φ (K := ℂ)).toLinearMap
          (Q1Subspace.rowSpace (pairRows (((Matrix.fromRows L0 R) * N).map (algebraMap ℝ ℂ))
            (((Matrix.fromRows L0 R) * (A * N)).map (algebraMap ℝ ℂ)))) := by
        rw [h1, h2]
    _ = Submodule.map (Φ (K := ℂ)).toLinearMap
          (Q1Subspace.rowSpace ((pairRows ((Matrix.fromRows L0 R) * N)
            ((Matrix.fromRows L0 R) * (A * N))).map (algebraMap ℝ ℂ))) := by
        rw [pairRows_map]
    _ = Submodule.map (Φ (K := ℂ)).toLinearMap
          (Q1Subspace.rowSpace
            ((Matrix.fromRows L0 R * pairRows N (A * N)).map (algebraMap ℝ ℂ))) := by
        rw [mul_pairRows]

/-- **The dimension identity for a real design**: `dim W = dim V`, `V` the real row
space. -/
theorem finrank_WR_eq {r0 n k r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (R : Matrix (Fin r) (Fin n) ℝ) :
    finrank ℂ ↥(WR A (N.map (algebraMap ℝ ℂ)) L0 R)
      = finrank ℝ ↥(Q1Subspace.rowSpace (Matrix.fromRows L0 R * pairRows N (A * N))) := by
  rw [WR_eq_map_complex]
  rw [LinearEquiv.finrank_map_eq (Φ (K := ℂ) (k := k))
    (Q1Subspace.rowSpace ((Matrix.fromRows L0 R * pairRows N (A * N)).map (algebraMap ℝ ℂ)))]
  have h1 : finrank ℂ ↥(Q1Subspace.rowSpace
        ((Matrix.fromRows L0 R * pairRows N (A * N)).map (algebraMap ℝ ℂ)))
      = ((Matrix.fromRows L0 R * pairRows N (A * N)).map (algebraMap ℝ ℂ)).rank :=
    (Q1Subspace.rank_eq_finrank_rowSpace _).symm
  rw [h1]
  have h2 : ((Matrix.fromRows L0 R * pairRows N (A * N)).map (algebraMap ℝ ℂ)).rank
      = (Matrix.fromRows L0 R * pairRows N (A * N)).rank :=
    Q1Paper.PaperI.DecComplex.rank_map_ofReal_any _
  rw [h2]
  have h3 : (Matrix.fromRows L0 R * pairRows N (A * N)).rank
      = finrank ℝ ↥(Q1Subspace.rowSpace (Matrix.fromRows L0 R * pairRows N (A * N))) :=
    Q1Subspace.rank_eq_finrank_rowSpace _
  rw [h3]

end Q1Paper.PaperII


