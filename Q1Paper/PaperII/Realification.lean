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

end Q1Paper.PaperII
