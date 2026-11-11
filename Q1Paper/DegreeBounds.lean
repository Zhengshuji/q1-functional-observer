/-
Q1Paper/DegreeBounds.lean

Degree estimates for determinants and adjugates over `K[X]` (G3b).

* an integer cast, and a power of `-1`, have degree zero;
* row-graded determinant bound: if row `i` has entries of `natDegree ≤ d i`, then
  `(det M).natDegree ≤ ∑ i, d i`;
* hence the adjugate entries of a matrix with linear entries have degree `≤ n - 1`
  (`adjugate_apply` writes them as the determinant of the matrix with one row replaced by
  a unit vector).
-/

import Mathlib.LinearAlgebra.Matrix.Adjugate

open Matrix Polynomial
open scoped BigOperators

namespace Q1Paper

variable {K : Type*} [Field K]

/-- An integer cast into `K[X]` has degree at most zero. -/
theorem natDegree_intCast_le (c : ℤ) : ((c : K[X])).natDegree ≤ 0 := by
  have h : ((c : K[X])) = C ((c : K)) := by push_cast; rfl
  rw [h, natDegree_C]

/-- A power of `-1` has degree zero. -/
theorem natDegree_neg_one_pow (j : ℕ) : ((-1 : K[X]) ^ j).natDegree = 0 := by
  have h : (-1 : K[X]) = C (-1 : K) := by
    simpa using (map_neg (C : K →+* K[X]) (1 : K)).symm
  rw [h, ← C_pow, natDegree_C]

/-- Row-graded determinant degree bound, by expansion along the first row. -/
theorem natDegree_det_le_sum : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) K[X])
    (d : Fin n → ℕ), (∀ i j, (M i j).natDegree ≤ d i) →
    (Matrix.det M).natDegree ≤ ∑ i, d i
  | 0, M, d, _ => by
      have h1 : Matrix.det M = 1 := Matrix.det_fin_zero
      rw [h1, natDegree_one]
      simp
  | n + 1, M, d, h => by
      classical
      rw [Matrix.det_succ_row_zero]
      refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
      refine Finset.sup_le ?_
      intro j _
      have hsign : (((-1 : K[X]) ^ (j : ℕ)).natDegree) ≤ 0 := by
        rw [natDegree_neg_one_pow]
      have h0 : (M 0 j).natDegree ≤ d 0 := h 0 j
      have hmin : (Matrix.det (M.submatrix Fin.succ (Fin.succAbove j))).natDegree
          ≤ ∑ k : Fin n, d k.succ := by
        refine natDegree_det_le_sum _ _ ?_
        intro i k
        exact h i.succ (Fin.succAbove j k)
      have hsplit : (∑ i : Fin (n + 1), d i) = d 0 + ∑ k : Fin n, d k.succ :=
        Fin.sum_univ_succ d
      calc (((-1 : K[X]) ^ (j : ℕ)) * M 0 j
            * Matrix.det (M.submatrix Fin.succ (Fin.succAbove j))).natDegree
          ≤ (((-1 : K[X]) ^ (j : ℕ)).natDegree)
            + ((M 0 j * Matrix.det (M.submatrix Fin.succ (Fin.succAbove j))).natDegree) := by
            rw [mul_assoc]
            exact Polynomial.natDegree_mul_le
        _ ≤ 0 + (d 0 + ∑ k : Fin n, d k.succ) := by
            have h2 : (M 0 j * Matrix.det (M.submatrix Fin.succ (Fin.succAbove j))).natDegree
                ≤ d 0 + ∑ k : Fin n, d k.succ := by
              calc _ ≤ (M 0 j).natDegree
                    + (Matrix.det (M.submatrix Fin.succ (Fin.succAbove j))).natDegree :=
                      Polynomial.natDegree_mul_le
                _ ≤ d 0 + ∑ k : Fin n, d k.succ := Nat.add_le_add h0 hmin
            omega
        _ = ∑ i, d i := by rw [hsplit]; ring

/-- Determinant degree bound with a uniform degree bound. -/
theorem natDegree_det_le {n : ℕ} (M : Matrix (Fin n) (Fin n) K[X]) (d : ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ d) :
    (Matrix.det M).natDegree ≤ n * d := by
  have := natDegree_det_le_sum M (fun _ => d) (fun i j => h i j)
  simpa [Finset.sum_const, smul_eq_mul] using this

/-- The indicator sum: all rows but one contribute `1`. -/
theorem sum_ite_eq_zero_one {n : ℕ} (j : Fin n) :
    (∑ a : Fin n, (if a = j then (0 : ℕ) else 1)) = n - 1 := by
  classical
  have hmem : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
  have hsplit := (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun a => if a = j then (0 : ℕ) else 1) hmem).symm
  have herase : (∑ a ∈ (Finset.univ.erase j), (if a = j then (0 : ℕ) else 1))
      = (Finset.univ.erase j).card := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℕ)) ?_, Finset.sum_const, smul_eq_mul,
      mul_one]
    intro a ha
    exact if_neg (Finset.mem_erase.mp ha).1
  rw [hsplit, herase]
  simp only [reduceIte]
  rw [Finset.card_erase_of_mem hmem, Finset.card_univ, Fintype.card_fin]
  omega

/-- Adjugate entries of a matrix with linear entries have degree at most 
 - 1. -/
theorem natDegree_adjugate_le {n : ℕ} (M : Matrix (Fin n) (Fin n) K[X])
    (h : ∀ i j, (M i j).natDegree ≤ 1) (i j : Fin n) :
    (Matrix.adjugate M i j).natDegree ≤ n - 1 := by
  classical
  have hmain : ∀ (N : Matrix (Fin n) (Fin n) K[X]),
      (∀ a b, (N a b).natDegree ≤ (if a = j then 0 else 1)) → N.det.natDegree ≤ n - 1 := by
    intro N hN
    refine le_trans (natDegree_det_le_sum N (fun a => if a = j then 0 else 1) hN) ?_
    exact le_of_eq (sum_ite_eq_zero_one j)
  rw [Matrix.adjugate_apply]
  refine hmain _ ?_
  intro a b
  rw [Matrix.updateRow_apply]
  by_cases ha : a = j
  · rw [if_pos ha, if_pos ha, Pi.single_apply]
    split_ifs <;> simp
  · rw [if_neg ha, if_neg ha]
    exact h a b

end Q1Paper
