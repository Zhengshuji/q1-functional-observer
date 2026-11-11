/-
Q1Paper/G3LeftInverse.lean

The rectangular polynomial left inverse of the paper, assembled from the single-block
identity `adjRowInverse_mul` (G3Adjugate) and the degree-bounded Bezout lemma
(G2Assembly).

Given `Q : Matrix (Fin q) (Fin ω) K[X]`, index the minors by row embeddings
`e : Fin ω ↪ Fin q`, put `f_e = det (Q.submatrix e id)` and
`S_e = adj (Q.submatrix e id) * E_e`.  Bezout coefficients `g_e` with
`Σ g_e f_e = 1` give `S = Σ g_e • S_e` with `S * Q = 1`.
-/

import Q1Paper.G3Adjugate
import Q1Paper.G2Assembly
import Q1Paper.DegreeBounds

open Matrix Polynomial

namespace Q1Paper

variable {K : Type*} [Field K] {q ω : ℕ}

/-- The family of minors indexed by row embeddings. -/
noncomputable def minors (Q : Matrix (Fin q) (Fin ω) K[X]) (e : Fin ω ↪ Fin q) : K[X] :=
  Matrix.det (Q.submatrix (e : Fin ω → Fin q) id)

/-- Assembly of the rectangular left inverse from Bezout coefficients. -/
theorem leftInverse_of_bezout {Q : Matrix (Fin q) (Fin ω) K[X]}
    {g : (Fin ω ↪ Fin q) → K[X]}
    (hbez : (∑ e, g e * minors Q e) = 1) :
    (∑ e, g e • adjRowInverse (e : Fin ω → Fin q) Q) * Q = 1 := by
  classical
  calc (∑ e, g e • adjRowInverse (e : Fin ω → Fin q) Q) * Q
      = ∑ e, (g e • adjRowInverse (e : Fin ω → Fin q) Q) * Q := by
        rw [Matrix.sum_mul]
    _ = ∑ e, g e • (adjRowInverse (e : Fin ω → Fin q) Q * Q) := by
        refine Finset.sum_congr rfl ?_
        intro e _
        rw [smul_mul]
    _ = ∑ e, g e • (minors Q e • (1 : Matrix (Fin ω) (Fin ω) K[X])) := by
        refine Finset.sum_congr rfl ?_
        intro e _
        rw [adjRowInverse_mul, minors]
    _ = ∑ e, (g e * minors Q e) • (1 : Matrix (Fin ω) (Fin ω) K[X]) := by
        refine Finset.sum_congr rfl ?_
        intro e _
        rw [smul_smul]
    _ = ((∑ e, g e * minors Q e) • (1 : Matrix (Fin ω) (Fin ω) K[X])) := by
        rw [Finset.sum_smul]
    _ = 1 := by rw [hbez, one_smul]

variable [IsAlgClosed K]

/-- If no maximal minor vanishes identically on a point, the rectangular left inverse
exists (degree hypotheses are those of the Bezout lemma). -/
theorem exists_leftInverse {Q : Matrix (Fin q) (Fin ω) K[X]}
    (hω : 1 ≤ ω)
    (hdeg : ∀ e : Fin ω ↪ Fin q, (minors Q e).natDegree ≤ ω)
    (hminor : ∀ α : K, ∃ e : Fin ω ↪ Fin q, (minors Q e).eval α ≠ 0) :
    ∃ S : Matrix (Fin ω) (Fin q) K[X], S * Q = 1 := by
  classical
  obtain ⟨g, hbez, -⟩ :=
    exists_bezout_family (f := fun e : Fin ω ↪ Fin q => minors Q e) hω hdeg hminor
  exact ⟨_, leftInverse_of_bezout (Q := Q) hbez⟩

/-- Entries of the rectangular left inverse block have degree at most ω - 1. -/
theorem natDegree_adjRowInverse_le {q ω : ℕ} (hω : 1 ≤ ω)
    (Q : Matrix (Fin q) (Fin ω) K[X]) (hlin : ∀ i j, (Q i j).natDegree ≤ 1)
    (e : Fin ω → Fin q) (i : Fin ω) (j : Fin q) :
    (adjRowInverse e Q i j).natDegree ≤ ω - 1 := by
  classical
  rw [adjRowInverse, Matrix.mul_apply]
  refine le_trans (Polynomial.natDegree_sum_le (Finset.univ : Finset (Fin ω)) _) ?_
  refine Finset.sup_le ?_
  intro k _
  calc (Matrix.adjugate (Q.submatrix e id) i k * rowSel e k j).natDegree
      ≤ (Matrix.adjugate (Q.submatrix e id) i k).natDegree + (rowSel (R := K[X]) e k j : K[X]).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ (ω - 1) + 0 := by
        have h1 : (Matrix.adjugate (Q.submatrix e id) i k).natDegree ≤ ω - 1 :=
          natDegree_adjugate_le _ (fun a b => hlin (e a) b) i k
        have h2 : (rowSel (R := K[X]) e k j : K[X]).natDegree = 0 := by
          unfold rowSel
          rw [Matrix.of_apply]
          split_ifs <;> simp
        omega
    _ = ω - 1 := by omega

/-- The assembled rectangular left inverse has degrees at most 2ω - 2. -/
theorem exists_leftInverse_linear {q ω : ℕ} (hω : 1 ≤ ω)
    (Q : Matrix (Fin q) (Fin ω) K[X]) (hlin : ∀ i j, (Q i j).natDegree ≤ 1)
    (hminor : ∀ α : K, ∃ e : Fin ω ↪ Fin q, (minors Q e).eval α ≠ 0) :
    ∃ S : Matrix (Fin ω) (Fin q) K[X],
      S * Q = 1 ∧ ∀ i j, (S i j).natDegree ≤ 2 * ω - 2 := by
  classical
  have hdeg : ∀ e : Fin ω ↪ Fin q, (minors Q e).natDegree ≤ ω := by
    intro e
    have := natDegree_det_le (Q.submatrix (e : Fin ω → Fin q) id) 1
      (fun i j => hlin (e i) j)
    simpa [minors] using this
  obtain ⟨g, hbez, hgdeg⟩ :=
    exists_bezout_family (f := fun e : Fin ω ↪ Fin q => minors Q e) hω hdeg hminor
  refine ⟨∑ e, g e • adjRowInverse (e : Fin ω → Fin q) Q,
    leftInverse_of_bezout (Q := Q) hbez, ?_⟩
  intro i j
  rw [Matrix.sum_apply]
  refine le_trans
    (Polynomial.natDegree_sum_le (Finset.univ : Finset (Fin ω ↪ Fin q)) _) ?_
  refine Finset.sup_le ?_
  intro e _
  have h1 : (g e).natDegree ≤ ω - 1 := by
    have hlt := hgdeg e
    omega
  have h2 : (adjRowInverse (e : Fin ω → Fin q) Q i j).natDegree ≤ ω - 1 :=
    natDegree_adjRowInverse_le hω Q hlin (e : Fin ω → Fin q) i j
  calc (((g e) • adjRowInverse (e : Fin ω → Fin q) Q) i j).natDegree
      = (g e * adjRowInverse (e : Fin ω → Fin q) Q i j).natDegree := by
        rw [Matrix.smul_apply, smul_eq_mul]
    _ ≤ (g e).natDegree + (adjRowInverse (e : Fin ω → Fin q) Q i j).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ (ω - 1) + (ω - 1) := Nat.add_le_add h1 h2
    _ = 2 * ω - 2 := by omega

end Q1Paper
