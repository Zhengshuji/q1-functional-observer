
import Q1Paper.PaperI.GramKernel
import Q1Paper.PaperI.Claim11_MinorsGram
/-!
Q1Paper/PaperI/GramCoefficients.lean

Section III-D, layer 3: the coefficient identity.  For a polynomial matrix
`P : Matrix (Fin q) (Fin ℓ) K[X]` whose maximal minors have degree at most `ω`,
the Gram kernel is the coefficient Gram form:

  `K(lam,mu) = ∑_{a,b : Fin (ω+1)} S_{a,b} lam^a mu^b`,

where `S_{a,b} = ∑_i c_{i,a} c_{i,b}` and `c_{i,a}` is the coefficient of `X^a`
in the minor `f_i = maximalMinor P (rowEmb i.1) (colEmb i.2)`.
-/


namespace Q1Paper.PaperI

open Matrix Polynomial

variable {K : Type*} [Field K]

/-- Evaluation of a polynomial of degree at most `ω` as a sum over `Fin (ω+1)`. -/
theorem eval_eq_sum_fin_coeff {p : K[X]} {ω : ℕ} (h : p.natDegree ≤ ω) (x : K) :
    p.eval x = ∑ a : Fin (ω + 1), p.coeff (a : ℕ) * x ^ (a : ℕ) := by
  rw [Polynomial.eval_eq_sum_range' (by omega : p.natDegree < ω + 1)]
  rw [Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [dif_pos (Finset.mem_range.mp hi)]

/-- The coefficient of `X^a` in the minor indexed by `(I, J)`. -/
noncomputable def minorCoeff {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X]) (ω : ℕ)
    (a : ℕ) (I : Set.powersetCard (Fin q) ω) (J : Set.powersetCard (Fin ℓ) ω) : K :=
  (maximalMinor P (rowEmb I) (colEmb J)).coeff a

/-- The coefficient Gram form `S_{a,b} = ∑_i c_{i,a} c_{i,b}`. -/
noncomputable def coeffGram {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X]) (ω : ℕ)
    (a b : ℕ) : K :=
  ∑ I : Set.powersetCard (Fin q) ω, ∑ J : Set.powersetCard (Fin ℓ) ω,
    minorCoeff P ω a I J * minorCoeff P ω b I J

/-- **Coefficient identity.**  The Gram kernel is the coefficient Gram form. -/
theorem gramKernelEval_eq_coeff_sum {q ℓ : ℕ} (ω : ℕ) (P : Matrix (Fin q) (Fin ℓ) K[X])
    (hdeg : ∀ (I : Set.powersetCard (Fin q) ω) (J : Set.powersetCard (Fin ℓ) ω),
      (maximalMinor P (rowEmb I) (colEmb J)).natDegree ≤ ω)
    (lam mu : K) :
    gramKernelEval ω P lam mu =
      ∑ a : Fin (ω + 1), ∑ b : Fin (ω + 1),
        coeffGram P ω (a : ℕ) (b : ℕ) * lam ^ (a : ℕ) * mu ^ (b : ℕ) := by
  classical
  rw [gramKernelEval_eq_double_sum]
  have hprod : ∀ (I : Set.powersetCard (Fin q) ω) (J : Set.powersetCard (Fin ℓ) ω),
      (maximalMinor P (rowEmb I) (colEmb J)).eval lam *
        (maximalMinor P (rowEmb I) (colEmb J)).eval mu
        = ∑ a : Fin (ω + 1), ∑ b : Fin (ω + 1),
            (minorCoeff P ω (a : ℕ) I J * minorCoeff P ω (b : ℕ) I J) *
              lam ^ (a : ℕ) * mu ^ (b : ℕ) := by
    intro I J
    rw [eval_eq_sum_fin_coeff (hdeg I J) lam, eval_eq_sum_fin_coeff (hdeg I J) mu,
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [minorCoeff]
    ring
  simp only [hprod]
  calc ∑ I, ∑ J, ∑ a : Fin (ω + 1), ∑ b : Fin (ω + 1),
          (minorCoeff P ω (a : ℕ) I J * minorCoeff P ω (b : ℕ) I J) *
            lam ^ (a : ℕ) * mu ^ (b : ℕ)
      = ∑ I, ∑ a : Fin (ω + 1), ∑ J, ∑ b : Fin (ω + 1),
          (minorCoeff P ω (a : ℕ) I J * minorCoeff P ω (b : ℕ) I J) *
            lam ^ (a : ℕ) * mu ^ (b : ℕ) := by
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ a : Fin (ω + 1), ∑ I, ∑ J, ∑ b : Fin (ω + 1),
          (minorCoeff P ω (a : ℕ) I J * minorCoeff P ω (b : ℕ) I J) *
            lam ^ (a : ℕ) * mu ^ (b : ℕ) := by
        rw [Finset.sum_comm]
    _ = ∑ a : Fin (ω + 1), ∑ I, ∑ b : Fin (ω + 1), ∑ J,
          (minorCoeff P ω (a : ℕ) I J * minorCoeff P ω (b : ℕ) I J) *
            lam ^ (a : ℕ) * mu ^ (b : ℕ) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ a : Fin (ω + 1), ∑ b : Fin (ω + 1), ∑ I, ∑ J,
          (minorCoeff P ω (a : ℕ) I J * minorCoeff P ω (b : ℕ) I J) *
            lam ^ (a : ℕ) * mu ^ (b : ℕ) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ a : Fin (ω + 1), ∑ b : Fin (ω + 1),
          coeffGram P ω (a : ℕ) (b : ℕ) * lam ^ (a : ℕ) * mu ^ (b : ℕ) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [coeffGram]
        simp only [Finset.sum_mul]

/-- **Coefficient identity for the pencil** λ H - H_A (the degree bound is
supplied by 
atDegree_maximalMinor_le). -/
theorem gramKernelEval_pencil_eq_coeff_sum {K : Type*} [Field K] {q k : ℕ}
    (H HA : Matrix (Fin q) (Fin k) K) {ω : ℕ} (hω : 1 ≤ ω) (lam mu : K) :
    gramKernelEval ω (pencil H HA) lam mu =
      ∑ a : Fin (ω + 1), ∑ b : Fin (ω + 1),
        coeffGram (pencil H HA) ω (a : ℕ) (b : ℕ) * lam ^ (a : ℕ) * mu ^ (b : ℕ) :=
  gramKernelEval_eq_coeff_sum ω (pencil H HA)
    (fun I J => natDegree_maximalMinor_le H HA (rowEmb I) (colEmb J)) lam mu

end Q1Paper.PaperI

