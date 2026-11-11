/-
Q1Paper/G3Coeff.lean

The coefficient encoding of the polynomial left inverse (G3c, Lemma 6 (iv) ⟺ (v)).

The pencil `Q(λ) = λX − G` is encoded as the matrix `pencil Xm Gm` over `K[X]`, and a
polynomial matrix `S(λ) = Σ_{j≤d} S_j λ^j` as `spoly S`.  The coefficient system (R0) is

  `-S_0 G = 1`,   `S_{j-1} X − S_j G = 0`,   `S_d X = 0`,

and the content of Lemma 6 is that `spoly S * pencil Xm Gm = 1` is equivalent to it.
-/

import Q1Paper.G3LeftInverse

open Matrix Polynomial
open scoped BigOperators

namespace Q1Paper

variable {K : Type*} [Field K] {q ω : ℕ}

/-- The pencil `λX − G` as a matrix over `K[X]`. -/
noncomputable def pencil (Xm Gm : Matrix (Fin q) (Fin ω) K) : Matrix (Fin q) (Fin ω) K[X] :=
  (Polynomial.X : K[X]) • (Xm.map (C : K →+* K[X])) - (Gm.map (C : K →+* K[X]))

/-- The polynomial matrix `Σ_{j≤d} S_j λ^j`. -/
noncomputable def spoly {d : ℕ} (S : Fin (d + 1) → Matrix (Fin ω) (Fin q) K) :
    Matrix (Fin ω) (Fin q) K[X] :=
  ∑ j : Fin (d + 1), (Polynomial.X ^ (j : ℕ) : K[X]) • ((S j).map (C : K →+* K[X]))

/-- Entrywise form of the pencil. -/
theorem pencil_apply (Xm Gm : Matrix (Fin q) (Fin ω) K) (i : Fin q) (j : Fin ω) :
    pencil Xm Gm i j = C (Xm i j) * Polynomial.X - C (Gm i j) := by
  simp [pencil, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, smul_eq_mul]

/-- Product expansion: multiplying the coefficient polynomial matrix by the pencil
gives one power more on the `X` part. -/
theorem spoly_mul_pencil {d : ℕ} (S : Fin (d + 1) → Matrix (Fin ω) (Fin q) K)
    (Xm Gm : Matrix (Fin q) (Fin ω) K) :
    spoly S * pencil Xm Gm
      = (∑ j : Fin (d + 1),
            (Polynomial.X ^ ((j : ℕ) + 1) : K[X]) • ((S j * Xm).map (C : K →+* K[X])))
        - (∑ j : Fin (d + 1),
            (Polynomial.X ^ (j : ℕ) : K[X]) • ((S j * Gm).map (C : K →+* K[X]))) := by
  simp only [spoly, pencil, Matrix.sum_mul, Matrix.mul_sub, Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro j _
    rw [smul_mul, Matrix.mul_smul, smul_smul, ← pow_succ, ← Matrix.map_mul]
  · refine Finset.sum_congr rfl ?_
    intro j _
    rw [smul_mul, ← Matrix.map_mul]

/-- The ω = 1 case of Lemma 6 (v) ⟹ (iv): with d = 0 there are no intermediate
equations, and the two endpoint conditions give S(λ)Q(λ) = 1. -/
theorem spoly_mul_pencil_zero {S : Fin 1 → Matrix (Fin ω) (Fin q) K}
    (Xm Gm : Matrix (Fin q) (Fin ω) K)
    (hX : S 0 * Xm = 0) (hG : S 0 * Gm = -1) :
    spoly (d := 0) S * pencil Xm Gm = 1 := by
  have hsp : spoly (d := 0) S = (S 0).map (C : K →+* K[X]) := by
    simp [spoly, Fin.sum_univ_one]
  rw [hsp, pencil, Matrix.mul_sub, Matrix.mul_smul]
  rw [← Matrix.map_mul, ← Matrix.map_mul, hX, hG]
  simp [Matrix.map_neg, Matrix.map_one, Matrix.map_zero]


/-- Lemma 6 (v) ⟹ (iv): the coefficient system yields the polynomial left inverse. -/
theorem spoly_mul_pencil_eq_one {d : ℕ} (S : Fin (d + 1) → Matrix (Fin ω) (Fin q) K)
    (Xm Gm : Matrix (Fin q) (Fin ω) K)
    (h0 : S 0 * Gm = -1)
    (hj : ∀ j : Fin d, S (Fin.castSucc j) * Xm - S (Fin.succ j) * Gm = 0)
    (hd : S (Fin.last d) * Xm = 0) :
    spoly S * pencil Xm Gm = 1 := by
  rw [spoly_mul_pencil S Xm Gm]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have hmid : (∑ i : Fin d,
        (Polynomial.X ^ ((i.castSucc : ℕ) + 1) : K[X]) •
          ((S i.castSucc * Xm).map (C : K →+* K[X])))
      = (∑ i : Fin d,
        (Polynomial.X ^ (i.succ : ℕ) : K[X]) •
          ((S i.succ * Gm).map (C : K →+* K[X]))) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    have hcast : ((i.castSucc : ℕ) + 1) = (i.succ : ℕ) := by
      rw [Fin.val_castSucc, Fin.val_succ]
    have hAB : S i.castSucc * Xm = S i.succ * Gm := sub_eq_zero.mp (hj i)
    rw [hcast, hAB]
  have hlast : (Polynomial.X ^ ((Fin.last d : ℕ) + 1) : K[X]) •
      ((S (Fin.last d) * Xm).map (C : K →+* K[X])) = 0 := by
    rw [hd]
    simp
  have hg0 : ((S 0 * Gm).map (C : K →+* K[X])) = -1 := by
    rw [h0]
    simp [Matrix.map_neg, Matrix.map_one]
  rw [hmid, hlast]
  simp only [Fin.val_zero, pow_zero, one_smul, hg0]
  abel

/-- The coefficient functional passes through a finite sum. -/
theorem coeff_sum_finset {α : Type*} (s : Finset α) (f : α → K[X]) (k : ℕ) :
    (∑ a ∈ s, f a).coeff k = ∑ a ∈ s, (f a).coeff k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, ih]

/-- Coefficient of a matrix product, entrywise. -/
theorem coeff_mul_apply {ω n p : ℕ} (A : Matrix (Fin ω) (Fin n) K[X])
    (B : Matrix (Fin n) (Fin p) K[X]) (i : Fin ω) (j : Fin p) (k : ℕ) :
    ((A * B) i j).coeff k
      = ∑ a : Fin n, ∑ x ∈ Finset.antidiagonal k,
          (A i a).coeff x.1 * (B a j).coeff x.2 := by
  classical
  rw [Matrix.mul_apply, coeff_sum_finset]
  simp_rw [Polynomial.coeff_mul]

end Q1Paper
