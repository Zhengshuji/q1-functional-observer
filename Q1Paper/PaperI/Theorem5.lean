
import Q1Paper.PaperI.Claim12
import Q1Paper.PaperI.CompressionMatrix
import Q1Paper.PaperI.Claim16
import Q1Paper.BezoutReal
import Q1Paper.G3Coeff

/-!
Q1Paper/PaperI/Theorem5.lean

Formalisation of (part of) Theorem 5 of Paper I, Section `sec:existsr`
(`thm:existsr`): the polynomial system that places `DEC(q)` in the existential
theory of the reals.

## The paper's construction

Fix `q`.  With `N` a basis matrix of `ker [CA; C]`, `H = L N`, `H_A = L A N` and
`ω = rank H`, the paper introduces the blocks

  `X : q × ω`,  `G : q × ω`,  `B : ω × k`,  `X_L : ω × q`,  `B_R : k × ω`,
  `S_j : ω × q`  (`j = 0, …, 2ω-2`),

imposes the polynomial equations

  `H = X B`, `H_A = G B`, `X_L X = 1`, `B B_R = 1`, `S(λ)(λ X - G) = 1`

(the last one expanded by comparing coefficients of `λ^j`, which is the linear
system `(R0)` of the paper), and ties `(H, H_A)` to the input row by row:

  `(B1)`  `X_i B = h_i^0`, `G_i B = g_i^0`                     (`1 ≤ i ≤ r_0`)
  `(B2)`  `(X_i B, G_i B) ∈ T = row [N  AN]`                  (`r_0 < i ≤ q`)

with `h_i^0 = (L_0 N)_i`, `g_i^0 = (L_0 A N)_i`.  The disjunction over
`ω = 0, …, min(q,k)` places `DEC(q)` in `∃ℝ`.

## What this file contains

`encodes` is the system above, stated as a predicate on real matrices, with all
dimensions explicit.  The rows of the observer are indexed by `Fin r₀ ⊕ Fin r`
(so that `q = r₀ + r` and the first `r₀` rows are the prescribed ones); this is
the same index type that `DEC` uses for `L = [L₀; R]`.

Proved here (no `sorry`, no `admit`, no new axioms):

* `rank_mul_rightInverse`, `rank_of_leftInverse` — the two rank facts used by
  both directions of the paper's proof;
* `pencilM`, `spolyM`, `spolyM_mul_pencilM_eq_one`, `pencilM_map_eval`,
  `spolyM_map_eval`, `v_implies_i_self` and their complexified counterparts
  `pencilM_map_eval₂`, `spolyM_map_eval₂`, `v_implies_i_real` — the paper's step
  "comparing coefficients makes the polynomial identity the linear system
  `(R0)`": a real solution of the coefficient system makes `λ X - G` of rank `ω`
  at every real (and, complexified, every complex) parameter;
* `compressedAlgebraic_of_eq_mul`, `compressedSpectral_of_pencil`,
  **`DEC_of_encodes`** — the *soundness* half of Theorem 5: a real solution of
  the system yields a real `R` with `L = [L₀; R]` satisfying `(5a)` and `(5b)`;
* `exists_rowMinor_det_ne_zero`, `exists_coeff_left_inverse_real` and
  **`coeff_iff_spectral`** — the *completeness* half of the `S`-block: for a
  real pencil of rank `ω` at every complex parameter the coefficient system
  `(R0)` has a real solution, and conversely (Bézout/left-inverse construction,
  via `Q1Paper.exists_bezout_family_real`).

## What is *not* formalised

1. The existence of the rank factorization `H = X B` with `B B_R = 1`,
   `X_L X = 1` from `rank H = ω` (a basis/echelon argument).  With it, plus
   `coeff_iff_spectral` and (B1)/(B2), the completeness half of Theorem 5
   follows; see the remark at the end of the file.
2. The complexification of the compressed interface: `DEC` in
   `Q1Paper/PaperI/Interface.lean` is stated for `λ : K`; the paper's `(5b)`
   quantifies over `λ : ℂ`.  `DEC_of_encodes` therefore concludes the real-`λ`
   version `DEC` (over `K = ℝ`), the strongest statement that follows from the
   real interface theorems used here.  The paper's complex convention would
   additionally need "the complexification of a real basis matrix of
   `ker [CA; C]` is a complex basis matrix of `ker [C_ℂ A_ℂ; C_ℂ]`"
   (a rank/dimension count), which is not formalised.
-/


namespace Q1Paper

open Matrix Polynomial

namespace Thm5

/-! ## 0.  The paper's system as a predicate on real matrices -/

/-- **The paper's system `Φ_ω`** (Section `sec:existsr` of Paper I), as a
predicate on real matrices.

`C`, `A`, `L₀` are the input, `N` is a basis matrix of `ker [CA; C]`; the row
type `Fin r₀ ⊕ Fin r` is the paper's `q = r₀ + r` rows of the observer
`L = [L₀; R]`, split into the `r₀` prescribed rows (`Sum.inl`) and the `r`
free rows (`Sum.inr`).  The blocks are

  `X G : (r₀ ⊕ r) × ω`,  `B : ω × k`,  `X_L : ω × (r₀ ⊕ r)`,
  `B_R : k × ω`,  `S_j : ω × (r₀ ⊕ r)`,

and the components of the conjunction are, in order:

* `X_L X = 1`  and  `B B_R = 1` (the two rank conditions);
* the coefficient form of `S(λ)(λ X - G) = 1`, i.e. `S₀ G = -1`,
  `S_{j} X - S_{j+1} G = 0`, `S_{2ω-2} X = 0`;
* the equations `H = X B` and `H_A = G B` are not separate conjuncts: `X B`
  and `G B` *are* the compressed blocks.  The rows are tied to the input by
  `(B1)`: for `i : Fin r₀` the `i`-th rows of `X B` and `G B` are those of
  `L₀ N` and `L₀ A N`;
* `(B2)`: for a free row `i : Fin r`, the pair `(X_i B, G_i B)` is a real
  combination of the rows of `[N  AN]`, i.e. it lies in `T = row [N  AN]`.
  (The paper writes this as `D [(X_iB)ᵀ; (G_iB)ᵀ] = 0` with `ker D = T`; the
  "∃ preimage" form used here is the same condition, with the preimage `r_i`
  exhibited, and is what the soundness proof consumes.) -/
def encodes {p r0 r n k ω : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (X G : Matrix (Fin r0 ⊕ Fin r) (Fin ω) ℝ) (B : Matrix (Fin ω) (Fin k) ℝ)
    (XL : Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ) (BR : Matrix (Fin k) (Fin ω) ℝ)
    (S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ) : Prop :=
  XL * X = 1 ∧
  B * BR = 1 ∧
  S 0 * G = -1 ∧
  (∀ j : Fin (2 * ω - 2), S (Fin.castSucc j) * X - S (Fin.succ j) * G = 0) ∧
  S (Fin.last (2 * ω - 2)) * X = 0 ∧
  (∀ i : Fin r0, (X * B) (Sum.inl i) = (L0 * N) i ∧
                 (G * B) (Sum.inl i) = (L0 * A * N) i) ∧
  (∀ i : Fin r, ∃ ri : Fin n → ℝ,
      Matrix.vecMul ri N = (X * B) (Sum.inr i) ∧
      Matrix.vecMul ri (A * N) = (G * B) (Sum.inr i))

/-! ## 1.  Rank lemmas -/

/-- Multiplying by a matrix with a right inverse does not change the rank. -/
theorem rank_mul_rightInverse {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq n] (P : Matrix m n ℝ) (Q : Matrix n p ℝ) (Q' : Matrix p n ℝ)
    (h : Q * Q' = 1) : (P * Q).rank = P.rank := by
  have hle : (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
  have hge : P.rank ≤ (P * Q).rank := by
    have h1 : P * Q * Q' = P := by rw [Matrix.mul_assoc, h, Matrix.mul_one]
    calc P.rank = (P * Q * Q').rank := by rw [h1]
      _ ≤ (P * Q).rank := Matrix.rank_mul_le_left (P * Q) Q'
  exact le_antisymm hle hge

/-- A matrix with a left inverse has full column rank. -/
theorem rank_of_leftInverse {ι : Type*} [Fintype ι] {ω : ℕ}
    (X : Matrix ι (Fin ω) ℝ) (XL : Matrix (Fin ω) ι ℝ) (h : XL * X = 1) :
    X.rank = ω := by
  have h1 : ω ≤ X.rank := by
    have h2 : (1 : Matrix (Fin ω) (Fin ω) ℝ).rank ≤ X.rank := by
      rw [← h]
      exact Matrix.rank_mul_le_right XL X
    rwa [Matrix.rank_one, Fintype.card_fin] at h2
  have h3 : X.rank ≤ ω := by
    simpa using Matrix.rank_le_card_width X
  omega

/-! ## 2.  The pencil `λ X - G` for an arbitrary row index type, and the
coefficient system `(R0)` -/

section Pencil

variable {K : Type*} [Field K]

/-- The pencil `λ X - G` as a matrix over `K[X]`, for an arbitrary row index
type.  (Same definition as `Q1Paper.pencil`, which is stated for `Fin q` rows.) -/
noncomputable def pencilM {ι : Type*} {k : ℕ} (X G : Matrix ι (Fin k) K) :
    Matrix ι (Fin k) K[X] :=
  (Polynomial.X : K[X]) • (X.map (Polynomial.C : K →+* K[X]))
    - (G.map (Polynomial.C : K →+* K[X]))

/-- The polynomial matrix `Σ_{j≤d} S_j λ^j`. -/
noncomputable def spolyM {ι : Type*} {k : ℕ} {d : ℕ}
    (S : Fin (d + 1) → Matrix (Fin k) ι K) : Matrix (Fin k) ι K[X] :=
  ∑ j : Fin (d + 1), (Polynomial.X ^ (j : ℕ) : K[X])
    • ((S j).map (Polynomial.C : K →+* K[X]))

/-- Entrywise form of the pencil. -/
theorem pencilM_apply {ι : Type*} {k : ℕ} (X G : Matrix ι (Fin k) K) (i : ι) (j : Fin k) :
    pencilM X G i j = Polynomial.C (X i j) * Polynomial.X - Polynomial.C (G i j) := by
  simp [pencilM, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, smul_eq_mul]

/-- Multiplying the coefficient polynomial matrix by the pencil gives one power
more on the `X` part. -/
theorem spolyM_mul_pencilM {ι : Type*} [Fintype ι] {k : ℕ} {d : ℕ}
    (S : Fin (d + 1) → Matrix (Fin k) ι K) (X G : Matrix ι (Fin k) K) :
    spolyM S * pencilM X G
      = (∑ j : Fin (d + 1), (Polynomial.X ^ ((j : ℕ) + 1) : K[X])
            • ((S j * X).map (Polynomial.C : K →+* K[X])))
        - (∑ j : Fin (d + 1), (Polynomial.X ^ (j : ℕ) : K[X])
            • ((S j * G).map (Polynomial.C : K →+* K[X]))) := by
  simp only [spolyM, pencilM, Matrix.sum_mul, Matrix.mul_sub, Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro j _
    rw [smul_mul, Matrix.mul_smul, smul_smul, ← pow_succ, ← Matrix.map_mul]
  · refine Finset.sum_congr rfl ?_
    intro j _
    rw [smul_mul, ← Matrix.map_mul]

/-- **(R0) ⟹ the polynomial identity** `S(λ)(λX - G) = 1`. -/
theorem spolyM_mul_pencilM_eq_one {ι : Type*} [Fintype ι] {k : ℕ} {d : ℕ}
    (S : Fin (d + 1) → Matrix (Fin k) ι K) (X G : Matrix ι (Fin k) K)
    (h0 : S 0 * G = -1)
    (hj : ∀ j : Fin d, S (Fin.castSucc j) * X - S (Fin.succ j) * G = 0)
    (hd : S (Fin.last d) * X = 0) :
    spolyM S * pencilM X G = 1 := by
  rw [spolyM_mul_pencilM S X G]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have hmid : (∑ i : Fin d,
        (Polynomial.X ^ ((i.castSucc : ℕ) + 1) : K[X])
          • ((S i.castSucc * X).map (Polynomial.C : K →+* K[X])))
      = (∑ i : Fin d, (Polynomial.X ^ (i.succ : ℕ) : K[X])
          • ((S i.succ * G).map (Polynomial.C : K →+* K[X]))) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    have hcast : ((i.castSucc : ℕ) + 1) = (i.succ : ℕ) := by
      rw [Fin.val_castSucc, Fin.val_succ]
    have hAB : S i.castSucc * X = S i.succ * G := sub_eq_zero.mp (hj i)
    rw [hcast, hAB]
  have hlast : (Polynomial.X ^ ((Fin.last d : ℕ) + 1) : K[X])
      • ((S (Fin.last d) * X).map (Polynomial.C : K →+* K[X])) = 0 := by
    rw [hd]
    simp
  have hg0 : ((S 0 * G).map (Polynomial.C : K →+* K[X])) = -1 := by
    rw [h0]
    simp [Matrix.map_neg, Matrix.map_one]
  rw [hmid, hlast]
  simp only [Fin.val_zero, pow_zero, one_smul, hg0]
  abel

/-- Evaluating the pencil at a point of the base field. -/
theorem pencilM_map_eval {ι : Type*} {k : ℕ} (X G : Matrix ι (Fin k) K) (z : K) :
    (pencilM X G).map (Polynomial.eval z) = z • X - G := by
  ext i j
  simp only [Matrix.map_apply, pencilM_apply, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Evaluating the polynomial matrix `Σ_j λ^j S_j` at a point of the base field. -/
theorem spolyM_map_eval {ι : Type*} {k : ℕ} {d : ℕ}
    (S : Fin (d + 1) → Matrix (Fin k) ι K) (z : K) :
    (spolyM S).map (Polynomial.eval z) = ∑ j : Fin (d + 1), (z ^ (j : ℕ)) • S j := by
  classical
  ext i j
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    spolyM, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro c _
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]

/-- Evaluation at a point of the base field is multiplicative on matrix products. -/
theorem map_mul_eval {m n p : Type*} [Fintype n] (z : K)
    (A : Matrix m n K[X]) (Bm : Matrix n p K[X]) :
    (A * Bm).map (Polynomial.eval z)
      = A.map (Polynomial.eval z) * Bm.map (Polynomial.eval z) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul]

/-- Evaluation at a point of the base field sends `1` to `1`. -/
theorem map_one_eval {n : Type*} [Fintype n] [DecidableEq n] (z : K) :
    (1 : Matrix n n K[X]).map (Polynomial.eval z) = (1 : Matrix n n K) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

end Pencil

/-- Evaluating the complexified pencil at `z : ℂ`. -/
theorem pencilM_map_eval₂ {ι : Type*} {k : ℕ} (X G : Matrix ι (Fin k) ℝ) (z : ℂ) :
    (pencilM X G).map (Polynomial.eval₂ (algebraMap ℝ ℂ) z)
      = z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ) := by
  ext i j
  simp only [Matrix.map_apply, pencilM_apply, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Evaluating the polynomial matrix `Σ_j λ^j S_j` at `z : ℂ`. -/
theorem spolyM_map_eval₂ {ι : Type*} {k : ℕ} {d : ℕ}
    (S : Fin (d + 1) → Matrix (Fin k) ι ℝ) (z : ℂ) :
    (spolyM S).map (Polynomial.eval₂ (algebraMap ℝ ℂ) z)
      = ∑ j : Fin (d + 1), (z ^ (j : ℕ)) • (S j).map (algebraMap ℝ ℂ) := by
  classical
  ext i j
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    spolyM, Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro c _
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]

/-- Evaluation at `z : ℂ` is multiplicative on matrix products. -/
theorem map_mul_eval₂_real {m n p : Type*} [Fintype n] (z : ℂ)
    (A : Matrix m n ℝ[X]) (Bm : Matrix n p ℝ[X]) :
    (A * Bm).map (Polynomial.eval₂ (algebraMap ℝ ℂ) z)
      = A.map (Polynomial.eval₂ (algebraMap ℝ ℂ) z)
        * Bm.map (Polynomial.eval₂ (algebraMap ℝ ℂ) z) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul]

/-- Evaluation at `z : ℂ` sends the identity matrix to the identity matrix. -/
theorem map_one_eval₂_real {n : Type*} [Fintype n] [DecidableEq n] (z : ℂ) :
    (1 : Matrix n n ℝ[X]).map (Polynomial.eval₂ (algebraMap ℝ ℂ) z) = (1 : Matrix n n ℂ) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp [Polynomial.eval₂_one, Polynomial.eval₂_zero]

/-- **(R0) ⟹ (5b)**, real-parameter form: a real solution of the coefficient
system makes `λ X - G` of rank `k` at every real `λ`. -/
theorem v_implies_i_self {ι : Type*} [Fintype ι] {k : ℕ}
    (X G : Matrix ι (Fin k) ℝ)
    (S : Fin (2 * k - 2 + 1) → Matrix (Fin k) ι ℝ)
    (h0 : S 0 * G = -1)
    (hj : ∀ j : Fin (2 * k - 2), S (Fin.castSucc j) * X - S (Fin.succ j) * G = 0)
    (hd : S (Fin.last (2 * k - 2)) * X = 0) :
    ∀ lam : ℝ, (lam • X - G).rank = k := by
  have hm : spolyM S * pencilM X G = 1 := spolyM_mul_pencilM_eq_one S X G h0 hj hd
  intro lam
  have h1 : (∑ j : Fin (2 * k - 2 + 1), (lam ^ (j : ℕ)) • S j) * (lam • X - G) = 1 := by
    have h := congrArg (fun N : Matrix (Fin k) (Fin k) ℝ[X] => N.map (Polynomial.eval lam)) hm
    rw [map_mul_eval, map_one_eval, spolyM_map_eval, pencilM_map_eval] at h
    exact h
  have hle : k ≤ (lam • X - G).rank := by
    have h2 : (1 : Matrix (Fin k) (Fin k) ℝ).rank ≤ (lam • X - G).rank := by
      rw [← h1]
      exact Matrix.rank_mul_le_right _ _
    rwa [Matrix.rank_one, Fintype.card_fin] at h2
  have hge : (lam • X - G).rank ≤ k := by
    simpa using Matrix.rank_le_card_width (lam • X - G)
  omega

/-- **(R0) ⟹ (5b)**, complex-parameter form: a real solution of the
coefficient system makes `λ X - G` of rank `k` at every complex `λ`. -/
theorem v_implies_i_real {ι : Type*} [Fintype ι] {k : ℕ}
    (X G : Matrix ι (Fin k) ℝ)
    (S : Fin (2 * k - 2 + 1) → Matrix (Fin k) ι ℝ)
    (h0 : S 0 * G = -1)
    (hj : ∀ j : Fin (2 * k - 2), S (Fin.castSucc j) * X - S (Fin.succ j) * G = 0)
    (hd : S (Fin.last (2 * k - 2)) * X = 0) :
    ∀ z : ℂ, (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)).rank = k := by
  have hm : spolyM S * pencilM X G = 1 := spolyM_mul_pencilM_eq_one S X G h0 hj hd
  intro z
  have h1 : (∑ j : Fin (2 * k - 2 + 1), (z ^ (j : ℕ)) • (S j).map (algebraMap ℝ ℂ))
      * (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)) = 1 := by
    have h := congrArg (fun N : Matrix (Fin k) (Fin k) ℝ[X] =>
      N.map (Polynomial.eval₂ (algebraMap ℝ ℂ) z)) hm
    rw [map_mul_eval₂_real, map_one_eval₂_real, spolyM_map_eval₂,
      pencilM_map_eval₂] at h
    exact h
  have hle : k ≤ (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)).rank := by
    have h2 : (1 : Matrix (Fin k) (Fin k) ℂ).rank
        ≤ (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)).rank := by
      rw [← h1]
      exact Matrix.rank_mul_le_right _ _
    rwa [Matrix.rank_one, Fintype.card_fin] at h2
  have hge : (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)).rank ≤ k := by
    simpa using Matrix.rank_le_card_width (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ))
  omega

/-! ## 3.  Soundness: a real solution of the system implies `DEC(q)` -/

/-- `(5a)` in compressed form follows from a factorisation `H_A = F H`. -/
theorem compressedAlgebraic_of_eq_mul {q k : Type*} [Fintype q] [Fintype k]
    (H HA : Matrix q k ℝ) (F : Matrix q q ℝ) (h : HA = F * H) :
    PaperI.compressedAlgebraic H HA := by
  have hmem : ∀ i, (F * H) i ∈ Q1Subspace.rowSpace H := by
    intro i
    have hsum : (F * H) i = ∑ j, F i j • H j := by
      ext jj
      simp [Matrix.mul_apply, Finset.sum_apply, smul_eq_mul]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hrow : Q1Subspace.rowSpace HA ≤ Q1Subspace.rowSpace H := by
    rw [h]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hmem i
  exact (Q1Subspace.rank_fromRows_eq_rank_iff HA H).mpr hrow

/-- Multiplying `[L₀; R]` on the right: `[L₀; R] * N = [L₀ N; R N]`. -/
theorem fromRows_mul {m₁ m₂ n p : Type*} [Fintype n]
    (A : Matrix m₁ n ℝ) (Bm : Matrix m₂ n ℝ) (N : Matrix n p ℝ) :
    Matrix.fromRows A Bm * N = Matrix.fromRows (A * N) (Bm * N) := by
  ext i j
  cases i <;> simp [Matrix.mul_apply]

/-- The `Sum.inl` row of `[L₀; R] * N`. -/
theorem fromRows_mul_row_inl {m₁ m₂ n p : Type*} [Fintype n]
    (A : Matrix m₁ n ℝ) (Bm : Matrix m₂ n ℝ) (N : Matrix n p ℝ) (i : m₁) :
    (Matrix.fromRows A Bm * N) (Sum.inl i) = (A * N) i := by
  rw [fromRows_mul]
  rfl

/-- The `Sum.inr` row of `[L₀; R] * N`. -/
theorem fromRows_mul_row_inr {m₁ m₂ n p : Type*} [Fintype n]
    (A : Matrix m₁ n ℝ) (Bm : Matrix m₂ n ℝ) (N : Matrix n p ℝ) (i : m₂) :
    (Matrix.fromRows A Bm * N) (Sum.inr i) = (Bm * N) i := by
  rw [fromRows_mul]
  rfl

/-- **(5b) in compressed form** for a pair `(X B, G B)` whose pencil has rank
`ω` at every real `λ`: right multiplication by the right-invertible `B`
preserves both ranks. -/
theorem compressedSpectral_of_pencil {ι : Type*} [Fintype ι] {k ω : ℕ}
    (X G : Matrix ι (Fin ω) ℝ) (B : Matrix (Fin ω) (Fin k) ℝ)
    (BR : Matrix (Fin k) (Fin ω) ℝ) (hBR : B * BR = 1) (hX : X.rank = ω)
    (hpen : ∀ lam : ℝ, (lam • X - G).rank = ω) :
    PaperI.compressedSpectral (X * B) (G * B) := by
  intro lam
  have hpencil : (lam • X - G).rank = ω := hpen lam
  have hH : (X * B).rank = ω := by
    rw [rank_mul_rightInverse X B BR hBR, hX]
  calc (lam • (X * B) - G * B).rank = ((lam • X - G) * B).rank := by
        rw [Matrix.sub_mul, Matrix.smul_mul]
    _ = (lam • X - G).rank := rank_mul_rightInverse (lam • X - G) B BR hBR
    _ = ω := hpencil
    _ = (X * B).rank := hH.symm

/-- **Soundness of the encoding** (the easy half of Theorem 5 of Paper I).

If the paper's system `Φ_ω` has a real solution for the input `(C, A, L₀)` and
the kernel basis `N`, then `DEC(q)` holds: with `R` read off row by row from
`(B2)` and `L = [L₀; R]`, one has `L N = X B` and `L A N = G B`, so `(5a)`
follows from `H_A = G B = (G X_L)(X B)` and `(5b)` from the coefficient system
together with `B B_R = 1`. -/
theorem DEC_of_encodes {p r0 r n k ω : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (hN : N.mulVecLin.range = (Matrix.fromRows (C * A) C).mulVecLin.ker)
    (X G : Matrix (Fin r0 ⊕ Fin r) (Fin ω) ℝ) (B : Matrix (Fin ω) (Fin k) ℝ)
    (XL : Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ) (BR : Matrix (Fin k) (Fin ω) ℝ)
    (S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ)
    (henc : encodes C A L0 N X G B XL BR S) :
    PaperI.DEC C A L0 r := by
  obtain ⟨hXL, hBR, hS0, hSj, hSd, hB1, hB2⟩ := henc
  choose R hR using hB2
  let Rm : Matrix (Fin r) (Fin n) ℝ := R
  set L : Matrix (Fin r0 ⊕ Fin r) (Fin n) ℝ := Matrix.fromRows L0 Rm with hL
  have hLN : L * N = X * B := by
    ext i kk
    cases i with
    | inl i =>
        rw [hL, fromRows_mul_row_inl]
        exact (congrFun (hB1 i).1 kk).symm
    | inr i =>
        rw [hL, fromRows_mul_row_inr]
        have h := congrFun (hR i).1 kk
        simpa [Matrix.vecMul, dotProduct, Matrix.mul_apply] using h
  have hLAN : L * A * N = G * B := by
    have hLA : L * A = Matrix.fromRows (L0 * A) (Rm * A) := by
      rw [hL, fromRows_mul]
    ext i kk
    cases i with
    | inl i =>
        rw [hLA, fromRows_mul_row_inl]
        exact (congrFun (hB1 i).2 kk).symm
    | inr i =>
        rw [hLA, fromRows_mul_row_inr, Matrix.mul_assoc]
        have h := congrFun (hR i).2 kk
        simpa [Matrix.vecMul, dotProduct, Matrix.mul_apply] using h
  have hXrank : X.rank = ω := rank_of_leftInverse X XL hXL
  have hpen : ∀ lam : ℝ, (lam • X - G).rank = ω :=
    v_implies_i_self X G S hS0 hSj hSd
  have hfac : (G * XL) * (X * B) = G * B := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc XL X B, hXL, Matrix.one_mul]
  refine (PaperI.DEC_iff_compressed C A L0 r N hN).mpr ⟨Rm, ?_, ?_⟩
  · show PaperI.compressedAlgebraic (L * N) (L * A * N)
    rw [hLN, hLAN]
    exact compressedAlgebraic_of_eq_mul (H := X * B) (HA := G * B) (F := G * XL) hfac.symm
  · show PaperI.compressedSpectral (L * N) (L * A * N)
    rw [hLN, hLAN]
    exact compressedSpectral_of_pencil X G B BR hBR hXrank hpen

/-! ## 4.  Completeness of the `S`-block -/

/-- A real `q × ω` matrix of rank `ω` has an invertible `ω × ω` column
submatrix; in fact a set of `ω` linearly independent rows already gives a
nonzero determinant, since the matrix has exactly `ω` columns. -/
theorem exists_rowMinor_det_ne_zero {K : Type*} [Field K] {ι : Type*} [Fintype ι] {ω : ℕ}
    (M : Matrix ι (Fin ω) K) (h : M.rank = ω) :
    ∃ ρ : Fin ω → ι, Function.Injective ρ ∧ (M.submatrix ρ id).det ≠ 0 := by
  classical
  have hrank : Module.finrank K ↥(Q1Subspace.rowSpace M) = ω := by
    rw [← Q1Subspace.rank_eq_finrank_rowSpace]
    exact h
  obtain ⟨ρ, hρ, hLI⟩ := PaperI.exists_injective_linearIndependent (v := M.row) hrank
  refine ⟨ρ, hρ, ?_⟩
  have hrow : LinearIndependent K (M.submatrix ρ id).row := by
    have h1 : (M.submatrix ρ id).row = M.row ∘ ρ := by
      funext i j
      rfl
    rw [h1]
    exact hLI
  have hcol : (M.submatrix ρ id)ᵀ.col = (M.submatrix ρ id).row := by
    funext i j
    rfl
  have hLI' : LinearIndependent K ((M.submatrix ρ id)ᵀ.col) := by
    rw [hcol]
    exact hrow
  have hns : (M.submatrix ρ id)ᵀ.Nonsingular := Matrix.linearIndependent_col_iff.mp hLI'
  have hdet : (M.submatrix ρ id)ᵀ.det ≠ 0 := Matrix.nonsingular_iff_det_ne_zero.mp hns
  rwa [Matrix.det_transpose] at hdet

/-- Step 1 of the completeness of the `S`-block: if the pencil `λ X - G` has
rank `ω` at every complex `λ`, then its maximal minors have no common complex
root. -/
theorem no_common_root_of_spectral {q ω : ℕ}
    (X G : Matrix (Fin q) (Fin ω) ℝ)
    (hspec : ∀ z : ℂ, (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)).rank = ω) :
    ∀ z : ℂ, ∃ e : Fin ω ↪ Fin q,
      (Q1Paper.complexify (Q1Paper.minors (PaperI.pencil X G) e)).eval z ≠ 0 := by
  classical
  intro z
  have hMz : (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)).rank = ω := hspec z
  obtain ⟨ρ, hρ, hdet⟩ :=
    exists_rowMinor_det_ne_zero
      (M := z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)) (ω := ω) hMz
  refine ⟨⟨ρ, hρ⟩, ?_⟩
  have h1 : PaperI.maximalMinor
        (PaperI.pencil (X.map (algebraMap ℝ ℂ)) (G.map (algebraMap ℝ ℂ))) ρ id
      = Q1Paper.complexify (Q1Paper.minors (PaperI.pencil X G) ⟨ρ, hρ⟩) := by
    have hp : PaperI.pencil (X.map (algebraMap ℝ ℂ)) (G.map (algebraMap ℝ ℂ))
        = (PaperI.pencil X G).map (Polynomial.map (algebraMap ℝ ℂ)) := by
      ext i j
      simp [PaperI.pencil, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C,
        Polynomial.map_X]
    rw [hp]
    exact PaperI.maximalMinor_map (PaperI.pencil X G) ρ id (algebraMap ℝ ℂ)
  have h2 : (PaperI.maximalMinor
        (PaperI.pencil (X.map (algebraMap ℝ ℂ)) (G.map (algebraMap ℝ ℂ))) ρ id).eval z
      = ((z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)).submatrix ρ id).det := by
    rw [PaperI.eval_maximalMinor, PaperI.pencil_map_eval]
  rw [h1] at h2
  rw [h2]
  exact hdet

/-- The two pencil encodings used in the project agree:
`Q1Paper.pencil` (a matrix over `K[X]` built with `smul`/`map`) and
`PaperI.pencil` (the entrywise form). -/
theorem pencilI_eq_pencilQ {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℝ) :
    (Q1Paper.pencil X G : Matrix (Fin q) (Fin ω) ℝ[X]) = PaperI.pencil X G := by
  ext i j
  rw [Q1Paper.pencil_apply]
  rfl

/-- The entries of `Q1Paper.pencil` have degree at most one. -/
theorem pencilQ_natDegree_le {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℝ)
    (i : Fin q) (j : Fin ω) :
    ((Q1Paper.pencil X G : Matrix (Fin q) (Fin ω) ℝ[X]) i j).natDegree ≤ 1 := by
  rw [Q1Paper.pencil_apply]
  refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
  rw [max_le_iff]
  constructor
  · refine le_trans (Polynomial.natDegree_mul_le) ?_
    simp
  · simp

set_option maxHeartbeats 1000000 in
/-- Step 2 of the completeness of the `S`-block: a Bézout family of the maximal
minors with degrees `< ω` assembles into the coefficient system `(R0)`. -/
theorem exists_coeff_of_no_common_root {q ω : ℕ} (hω : 1 ≤ ω)
    (X G : Matrix (Fin q) (Fin ω) ℝ)
    (hroot : ∀ z : ℂ, ∃ e : Fin ω ↪ Fin q,
      (Q1Paper.complexify (Q1Paper.minors (Q1Paper.pencil X G) e)).eval z ≠ 0) :
    ∃ S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin q) ℝ,
      S 0 * G = -1 ∧
      (∀ j : Fin (2 * ω - 2), S (Fin.castSucc j) * X - S (Fin.succ j) * G = 0) ∧
      S (Fin.last (2 * ω - 2)) * X = 0 := by
  classical
  set Q : Matrix (Fin q) (Fin ω) ℝ[X] := (Q1Paper.pencil X G : Matrix (Fin q) (Fin ω) ℝ[X])
    with hQ
  have hdegM : ∀ e : Fin ω ↪ Fin q,
      (PaperI.maximalMinor Q (e : Fin ω → Fin q) id).natDegree ≤ ω := by
    intro e
    have h := PaperI.natDegree_det_le (Q.submatrix (e : Fin ω → Fin q) id)
      (d := 1) (fun i j => pencilQ_natDegree_le X G (e i) j)
    have h2 : (Q.submatrix (e : Fin ω → Fin q) id).det.natDegree ≤ ω := by
      simpa using h
    exact h2
  have hdeg : ∀ e : Fin ω ↪ Fin q, (Q1Paper.minors Q e).natDegree ≤ ω :=
    fun e => hdegM e
  obtain ⟨g, hbez, hgdeg⟩ :=
    Q1Paper.exists_bezout_family_real
      (f := fun e : Fin ω ↪ Fin q => Q1Paper.minors Q e) hω hdeg hroot
  let Sbig : Matrix (Fin ω) (Fin q) ℝ[X] :=
    ∑ e : Fin ω ↪ Fin q, g e • Q1Paper.adjRowInverse (e : Fin ω → Fin q) Q
  have hmul : Sbig * Q = 1 := Q1Paper.leftInverse_of_bezout (Q := Q) hbez
  have hdegS : ∀ i j, (Sbig i j).natDegree ≤ 2 * ω - 2 := by
    intro i j
    have h0 : Sbig i j
        = ∑ e : Fin ω ↪ Fin q,
            (g e • Q1Paper.adjRowInverse (e : Fin ω → Fin q) Q) i j := by
      show (∑ e : Fin ω ↪ Fin q, g e • Q1Paper.adjRowInverse (e : Fin ω → Fin q) Q) i j
        = ∑ e : Fin ω ↪ Fin q,
            (g e • Q1Paper.adjRowInverse (e : Fin ω → Fin q) Q) i j
      rw [Matrix.sum_apply]
    rw [h0]
    refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
    refine Finset.sup_le ?_
    intro e _
    have h1 : (g e).natDegree ≤ ω - 1 := by
      have := hgdeg e
      omega
    have h2 : (Q1Paper.adjRowInverse (e : Fin ω → Fin q) Q i j).natDegree ≤ ω - 1 :=
      Q1Paper.natDegree_adjRowInverse_le hω Q
        (fun a b => pencilQ_natDegree_le X G a b) (e : Fin ω → Fin q) i j
    calc ((g e • Q1Paper.adjRowInverse (e : Fin ω → Fin q) Q) i j).natDegree
        = (g e * Q1Paper.adjRowInverse (e : Fin ω → Fin q) Q i j).natDegree := by
          rw [Matrix.smul_apply, smul_eq_mul]
      _ ≤ (g e).natDegree + (Q1Paper.adjRowInverse (e : Fin ω → Fin q) Q i j).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ (ω - 1) + (ω - 1) := Nat.add_le_add h1 h2
      _ = 2 * ω - 2 := by omega
  exact Q1Paper.iv_implies_v X G Sbig hmul hdegS

/-- **Completeness of the `S`-block.**  Let `X, G` be real `q × ω` matrices and
suppose `rank(λ X - G) = ω` for every complex `λ`.  Then there are real matrices
`S_0, …, S_{2ω-2} : ω × q` satisfying the coefficient system `(R0)` of the
paper.

The proof is the paper's: by Claim 11 (`no_common_root_of_spectral`, which uses
`exists_rowMinor_det_ne_zero`) the maximal minors of the pencil have no common
complex root, Claim 9 (`exists_bezout_family_real`) supplies a Bézout family of
degree `< ω` over `ℝ`, and the adjugate assembly (`leftInverse_of_bezout`)
produces a polynomial left inverse of degree `≤ 2ω-2`, whose coefficients are
the `S_j` (`iv_implies_v`). -/
theorem exists_coeff_left_inverse_real {q ω : ℕ} (hω : 1 ≤ ω)
    (X G : Matrix (Fin q) (Fin ω) ℝ) (_hXr : X.rank = ω)
    (hspec : ∀ z : ℂ, (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)).rank = ω) :
    ∃ S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin q) ℝ,
      S 0 * G = -1 ∧
      (∀ j : Fin (2 * ω - 2), S (Fin.castSucc j) * X - S (Fin.succ j) * G = 0) ∧
      S (Fin.last (2 * ω - 2)) * X = 0 := by
  have hrootQ : ∀ z : ℂ, ∃ e : Fin ω ↪ Fin q,
      (Q1Paper.complexify (Q1Paper.minors (Q1Paper.pencil X G) e)).eval z ≠ 0 := by
    intro z
    obtain ⟨e, he⟩ := no_common_root_of_spectral X G hspec z
    refine ⟨e, ?_⟩
    have heq : Q1Paper.minors (Q1Paper.pencil X G) e
        = Q1Paper.minors (PaperI.pencil X G) e := by
      rw [pencilI_eq_pencilQ]
    rw [heq]
    exact he
  exact exists_coeff_of_no_common_root hω X G hrootQ

/-- **The `S`-block is exactly `(5b)` for the pencil.**  For a real pencil
`λ X - G` with `X` of full column rank `ω ≥ 1`, the coefficient system `(R0)`
of the paper is solvable in real matrices if and only if `rank(λ X - G) = ω`
for every complex `λ`.

(⟹ is `v_implies_i_real`, ⟸ is `exists_coeff_left_inverse_real`.) -/
theorem coeff_iff_spectral {q ω : ℕ} (hω : 1 ≤ ω) (X G : Matrix (Fin q) (Fin ω) ℝ)
    (hXr : X.rank = ω) :
    (∃ S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin q) ℝ,
        S 0 * G = -1 ∧
        (∀ j : Fin (2 * ω - 2), S (Fin.castSucc j) * X - S (Fin.succ j) * G = 0) ∧
        S (Fin.last (2 * ω - 2)) * X = 0) ↔
      ∀ z : ℂ, (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)).rank = ω := by
  constructor
  · rintro ⟨S, h0, hj, hd⟩
    exact v_implies_i_real X G S h0 hj hd
  · intro h
    exact exists_coeff_left_inverse_real hω X G hXr h

/-! ## 5.  How the two halves fit together

`DEC_of_encodes` is the soundness half of Theorem 5.  For the completeness half,
given `R` with `(5a)` and `(5b)` (i.e. `compressedAlgebraic` and
`compressedSpectral` for `H = L N`, `H_A = L A N`), the paper

1. takes a rank factorization `H = X B` with `B B_R = 1` and `X_L X = 1`,
2. sets `G = F X` where `H_A = F H` (which exists by `(5a)`, cf.
   `PaperI.exists_factor_of_rawAlgebraic`),
3. obtains `S` from `(5b)` for the pair `(X, G)` via `coeff_iff_spectral`,
4. checks `(B1)` and `(B2)` by construction.

Step 3 is `coeff_iff_spectral` above, together with the transfer of `(5b)` from
`(H, H_A)` to `(X, G)` (`compressedSpectral_of_pencil`, read backwards: `(5b)`
for `(X B, G B)` gives it for `(X, G)` because `B` has a right inverse).
Step 1 — the rank factorization with its two inverses — is the one ingredient
that is not formalised here: it is the standard basis/echelon argument that a
`q × k` matrix of rank `ω` is `X B` with `X` of full column rank `ω` and `B` of
full row rank `ω`. -/

end Thm5

end Q1Paper
