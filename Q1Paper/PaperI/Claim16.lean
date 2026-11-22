/-
Q1Paper/PaperI/Claim16.lean

Claim 16 of the paper (`lem:zero`, the "zero-free-row" case).

For `X G : Matrix (Fin q) (Fin ω) ℚ` with `q ≥ ω ≥ 1` and the pencil
`Q(λ) = λ X − G : Matrix (Fin q) (Fin ω) ℚ[X]`, the paper states the equivalence of

  (i)   `rank (λ • X − G) = ω` for every `λ : ℂ`;
  (ii)  the maximal `ω × ω` minors of `Q` have no common complex root;
  (iii) the maximal minors do not all vanish and their gcd in `ℚ[λ]` is a nonzero constant;
  (iv)  there is `S : Matrix (Fin ω) (Fin q) ℚ[X]` with `S * Q = 1` and `natDegree ≤ 2ω−2`;
  (v)   coefficient matrices `S_0, …, S_{2ω−2} : Matrix (Fin ω) (Fin q) ℚ` with
        `−S_0 G = 1`, `S_{j−1} X − S_j G = 0` (`1 ≤ j ≤ 2ω−2`), `S_{2ω−2} X = 0`.

What is proved here (no `sorry`, no `admit`, no new axioms):

* `coeffM` and its calculus: the `k`-th coefficient matrix of a polynomial matrix,
  compatible with sums, differences, multiplication by `X`, the identity, and with
  multiplication by a constant matrix (`coeffM_mul_map_C`).
* `mul_pencil_eq`       : `S * (λX − G) = X • (S·X) − S·G` inside `K[X]`.
* `iv_implies_v`        : (iv) ⟹ (v), **for an arbitrary field `K`** (coefficient comparison).
* `v_implies_iv`        : (v) ⟹ (iv), arbitrary field `K` (via `spoly_mul_pencil_eq_one`),
  including the degree bound `2ω−2`.
* `claim16_iv_iff_v`    : (iv) ⟺ (v) over `ℚ`.
* `pencil_map_eval₂`, `spoly_map_eval₂`, `map_mul_eval₂`, `map_one_eval₂` : evaluation of
  the pencil and of `spoly` at `lam : ℂ`, and multiplicativity of evaluation.
* `v_implies_i`         : (v) ⟹ (i) — evaluating at `lam` produces a left inverse of
  `lam • X − G`, hence full column rank.
* `claim16_iv_implies_i`   : (iv) ⟹ (i) over `ℚ` (composite).
* `claim16_ii_implies_iv`  : (ii)/(iii) ⟹ (iv) over an algebraically closed field
  (`exists_leftInverse_linear`).
* `claim16_iii_implies_iv` : (iii), in the form "the maximal minors admit a Bézout family of
  degree `< ω` over `ℚ`" ⟹ (iv).  This is the exact output of the paper's Bézout step.
* `claim16_iii_implies_i`  : the composite (iii) ⟹ (i) over `ℚ`.

Remaining gap: (iii) "the gcd in `ℚ[λ]` of the maximal minors is a nonzero constant" ⟹ the
degree-bounded Bézout family over `ℚ` used as the hypothesis of
`claim16_iii_implies_iv`.  The paper obtains it over `ℝ` (`exists_bezout_family_real`); the
transport back to `ℚ` needs a descent argument for the rational linear system which is not
formalised here.  Over an algebraically closed field the gap is closed by
`claim16_ii_implies_iv`.
-/

import Q1Paper.G3Coeff
import Q1Paper.G3LeftInverse
import Q1Paper.BezoutReal
import Mathlib.LinearAlgebra.Matrix.Rank

open Matrix Polynomial
open scoped BigOperators

namespace Q1Paper

noncomputable section

/-! ## Coefficient matrices -/

/-- The `k`-th coefficient matrix of a polynomial matrix `M`. -/
def coeffM {K : Type*} [Semiring K] {m n : Type*} (M : Matrix m n K[X]) (k : ℕ) :
    Matrix m n K :=
  Matrix.of fun i j => (M i j).coeff k

@[simp] theorem coeffM_apply {K : Type*} [Semiring K] {m n : Type*}
    (M : Matrix m n K[X]) (k : ℕ) (i : m) (j : n) :
    coeffM M k i j = (M i j).coeff k := rfl

section CoeffCalculus

variable {K : Type*} [CommRing K] {m n : Type*}

theorem coeffM_add (A B : Matrix m n K[X]) (k : ℕ) :
    coeffM (A + B) k = coeffM A k + coeffM B k := by
  ext i j
  simp [coeffM]

theorem coeffM_sub (A B : Matrix m n K[X]) (k : ℕ) :
    coeffM (A - B) k = coeffM A k - coeffM B k := by
  ext i j
  simp [coeffM]

theorem coeffM_smul_X_succ (A : Matrix m n K[X]) (k : ℕ) :
    coeffM ((Polynomial.X : K[X]) • A) (k + 1) = coeffM A k := by
  ext i j
  simp [coeffM, Matrix.smul_apply, smul_eq_mul]

theorem coeffM_smul_X_zero (A : Matrix m n K[X]) :
    coeffM ((Polynomial.X : K[X]) • A) 0 = 0 := by
  ext i j
  rw [coeffM_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  exact Polynomial.X_dvd_iff.mp ⟨A i j, rfl⟩

theorem coeffM_one_zero [DecidableEq n] :
    coeffM (1 : Matrix n n K[X]) 0 = 1 := by
  ext i j
  rw [coeffM_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Polynomial.coeff_one, if_pos rfl, Matrix.one_apply_eq]
  · rw [if_neg hij, Polynomial.coeff_zero, Matrix.one_apply_ne hij]

theorem coeffM_one_succ [DecidableEq n] (k : ℕ) :
    coeffM (1 : Matrix n n K[X]) (k + 1) = 0 := by
  ext i j
  rw [coeffM_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Polynomial.coeff_one, if_neg (Nat.succ_ne_zero k), Matrix.zero_apply]
  · rw [if_neg hij, Polynomial.coeff_zero, Matrix.zero_apply]

end CoeffCalculus

/-- Coefficient matrix of a product with a constant matrix: the `k`-th coefficient of
`S * Xm` (with `Xm` seen in `K[X]`) is the `k`-th coefficient matrix of `S` times `Xm`. -/
theorem coeffM_mul_map_C {K : Type*} [Field K] {ω q : ℕ}
    (S : Matrix (Fin ω) (Fin q) K[X]) (Xm : Matrix (Fin q) (Fin ω) K) (k : ℕ) :
    coeffM (S * Xm.map (Polynomial.C : K →+* K[X])) k = coeffM S k * Xm := by
  classical
  ext i j
  rw [coeffM_apply, coeff_mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [Finset.sum_eq_single (k, 0)]
  · simp [Matrix.map_apply, Polynomial.coeff_C]
  · intro x hx hxne
    have hsum : x.1 + x.2 = k := Finset.mem_antidiagonal.mp hx
    have hx2 : x.2 ≠ 0 := by
      intro h
      have h1 : x.1 = k := by omega
      exact hxne (Prod.ext h1 h)
    simp [Matrix.map_apply, Polynomial.coeff_C, hx2]
  · intro h
    exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h

/-! ## The pencil and its evaluation -/

/-- The entries of the pencil `λX − G` are affine in `λ`. -/
theorem pencil_natDegree_le {K : Type*} [Field K] {q ω : ℕ}
    (X G : Matrix (Fin q) (Fin ω) K) (i : Fin q) (j : Fin ω) :
    ((pencil X G) i j).natDegree ≤ 1 := by
  rw [pencil_apply]
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · calc (((Polynomial.C (X i j) : K[X]) * Polynomial.X)).natDegree
        ≤ (Polynomial.C (X i j) : K[X]).natDegree + Polynomial.X.natDegree :=
          Polynomial.natDegree_mul_le
      _ = 1 := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
  · rw [Polynomial.natDegree_C]; omega

/-- Evaluating the pencil at `lam : ℂ` gives `lam • X − G`. -/
theorem pencil_map_eval₂ {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℚ) (lam : ℂ) :
    (pencil X G).map (Polynomial.eval₂ (algebraMap ℚ ℂ) lam)
      = lam • X.map (algebraMap ℚ ℂ) - G.map (algebraMap ℚ ℂ) := by
  ext i j
  simp only [Matrix.map_apply, pencil_apply, Matrix.sub_apply, Matrix.smul_apply,
    Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
    smul_eq_mul]
  ring

/-- Evaluating `spoly S` at `lam : ℂ` gives `Σ_j lam^j • S_j`. -/
theorem spoly_map_eval₂ {q ω d : ℕ} (S : Fin (d + 1) → Matrix (Fin ω) (Fin q) ℚ) (lam : ℂ) :
    (spoly S).map (Polynomial.eval₂ (algebraMap ℚ ℂ) lam)
      = ∑ j : Fin (d + 1), (lam ^ (j : ℕ)) • (S j).map (algebraMap ℚ ℂ) := by
  classical
  ext i j
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.map_apply, spoly, Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro c _
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]

/-- Evaluation at `lam : ℂ` is multiplicative on matrix products. -/
theorem map_mul_eval₂ {m n p : Type*} [Fintype n] (lam : ℂ)
    (A : Matrix m n ℚ[X]) (B : Matrix n p ℚ[X]) :
    (A * B).map (Polynomial.eval₂ (algebraMap ℚ ℂ) lam)
      = A.map (Polynomial.eval₂ (algebraMap ℚ ℂ) lam)
        * B.map (Polynomial.eval₂ (algebraMap ℚ ℂ) lam) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul]

/-- Evaluation at `lam : ℂ` sends the identity matrix to the identity matrix. -/
theorem map_one_eval₂ {n : Type*} [Fintype n] [DecidableEq n] (lam : ℂ) :
    (1 : Matrix n n ℚ[X]).map (Polynomial.eval₂ (algebraMap ℚ ℂ) lam) = 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp [Polynomial.eval₂_one, Polynomial.eval₂_zero]

/-- The pencil splits as `X • (S·X) − S·G` inside `K[X]`. -/
theorem mul_pencil_eq {K : Type*} [Field K] {q ω : ℕ} (S : Matrix (Fin ω) (Fin q) K[X])
    (X G : Matrix (Fin q) (Fin ω) K) :
    S * pencil X G
      = (Polynomial.X : K[X]) • (S * X.map (Polynomial.C : K →+* K[X]))
        - S * G.map (Polynomial.C : K →+* K[X]) := by
  rw [pencil, Matrix.mul_sub, Matrix.mul_smul]

/-! ## (iv) ⟹ (v): coefficient comparison -/

/-- **(iv) ⟹ (v).**  If a polynomial matrix `S` of degree at most `2ω−2` is a left inverse
of the pencil `λX − G`, then its coefficient matrices `S_j` solve the linear system
`−S_0 G = 1`, `S_{j−1} X − S_j G = 0`, `S_{2ω−2} X = 0`. -/
theorem iv_implies_v {K : Type*} [Field K] {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) K)
    (S : Matrix (Fin ω) (Fin q) K[X]) (hmul : S * pencil X G = 1)
    (hdeg : ∀ i j, (S i j).natDegree ≤ 2 * ω - 2) :
    ∃ T : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin q) K,
      T 0 * G = -1 ∧
      (∀ j : Fin (2 * ω - 2), T (Fin.castSucc j) * X - T (Fin.succ j) * G = 0) ∧
      T (Fin.last (2 * ω - 2)) * X = 0 := by
  classical
  set d := 2 * ω - 2 with hddef
  set A : Matrix (Fin ω) (Fin ω) K[X] := S * X.map (Polynomial.C : K →+* K[X]) with hA
  set B : Matrix (Fin ω) (Fin ω) K[X] := S * G.map (Polynomial.C : K →+* K[X]) with hB
  have hAB : (Polynomial.X : K[X]) • A - B = 1 := by
    rw [hA, hB, ← mul_pencil_eq]
    exact hmul
  have hAeq : ∀ k, coeffM A k = coeffM S k * X := by
    intro k
    rw [hA, coeffM_mul_map_C]
  have hBeq : ∀ k, coeffM B k = coeffM S k * G := by
    intro k
    rw [hB, coeffM_mul_map_C]
  refine ⟨fun j => coeffM S (j : ℕ), ?_, ?_, ?_⟩
  · have h := congrArg (fun N => coeffM N 0) hAB
    rw [coeffM_sub, coeffM_smul_X_zero, coeffM_one_zero] at h
    rw [hBeq, zero_sub] at h
    simpa using neg_eq_iff_eq_neg.mp h
  · intro j
    have h := congrArg (fun N => coeffM N ((j : ℕ) + 1)) hAB
    rw [coeffM_sub, coeffM_smul_X_succ, coeffM_one_succ] at h
    rw [hAeq, hBeq] at h
    simpa [Fin.val_castSucc, Fin.val_succ] using h
  · have h := congrArg (fun N => coeffM N (d + 1)) hAB
    rw [coeffM_sub, coeffM_smul_X_succ, coeffM_one_succ] at h
    have hS0 : coeffM S (d + 1) = 0 := by
      ext i j
      rw [coeffM_apply, Matrix.zero_apply]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hdeg i j; omega)
    rw [hBeq, hS0, Matrix.zero_mul, sub_zero, hAeq] at h
    simpa [Fin.val_last] using h

/-! ## (v) ⟹ (iv) -/

/-- **(v) ⟹ (iv).**  A solution of the coefficient system reassembles into a polynomial
left inverse of the pencil, of degree at most `2ω−2`. -/
theorem v_implies_iv {K : Type*} [Field K] {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) K)
    (S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin q) K)
    (h0 : S 0 * G = -1)
    (hj : ∀ j : Fin (2 * ω - 2), S (Fin.castSucc j) * X - S (Fin.succ j) * G = 0)
    (hd : S (Fin.last (2 * ω - 2)) * X = 0) :
    ∃ S' : Matrix (Fin ω) (Fin q) K[X],
      S' * pencil X G = 1 ∧ ∀ i j, (S' i j).natDegree ≤ 2 * ω - 2 := by
  refine ⟨spoly S, spoly_mul_pencil_eq_one S X G h0 hj hd, ?_⟩
  intro i j
  rw [spoly, Matrix.sum_apply]
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  refine Finset.sup_le ?_
  intro k _
  have hk : (k : ℕ) ≤ 2 * ω - 2 := by have := k.isLt; omega
  have hterm : (((Polynomial.X ^ (k : ℕ) : K[X]) •
      ((S k).map (Polynomial.C : K →+* K[X]))) i j).natDegree
      = ((Polynomial.X ^ (k : ℕ) : K[X]) * Polynomial.C ((S k) i j)).natDegree := by
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
  change (((Polynomial.X ^ (k : ℕ) : K[X]) •
      ((S k).map (Polynomial.C : K →+* K[X]))) i j).natDegree ≤ 2 * ω - 2
  rw [hterm]
  calc ((Polynomial.X ^ (k : ℕ) : K[X]) * Polynomial.C ((S k) i j)).natDegree
      ≤ (Polynomial.X ^ (k : ℕ) : K[X]).natDegree
          + (Polynomial.C ((S k) i j)).natDegree := Polynomial.natDegree_mul_le
    _ = (k : ℕ) + 0 := by rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
    _ ≤ 2 * ω - 2 := by omega

/-- **(iv) ⟺ (v)** over `ℚ`. -/
theorem claim16_iv_iff_v {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℚ) :
    (∃ S : Matrix (Fin ω) (Fin q) ℚ[X],
        S * pencil X G = 1 ∧ ∀ i j, (S i j).natDegree ≤ 2 * ω - 2)
      ↔ ∃ T : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin q) ℚ,
          T 0 * G = -1 ∧
          (∀ j : Fin (2 * ω - 2), T (Fin.castSucc j) * X - T (Fin.succ j) * G = 0) ∧
          T (Fin.last (2 * ω - 2)) * X = 0 := by
  constructor
  · rintro ⟨S, hS, hdeg⟩
    exact iv_implies_v X G S hS hdeg
  · rintro ⟨T, h0, hj, hd⟩
    exact v_implies_iv X G T h0 hj hd

/-! ## (v) ⟹ (i): full column rank at every complex parameter -/

/-- **(v) ⟹ (i).**  Evaluating a solution of the coefficient system at `lam : ℂ` produces a
left inverse of `lam • X − G`, which therefore has full column rank `ω`. -/
theorem v_implies_i {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℚ)
    (S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin q) ℚ)
    (h0 : S 0 * G = -1)
    (hj : ∀ j : Fin (2 * ω - 2), S (Fin.castSucc j) * X - S (Fin.succ j) * G = 0)
    (hd : S (Fin.last (2 * ω - 2)) * X = 0) :
    ∀ lam : ℂ, (lam • X.map (algebraMap ℚ ℂ) - G.map (algebraMap ℚ ℂ)).rank = ω := by
  have hm : spoly S * pencil X G = 1 := spoly_mul_pencil_eq_one S X G h0 hj hd
  intro lam
  set M : Matrix (Fin q) (Fin ω) ℂ :=
    lam • X.map (algebraMap ℚ ℂ) - G.map (algebraMap ℚ ℂ) with hM
  set T : Matrix (Fin ω) (Fin q) ℂ :=
    ∑ j : Fin (2 * ω - 2 + 1), (lam ^ (j : ℕ)) • (S j).map (algebraMap ℚ ℂ) with hT
  have h1 : T * M = 1 := by
    have h := congrArg (fun N : Matrix (Fin ω) (Fin ω) ℚ[X] =>
      N.map (Polynomial.eval₂ (algebraMap ℚ ℂ) lam)) hm
    rw [map_mul_eval₂, map_one_eval₂, spoly_map_eval₂, pencil_map_eval₂] at h
    rw [hT, hM]
    exact h
  have hle : ω ≤ M.rank := by
    have h2 : (1 : Matrix (Fin ω) (Fin ω) ℂ).rank ≤ M.rank := by
      rw [← h1]
      exact Matrix.rank_mul_le_right T M
    rwa [Matrix.rank_one, Fintype.card_fin] at h2
  have hge : M.rank ≤ ω := by
    simpa using Matrix.rank_le_card_width M
  exact le_antisymm hge hle

/-- **(iv) ⟹ (i)** over `ℚ`: a degree-bounded polynomial left inverse forces full column
rank at every complex parameter. -/
theorem claim16_iv_implies_i {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℚ)
    (S : Matrix (Fin ω) (Fin q) ℚ[X]) (hmul : S * pencil X G = 1)
    (hdeg : ∀ i j, (S i j).natDegree ≤ 2 * ω - 2) :
    ∀ lam : ℂ, (lam • X.map (algebraMap ℚ ℂ) - G.map (algebraMap ℚ ℂ)).rank = ω := by
  obtain ⟨T, h0, hj, hd⟩ := iv_implies_v X G S hmul hdeg
  exact v_implies_i X G T h0 hj hd

/-! ## (ii)/(iii) ⟹ (iv) over an algebraically closed field -/

/-- **(ii)/(iii) ⟹ (iv)**, over an algebraically closed field `K`.  The hypothesis is the
"no common root" form of (ii); over an algebraically closed field this is equivalent to
(iii) (the gcd of the maximal minors being a nonzero constant). -/
theorem claim16_ii_implies_iv {K : Type*} [Field K] [IsAlgClosed K] {q ω : ℕ} (hω : 1 ≤ ω)
    (X G : Matrix (Fin q) (Fin ω) K)
    (hroot : ∀ α : K, ∃ e : Fin ω ↪ Fin q, (minors (pencil X G) e).eval α ≠ 0) :
    ∃ S : Matrix (Fin ω) (Fin q) K[X],
      S * pencil X G = 1 ∧ ∀ i j, (S i j).natDegree ≤ 2 * ω - 2 :=
  exists_leftInverse_linear hω (pencil X G) (fun i j => pencil_natDegree_le X G i j) hroot

/-! ## (iii) ⟹ (iv) over `ℚ` from a degree-bounded Bézout family -/

/-- Degree bound for the adjugate block used in the assembly of the rectangular left
inverse.  This is `Q1Paper.natDegree_adjRowInverse_le` without the `IsAlgClosed` hypothesis
that the ambient section of `G3LeftInverse` carries. -/
theorem natDegree_adjRowInverse_le' {K : Type*} [Field K] {q ω : ℕ} (_hω : 1 ≤ ω)
    (Q : Matrix (Fin q) (Fin ω) K[X]) (hlin : ∀ i j, (Q i j).natDegree ≤ 1)
    (e : Fin ω → Fin q) (i : Fin ω) (j : Fin q) :
    (adjRowInverse e Q i j).natDegree ≤ ω - 1 := by
  classical
  rw [adjRowInverse, Matrix.mul_apply]
  refine le_trans (Polynomial.natDegree_sum_le (Finset.univ : Finset (Fin ω)) _) ?_
  refine Finset.sup_le ?_
  intro k _
  calc (Matrix.adjugate (Q.submatrix e id) i k * rowSel e k j).natDegree
      ≤ (Matrix.adjugate (Q.submatrix e id) i k).natDegree
          + (rowSel (R := K[X]) e k j : K[X]).natDegree := Polynomial.natDegree_mul_le
    _ ≤ (ω - 1) + 0 := by
        have h1 : (Matrix.adjugate (Q.submatrix e id) i k).natDegree ≤ ω - 1 :=
          natDegree_adjugate_le _ (fun a b => hlin (e a) b) i k
        have h2 : (rowSel (R := K[X]) e k j : K[X]).natDegree = 0 := by
          unfold rowSel
          rw [Matrix.of_apply]
          split_ifs <;> simp
        omega
    _ = ω - 1 := by omega

/-- **(iii) ⟹ (iv)** over `ℚ`, where (iii) is supplied in the form in which the paper's
Bézout argument (`exists_bezout_family_real`, transported to the pencil) delivers it: the
maximal minors of the pencil have a Bézout family over `ℚ[λ]` with all multipliers of
degree `< ω`.  The conclusion is (iv) with the exact bound `2ω−2`. -/
theorem claim16_iii_implies_iv {q ω : ℕ} (hω : 1 ≤ ω) (X G : Matrix (Fin q) (Fin ω) ℚ)
    (hbez : ∃ g : (Fin ω ↪ Fin q) → ℚ[X],
      (∑ e, g e * minors (pencil X G) e) = 1 ∧ ∀ e, (g e).natDegree < ω) :
    ∃ S : Matrix (Fin ω) (Fin q) ℚ[X],
      S * pencil X G = 1 ∧ ∀ i j, (S i j).natDegree ≤ 2 * ω - 2 := by
  classical
  obtain ⟨g, hbezsum, hgdeg⟩ := hbez
  refine ⟨∑ e, g e • adjRowInverse (e : Fin ω → Fin q) (pencil X G),
    leftInverse_of_bezout (Q := pencil X G) hbezsum, ?_⟩
  intro i j
  rw [Matrix.sum_apply]
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  refine Finset.sup_le ?_
  intro e _
  have h1 : (g e).natDegree ≤ ω - 1 := by have := hgdeg e; omega
  have h2 : (adjRowInverse (e : Fin ω → Fin q) (pencil X G) i j).natDegree ≤ ω - 1 :=
    natDegree_adjRowInverse_le' hω (pencil X G) (fun a b => pencil_natDegree_le X G a b)
      (e : Fin ω → Fin q) i j
  calc (((g e) • adjRowInverse (e : Fin ω → Fin q) (pencil X G)) i j).natDegree
      = ((g e) * adjRowInverse (e : Fin ω → Fin q) (pencil X G) i j).natDegree := by
        rw [Matrix.smul_apply, smul_eq_mul]
    _ ≤ (g e).natDegree
          + (adjRowInverse (e : Fin ω → Fin q) (pencil X G) i j).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ (ω - 1) + (ω - 1) := Nat.add_le_add h1 h2
    _ = 2 * ω - 2 := by omega

/-- **(iii) ⟹ (i)** over `ℚ`, composing `claim16_iii_implies_iv`, `iv_implies_v` and
`v_implies_i`. -/
theorem claim16_iii_implies_i {q ω : ℕ} (hω : 1 ≤ ω) (X G : Matrix (Fin q) (Fin ω) ℚ)
    (hbez : ∃ g : (Fin ω ↪ Fin q) → ℚ[X],
      (∑ e, g e * minors (pencil X G) e) = 1 ∧ ∀ e, (g e).natDegree < ω) :
    ∀ lam : ℂ, (lam • X.map (algebraMap ℚ ℂ) - G.map (algebraMap ℚ ℂ)).rank = ω := by
  obtain ⟨S, hS, hdeg⟩ := claim16_iii_implies_iv hω X G hbez
  exact claim16_iv_implies_i X G S hS hdeg

end

end Q1Paper
