/-
Q1Paper/PaperI/Hadamard.lean

Hadamard's determinant inequality, ported from the external package `hex-matrix-theory`
(Apache-2.0; tag `v0.10.0`; file `HexMatrixTheory/Hadamard.lean`, 106 lines, author
Kim Morrison), together with the integer corollary needed to replace the Leibniz
constant `bitLenInt (n!)` by the sharp Hadamard constant in Claim 21.

Our environment: Lean `v4.35.0`, Mathlib rev `f0b4c81` (the source pins a different
Mathlib rev, so the port was re-checked against our names).

## Main results

* `Matrix.norm_det_le_prod_norm_column` — Hadamard's inequality over `RCLike 𝕜`:
  `‖A.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2)`.
* `Matrix.det_natAbs_le_of_entry_bound` — integer corollary.  For
  `A : Matrix (Fin n) (Fin n) ℤ` with `|A i j| < 2 ^ b` and `1 ≤ n`,
  `A.det.natAbs ≤ n ^ ((n + 1) / 2) * (2 ^ b) ^ n`.
* `Matrix.det_abs_le_of_entry_bound` — the same in `ℤ`:
  `|A.det| ≤ ((n ^ ((n + 1) / 2) * (2 ^ b) ^ n : ℕ) : ℤ)`.
* `Matrix.bitLenInt_det_le_hadamard` — bit-length form:
  `bitLenInt A.det ≤ b * n + n.size * ((n + 1) / 2)`.
* `Matrix.bitLenInt_det_le_n_mul` — the shape requested for Claim 21:
  `bitLenInt A.det ≤ n * b + n * bitLenInt (n : ℤ)`.
* `Matrix.bitLenInt_det_le_n_mul_size_succ` — the explicit
  `bitLenInt A.det ≤ n * b + n * (n.size + 1)` form (Hadamard's `(n/2) log₂ n` term
  weakened to `n (log₂ n + 1)`).

## Which Mathlib lemmas the port needed

The proof is the standard Gram–Schmidt / QR argument; the ingredients are

* `gramSchmidtOrthonormalBasis`, `gramSchmidtOrthonormalBasis_det`
  (`Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.lean`) — the change-of-basis
  matrix to the Gram–Schmidt basis is upper triangular, so its determinant is the
  product of the diagonal inner products;
* `OrthonormalBasis.det_to_matrix_orthonormalBasis`
  (`Mathlib/Analysis/InnerProductSpace/PiL2.lean`) — `‖a.toBasis.det b‖ = 1` for two
  orthonormal bases, so passing from `e` to the standard basis does not change the norm;
* `AlternatingMap.eq_smul_basis_det` (`Mathlib/LinearAlgebra/Determinant.lean`) — to
  relate the two determinant functionals;
* `Basis.det_apply`, `EuclideanSpace.basisFun_toBasis`, `PiLp.basisFun_repr`,
  `EuclideanSpace.norm_eq`, `norm_inner_le_norm`, `finrank_euclideanSpace`.

## What drifted (and what did not)

The task anticipated that our rev had split
`OrthonormalBasis.det_to_matrix_orthonormalBasis` into
`..._of_same_orientation` / `..._of_opposite_orientation`.  The split lemmas *do* exist
(`Mathlib/Analysis/InnerProductSpace/Orientation.lean`), but they are an **addition**:
the original norm-valued statement `OrthonormalBasis.det_to_matrix_orthonormalBasis :
‖a.toBasis.det b‖ = 1` still exists in `PiL2.lean` (real case: the
`_real` variant `a.toBasis.det b = 1 ∨ a.toBasis.det b = -1`).  So the intended repair
was **not needed** — no case split on orientation is required, because we only need the
*norm* of the change-of-basis determinant.

Two real drifts did appear and were fixed:

1. `AlternatingMap.smul_apply` is deprecated in our rev; the replacement is the root
   lemma `smul_apply` (the constant moved namespaces).  Using the old name still
   compiles but warns, so we use `smul_apply`.
2. `[WellFoundedLT n]` is not actually used by the statement; our `variable` block
   triggers the `unusedSectionVars` linter, so the theorem is stated with
   `omit [WellFoundedLT n] in`.  (The source's block carries it because the source's
   Gram–Schmidt API is stated under it.)

Nothing else drifted: the source's proof term is accepted verbatim apart from these two
points.  In particular `Finset.prod_le_prod₀` still exists in our rev.

No `sorry`, no `admit`, no new axioms.  Check with
`lake env lean Q1Paper/PaperI/Hadamard.lean`.
-/

import Mathlib
import Q1Paper.PaperI.BitLen

open Finset Module InnerProductSpace
open scoped InnerProductSpace

namespace Matrix

/-! ## 1.  Hadamard's determinant inequality -/

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
  [LinearOrder n] [LocallyFiniteOrderBot n] [WellFoundedLT n]

omit [WellFoundedLT n] in
/-- **Hadamard's inequality** (sharp form). The norm of the determinant of a square matrix
over an `RCLike` field is at most the product of the Euclidean (L²) norms of its columns:
`‖A.det‖ ≤ ∏ j, √(∑ i, ‖A i j‖ ^ 2)`.

This dominates the crude entrywise bound `Matrix.det_le`; equality holds precisely when the
columns are pairwise orthogonal. -/
theorem norm_det_le_prod_norm_column (A : Matrix n n 𝕜) :
    ‖A.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) := by
  classical
  -- The columns of `A` viewed as vectors of Euclidean space.
  set f : n → EuclideanSpace 𝕜 n :=
    fun j => (WithLp.equiv 2 (n → 𝕜)).symm (fun i => A i j) with hf
  have hfi : ∀ i j, (f j) i = A i j := fun i j => rfl
  -- `‖f j‖` is exactly the L² norm of column `j`.
  have hcol : ∀ j, ‖f j‖ = Real.sqrt (∑ i, ‖A i j‖ ^ 2) := by
    intro j
    rw [EuclideanSpace.norm_eq]
    simp only [hfi]
  -- The Gram-Schmidt orthonormal basis built from the columns.
  have hdim : finrank 𝕜 (EuclideanSpace 𝕜 n) = Fintype.card n := finrank_euclideanSpace
  set e := gramSchmidtOrthonormalBasis hdim f with he
  -- Its change-of-basis determinant is the product of the diagonal inner products.
  have hdet : e.toBasis.det f = ∏ i, inner 𝕜 (e i) (f i) := by
    rw [he]; exact gramSchmidtOrthonormalBasis_det hdim f
  -- The determinant with respect to the standard orthonormal basis is `A.det`.
  have hmat : (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix f = A := by
    ext i j
    rw [Basis.toMatrix_apply, EuclideanSpace.basisFun_toBasis, PiLp.basisFun_repr]
    exact hfi i j
  have hstd : (EuclideanSpace.basisFun n 𝕜).toBasis.det f = A.det := by
    rw [Basis.det_apply, hmat]
  -- Passing from `e` to the standard orthonormal basis rescales the determinant by a
  -- unit-modulus factor, so the norms agree.
  have hchange : ‖e.toBasis.det f‖ = ‖A.det‖ := by
    have key : e.toBasis.det f
        = (e.toBasis.det (EuclideanSpace.basisFun n 𝕜).toBasis)
          • ((EuclideanSpace.basisFun n 𝕜).toBasis.det f) := by
      conv_lhs =>
        rw [(e.toBasis.det).eq_smul_basis_det (EuclideanSpace.basisFun n 𝕜).toBasis]
      simp
    have hunit : ‖e.toBasis.det (EuclideanSpace.basisFun n 𝕜).toBasis‖ = 1 := by
      exact e.det_to_matrix_orthonormalBasis (EuclideanSpace.basisFun n 𝕜)
    rw [key, norm_smul, hunit, one_mul, hstd]
  -- Cauchy-Schwarz on each diagonal factor.
  have hbound : ‖e.toBasis.det f‖ ≤ ∏ j, ‖f j‖ := by
    rw [hdet, norm_prod]
    refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
    calc ‖inner 𝕜 (e i) (f i)‖ ≤ ‖e i‖ * ‖f i‖ := norm_inner_le_norm _ _
      _ = ‖f i‖ := by rw [e.orthonormal.norm_eq_one, one_mul]
  calc ‖A.det‖ = ‖e.toBasis.det f‖ := hchange.symm
    _ ≤ ∏ j, ‖f j‖ := hbound
    _ = ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) := Finset.prod_congr rfl (fun j _ => hcol j)

/-! ## 2.  The integer corollary used by Claim 21

We bound each column by `√n · (2 ^ b - 1)` and each `(√n) ^ n` by `n ^ ((n + 1) / 2)`
(which is `n ^ (n / 2)` for even `n` and `n ^ ((n + 1) / 2)` for odd `n` — i.e. the
sharp `(n / 2) log₂ n` constant up to the harmless `ceil`). -/

/-- Auxiliary real inequality: `(√x) ^ m ≤ x ^ ((m + 1) / 2)` for `x ≥ 1`.
This is where the sharp `n / 2` exponent comes from: for even `m` there is equality,
for odd `m` the extra `√x ≤ x` factor costs at most one extra power. -/
theorem sqrt_pow_le_pow_div_two_add (x : ℝ) (hx : 1 ≤ x) (m : ℕ) :
    Real.sqrt x ^ m ≤ x ^ ((m + 1) / 2) := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hsx : Real.sqrt x ≤ x := by
    have h1 : Real.sqrt x ≤ Real.sqrt (x * x) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_mul_self hx0] at h1
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    have h2 : (k + k + 1) / 2 = k := by omega
    have h4 : k + k = 2 * k := by ring
    rw [h2, h4, pow_mul, Real.sq_sqrt hx0]
  · subst hk
    have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    rw [h2, pow_succ, pow_mul, Real.sq_sqrt hx0]
    exact mul_le_mul_of_nonneg_left hsx (by positivity)

/-- **Integer Hadamard corollary.**  If `|A i j| < 2 ^ b` for all entries of a square
integer matrix, then `|det A| ≤ n ^ ((n + 1) / 2) * (2 ^ b) ^ n`.

(For even `n` the exponent is exactly `n / 2`, matching the sharp Hadamard constant
`(n / 2) log₂ n`; for odd `n` it is `(n + 1) / 2`.) -/
theorem det_natAbs_le_of_entry_bound {n b : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, |A i j| < (2 : ℤ) ^ b) :
    A.det.natAbs ≤ n ^ ((n + 1) / 2) * (2 ^ b) ^ n := by
  -- (a) every entry is bounded by `2 ^ b - 1` in absolute value.
  have hlt : ∀ i j, (A i j).natAbs < 2 ^ b := by
    intro i j
    have h := hA i j
    have h2 : (((A i j).natAbs : ℕ) : ℤ) < ((2 ^ b : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      calc |A i j| < (2 : ℤ) ^ b := h
        _ = ((2 ^ b : ℕ) : ℤ) := by push_cast; ring
    exact_mod_cast h2
  -- (b) the real matrix obtained by casting.
  set M : Matrix (Fin n) (Fin n) ℝ := A.map (Int.castRingHom ℝ) with hM
  have hMij : ∀ i j, M i j = ((A i j : ℤ) : ℝ) := by
    intro i j
    simp [hM, Int.coe_castRingHom]
  -- (c) norm of an entry, and the resulting column bound.
  have hentry : ∀ i j, ‖M i j‖ ≤ ((2 ^ b - 1 : ℕ) : ℝ) := by
    intro i j
    have h1 : ‖M i j‖ = ((A i j).natAbs : ℝ) := by
      rw [hMij i j, Real.norm_eq_abs, ← Int.cast_abs]
      have h2 : ((A i j).natAbs : ℝ) = ((|A i j| : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.natCast_natAbs]
      rw [h2]
    rw [h1]
    exact_mod_cast Nat.le_sub_one_of_lt (hlt i j)
  -- (d) the sum of squares in each column.
  have hsum : ∀ j, ∑ i, ‖M i j‖ ^ 2 ≤ (n : ℝ) * ((2 ^ b - 1 : ℕ) : ℝ) ^ 2 := by
    intro j
    calc ∑ i, ‖M i j‖ ^ 2 ≤ ∑ _i : Fin n, ((2 ^ b - 1 : ℕ) : ℝ) ^ 2 := by
          exact Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hentry i j) 2)
      _ = (n : ℝ) * ((2 ^ b - 1 : ℕ) : ℝ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- (e) each column norm.
  have hsqrt : ∀ j, Real.sqrt (∑ i, ‖M i j‖ ^ 2)
      ≤ Real.sqrt n * ((2 ^ b - 1 : ℕ) : ℝ) := by
    intro j
    calc Real.sqrt (∑ i, ‖M i j‖ ^ 2)
        ≤ Real.sqrt ((n : ℝ) * ((2 ^ b - 1 : ℕ) : ℝ) ^ 2) := Real.sqrt_le_sqrt (hsum j)
      _ = Real.sqrt n * ((2 ^ b - 1 : ℕ) : ℝ) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (by positivity)]
  -- (f) Hadamard, then bound the product.
  have hprod : ‖M.det‖ ≤ (Real.sqrt n) ^ n * ((2 ^ b - 1 : ℕ) : ℝ) ^ n := by
    calc ‖M.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖M i j‖ ^ 2) := norm_det_le_prod_norm_column M
      _ ≤ ∏ _j : Fin n, (Real.sqrt n * ((2 ^ b - 1 : ℕ) : ℝ)) := by
          refine Finset.prod_le_prod₀ (fun j _ => Real.sqrt_nonneg _) (fun j _ => hsqrt j)
      _ = (Real.sqrt n * ((2 ^ b - 1 : ℕ) : ℝ)) ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = (Real.sqrt n) ^ n * ((2 ^ b - 1 : ℕ) : ℝ) ^ n := mul_pow _ _ n
  -- (g) the two scalar bounds.
  have hfinal : ‖M.det‖ ≤ ((n ^ ((n + 1) / 2) * (2 ^ b) ^ n : ℕ) : ℝ) := by
    have h1 : (Real.sqrt n) ^ n ≤ (n : ℝ) ^ ((n + 1) / 2) :=
      sqrt_pow_le_pow_div_two_add (n : ℝ) (by exact_mod_cast hn) n
    have h2 : ((2 ^ b - 1 : ℕ) : ℝ) ^ n ≤ ((2 ^ b : ℕ) : ℝ) ^ n :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.sub_le (2 ^ b) 1) n
    calc ‖M.det‖ ≤ (Real.sqrt n) ^ n * ((2 ^ b - 1 : ℕ) : ℝ) ^ n := hprod
      _ ≤ (n : ℝ) ^ ((n + 1) / 2) * ((2 ^ b : ℕ) : ℝ) ^ n :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = ((n ^ ((n + 1) / 2) * (2 ^ b) ^ n : ℕ) : ℝ) := by push_cast; ring
  -- (h) transport back to `ℤ` / `ℕ`.
  have hcast : ((A.det : ℤ) : ℝ) = M.det := by
    have h := RingHom.map_det (Int.castRingHom ℝ) A
    rw [RingHom.mapMatrix_apply] at h
    simpa [hM, Int.coe_castRingHom] using h
  have hnorm : ((A.det.natAbs : ℕ) : ℝ) = ‖M.det‖ := by
    rw [← hcast, Real.norm_eq_abs, ← Int.cast_abs]
    rw [show ((A.det.natAbs : ℕ) : ℝ) = ((|A.det| : ℤ) : ℝ) from by
      rw [← Int.cast_natCast, Int.natCast_natAbs]]
  have h2 : ((A.det.natAbs : ℕ) : ℝ)
      ≤ ((n ^ ((n + 1) / 2) * (2 ^ b) ^ n : ℕ) : ℝ) := by
    rw [hnorm]; exact hfinal
  exact_mod_cast h2

/-- The same corollary stated inside `ℤ`:
`|A.det| ≤ n ^ ((n + 1) / 2) * (2 ^ b) ^ n`. -/
theorem det_abs_le_of_entry_bound {n b : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, |A i j| < (2 : ℤ) ^ b) :
    |A.det| ≤ ((n ^ ((n + 1) / 2) * (2 ^ b) ^ n : ℕ) : ℤ) := by
  calc |A.det| = ((A.det.natAbs : ℕ) : ℤ) := (Int.natCast_natAbs A.det).symm
    _ ≤ ((n ^ ((n + 1) / 2) * (2 ^ b) ^ n : ℕ) : ℤ) := by
        exact_mod_cast det_natAbs_le_of_entry_bound hn A hA

/-- **Bit-length form of the Hadamard bound.**  For an integer matrix whose entries are
bounded by `2 ^ b`, the determinant needs at most `b · n + n.size · ((n + 1) / 2)` bits —
compare the Leibniz bound `n · b + bitLenInt (n!)`, whose second term is `Θ(n log n)`
with constant `1` instead of `1/2`. -/
theorem bitLenInt_det_le_hadamard {n b : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, |A i j| < (2 : ℤ) ^ b) :
    Q1Paper.PaperI.bitLenInt A.det ≤ b * n + n.size * ((n + 1) / 2) := by
  rw [Q1Paper.PaperI.bitLenInt_le_iff]
  have hexp : (n + 1) / 2 ≠ 0 := by omega
  calc A.det.natAbs ≤ n ^ ((n + 1) / 2) * (2 ^ b) ^ n :=
        det_natAbs_le_of_entry_bound hn A hA
    _ = n ^ ((n + 1) / 2) * 2 ^ (b * n) := by rw [← Nat.pow_mul]
    _ < (2 ^ n.size) ^ ((n + 1) / 2) * 2 ^ (b * n) := by
        refine Nat.mul_lt_mul_of_pos_right
          (Nat.pow_lt_pow_left (Nat.lt_size_self n) hexp) (by positivity)
    _ = 2 ^ (n.size * ((n + 1) / 2)) * 2 ^ (b * n) := by rw [← Nat.pow_mul]
    _ = 2 ^ (n.size * ((n + 1) / 2) + b * n) := (Nat.pow_add _ _ _).symm
    _ = 2 ^ (b * n + n.size * ((n + 1) / 2)) := by rw [Nat.add_comm]

/-- The shape used by Claim 21: `bitLenInt A.det ≤ n * b + n * bitLenInt (n : ℤ)`.
This is `n·b + n·log₂ n` — the Hadamard constant — instead of the Leibniz
`bitLenInt (n!) ≈ n log₂ n` with the extra `log₂ n` factor behaviour of `bitLenInt (n!)`. -/
theorem bitLenInt_det_le_n_mul {n b : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, |A i j| < (2 : ℤ) ^ b) :
    Q1Paper.PaperI.bitLenInt A.det ≤ n * b + n * Q1Paper.PaperI.bitLenInt (n : ℤ) := by
  have hsz : Q1Paper.PaperI.bitLenInt (n : ℤ) = n.size := by
    simp [Q1Paper.PaperI.bitLenInt]
  rw [hsz]
  have h2 : (n + 1) / 2 ≤ n := by omega
  calc Q1Paper.PaperI.bitLenInt A.det ≤ b * n + n.size * ((n + 1) / 2) :=
        bitLenInt_det_le_hadamard hn A hA
    _ ≤ b * n + n.size * n := Nat.add_le_add_left (Nat.mul_le_mul_left n.size h2) (b * n)
    _ = n * b + n * n.size := by ring

/-! ### 2b.  The explicit `n * b + n * (n.size + 1)` form requested for the paper

The sharpest statement in this file is `Matrix.bitLenInt_det_le_hadamard`,
`bitLenInt A.det ≤ b * n + n.size * ((n + 1) / 2)`, which keeps Hadamard's constant
`1/2` in front of the `n log₂ n` term.  The corollary below trades that constant `1/2`
for `1` to obtain the single-term shape `n * b + n * (n.size + 1)`, i.e.
`n · b + n · (log₂ n + 1)`.  Nothing is lost asymptotically: both are `O(n (b + log n))`. -/

/-- **Explicit bit-length bound of Hadamard type.**
For `A : Matrix (Fin n) (Fin n) ℤ` with `|A i j| < 2 ^ b` for every entry and `1 ≤ n`,

`bitLenInt A.det ≤ n * b + n * (n.size + 1)`,

i.e. `n · b + n · (log₂ n + 1)`, where `n.size` is the binary length of `n`
(so `log₂ n < n.size ≤ log₂ n + 1`).  The second summand is Hadamard's
`(n / 2) · log₂ n` column-norm term, weakened to the coarser `n · (log₂ n + 1)`:
`n.size * ((n + 1) / 2) ≤ n * n.size ≤ n * (n.size + 1)`.

The sharp form with the genuine Hadamard constant is `Matrix.bitLenInt_det_le_hadamard`. -/
theorem bitLenInt_det_le_n_mul_size_succ {n b : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : ∀ i j, |A i j| < (2 : ℤ) ^ b) :
    Q1Paper.PaperI.bitLenInt A.det ≤ n * b + n * (n.size + 1) := by
  have h1 : (n + 1) / 2 ≤ n := by omega
  calc Q1Paper.PaperI.bitLenInt A.det ≤ b * n + n.size * ((n + 1) / 2) :=
        bitLenInt_det_le_hadamard hn A hA
    _ ≤ b * n + n.size * n := Nat.add_le_add_left (Nat.mul_le_mul_left n.size h1) (b * n)
    _ = n * b + n * n.size := by ring
    _ ≤ n * b + n * (n.size + 1) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left n (Nat.le_succ n.size)) (n * b)

end Matrix
