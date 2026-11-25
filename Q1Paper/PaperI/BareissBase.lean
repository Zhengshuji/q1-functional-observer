
import Q1Paper.PaperI.BitLenAdd

/-!
Q1Paper/PaperI/BareissBase.lean

Claim 13 / Claim 21 support: the *Bareiss fraction-free elimination*
layer (design-report companion).

The general theorem — "every entry of the Bareiss tableau is a bordered minor of
the original matrix" — is Sylvester's / Desnanot–Jacobi identity and is **not**
stated here: it is the one piece that needs real work (Cauchy–Binet).  What is
proved here is everything the induction rests on:

* `bMinor`      : the ω × ω minor selected by two index maps `Fin ω → N`;
* `bMinor2`     : the bordered 2 × 2 minor `det [[a_kk, a_kj],[a_ik, a_ij]]`;
* `bMinor3`     : the bordered 3 × 3 minor `det [[a_kk,a_kl,a_kj],...]`;
* `bStepNum`    : the numerator `a_kk a_ij - a_ik a_kj` of a Bareiss step;
* `bStep`       : the step itself, `bStepNum ... / d` (division by the previous pivot);

Base of the induction (no hypothesis at all):
* `bStepNum_zero_eq_minor2` : step 0's numerator *is* the 2 × 2 bordered minor;
* `bareiss_two_two`         : 2 × 2 case — the algorithm's only step, divisor `1`,
                              gives `det`;
* `bareiss_two_dvd`         : the 2 × 2 exact-division lemma (divisor `1`, vacuous).

The first non-vacuous instance (needs a00 ≠ 0):
* `sylvester_two`  : a11^(1) a_ij^(1) - a_i1^(1) a_1j^(1) = a00 * det A[{0,1,i},{0,1,j}],
  i.e. step 1's numerator is a00 times the 3 × 3 bordered minor;
* `sylvester_three`: the same in the `Fin 3` spelling `b11 b22 - b21 b12 = a00 det A`;
* `bMinor3_last`   : for n = 3 that 3 × 3 minor is `det A` itself;
* `bareiss_step_one_dvd` / `bareiss_step_one_exact` : exact division at step 1;
* `bareiss_three_two_two` : the 3 × 3 algorithm's last entry is `det A`.

Claim 21 bound:
* `bitLenInt_bMinor_le`           : ω·b + bitLen ω! bits for a minor;
* `bitLenInt_bMinor_le_factorial` : ω ≤ N upgraded to N·b + bitLen N!;
* `bitLenInt_bMinor_le_size`      : closed form N·b + N·(N.size) + 1.

No `sorry`, no new axioms.  Check with
  lake env lean Q1Paper/PaperI/BareissBase.lean
-/


open Matrix

namespace Q1Paper.PaperI

/-! ## 1.  Minors and the Bareiss step -/

variable {R : Type*} [CommRing R]

/-- The ω × ω **minor** of `M` cut out by the row map `r` and the column map
`c`: the determinant of the corresponding submatrix.

`r` and `c` need not be injective; nothing below uses injectivity. -/
noncomputable def bMinor {m n : Type*} (M : Matrix m n R) {ω : ℕ}
    (r : Fin ω → m) (c : Fin ω → n) : R :=
  (M.submatrix r c).det

/-- The bordered 2 × 2 **minor** `det [[a_kk, a_kj], [a_ik, a_ij]]`.

It is the entry produced by the Bareiss step at pivot `(k,k)` when the previous
pivot is `1`; with `k = 0` it is the 2 × 2 minor of rows `{0,i}` and columns
`{0,j}`. -/
noncomputable def bMinor2 {N : ℕ} (M : Matrix (Fin N) (Fin N) R) (k i j : Fin N) : R :=
  (!![M k k, M k j; M i k, M i j]).det

/-- The bordered 3 × 3 **minor** `det [[a_kk, a_kl, a_kj], [a_lk, a_ll, a_lj],
[a_ik, a_il, a_ij]]`, i.e. the entry produced by the step at pivot `(l,l)` when
the previous pivot is the corresponding 2 × 2 minor. -/
noncomputable def bMinor3 {N : ℕ} (M : Matrix (Fin N) (Fin N) R) (k l i j : Fin N) : R :=
  (!![M k k, M k l, M k j; M l k, M l l, M l j; M i k, M i l, M i j]).det

/-- The **numerator** of the Bareiss step at pivot `(k,k)`:
`a_kk a_ij - a_ik a_kj`.

This is the whole algebraic content of a fraction-free step; the step divides it
by the *previous* pivot `a_{k-1,k-1}` (by `1` for `k = 0`). -/
def bStepNum {N : ℕ} (M : Matrix (Fin N) (Fin N) R) (k i j : Fin N) : R :=
  M k k * M i j - M i k * M k j

/-- One **Bareiss step**, the previous pivot `d` left as a parameter:
`a_ij ↦ (a_kk a_ij - a_ik a_kj) / d`.

`bStepNum` and `bStep` are kept separate because *exactness* (the divisibility of
`bStepNum` by `d`) is a statement about the numerator alone, and is what the
theorems below establish; `bStep` is only meaningful once that is proved. -/
def bStep {N : ℕ} [Div R] (M : Matrix (Fin N) (Fin N) R) (d : R) (k i j : Fin N) : R :=
  bStepNum M k i j / d

/-! ## 2.  Step 0: the numerator is the 2 × 2 bordered minor -/

/-- **Step 0 of Bareiss is the 2 × 2 bordered minor**, in every dimension and
for all `i j`.  No hypothesis whatsoever: both sides are the 2 × 2
determinant `a00 a_ij - a_i0 a_0j`.  This is the `k = 0` instance of the minor
identity and the base of its induction. -/
theorem bStepNum_zero_eq_minor2 {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i j : Fin (N + 1)) : bStepNum M 0 i j = bMinor2 M 0 i j := by
  simp [bStepNum, bMinor2, Matrix.det_fin_two]
  ring

/-- **The 2 × 2 case.**  For a 2 × 2 integer matrix the whole algorithm is one
step, with divisor `a_{-1,-1} = 1`; the result at `(1,1)` is `det M`. -/
theorem bareiss_two_two (M : Matrix (Fin 2) (Fin 2) ℤ) :
    bStep M 1 0 1 1 = M.det := by
  simp [bStep, bStepNum, Matrix.det_fin_two]
  ring

/-- **The 2 × 2 exact-division lemma.**  The numerator of the (unique) step of
the 2 × 2 algorithm is divisible by the previous pivot, which is `1`.

Deliberately vacuous: it records that the 2 × 2 case needs no hypothesis at
all, and that the first non-vacuous exactness statement is
`bareiss_step_one_dvd` below. -/
theorem bareiss_two_dvd (M : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2) :
    (1 : ℤ) ∣ bStepNum M 0 i j :=
  one_dvd _

/-- The 3 × 3 bordered minor with `k = 0`, `l = 1`, `i = j = 2` is `det A`. -/
theorem bMinor3_last (A : Matrix (Fin 3) (Fin 3) R) : bMinor3 A 0 1 2 2 = A.det := by
  simp [bMinor3, Matrix.det_fin_three]

/-! ## 3.  Step 1: Sylvester / Desnanot–Jacobi in bordered form -/

/-- **Sylvester's identity, bordered form.**  In every dimension and for all
`i j`,

`a11^(1) * a_ij^(1) - a_i1^(1) * a_1j^(1) = a00 * det A[{0,1,i},{0,1,j}]`,

where `a_uv^(1) = det A[{k,u},{k,v}] = bMinor2 M k u v` is what step 0 produced.

Equivalently: the numerator of the step at pivot `(1,1)` is `a00` times the
3 × 3 bordered minor, so dividing by `a00` — which is exactly what the
algorithm does, `a00` preceding `a11^(1)` in the pivot sequence — leaves that
3 × 3 minor.  No injectivity of the indices is assumed; for `i, j ≤ 1` both
sides degenerate consistently. -/
theorem sylvester_two {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i j : Fin (N + 1)) :
    bMinor2 M 0 1 1 * bMinor2 M 0 i j - bMinor2 M 0 i 1 * bMinor2 M 0 1 j =
      M 0 0 * bMinor3 M 0 1 i j := by
  simp [bMinor2, bMinor3, Matrix.det_fin_two, Matrix.det_fin_three]
  ring

/-- **The 3 × 3 minor identity** in the `Fin 3` spelling used by the appendix:
for `b_uv = a00 a_uv - a_u0 a_0v`, `b11 b22 - b21 b12 = a00 * det A`. -/
theorem sylvester_three (A : Matrix (Fin 3) (Fin 3) R) :
    bMinor2 A 0 1 1 * bMinor2 A 0 2 2 - bMinor2 A 0 2 1 * bMinor2 A 0 1 2 =
      A 0 0 * A.det := by
  simp [bMinor2, Matrix.det_fin_two, Matrix.det_fin_three]
  ring

/-- **Exact division at step 1.**  The step-1 numerator is divisible by `a00`,
with the 3 × 3 bordered minor as explicit witness. -/
theorem bareiss_step_one_dvd {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ)
    (i j : Fin (N + 1)) :
    M 0 0 ∣ bMinor2 M 0 1 1 * bMinor2 M 0 i j - bMinor2 M 0 i 1 * bMinor2 M 0 1 j :=
  ⟨_, sylvester_two M i j⟩

/-- **The exact-division lemma at step 1**, quotient form: for `a00 ≠ 0` the
quotient is the 3 × 3 bordered minor, i.e. the tableau entry after the second
step *is* the minor.  This is where the hypothesis `Δ1 = a00 ≠ 0` enters. -/
theorem bareiss_step_one_exact {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ)
    (i j : Fin (N + 1)) (h : M 0 0 ≠ 0) :
    (bMinor2 M 0 1 1 * bMinor2 M 0 i j - bMinor2 M 0 i 1 * bMinor2 M 0 1 j) / M 0 0 =
      bMinor3 M 0 1 i j := by
  rw [sylvester_two M i j, Int.mul_ediv_cancel_left _ h]

/-- **The 3 × 3 algorithm is correct.**  For a 3 × 3 integer matrix with
`a00 ≠ 0`, the last entry produced by the two Bareiss steps is `det A`. -/
theorem bareiss_three_two_two (A : Matrix (Fin 3) (Fin 3) ℤ) (h : A 0 0 ≠ 0) :
    (bMinor2 A 0 1 1 * bMinor2 A 0 2 2 - bMinor2 A 0 2 1 * bMinor2 A 0 1 2) / A 0 0 =
      A.det := by
  rw [sylvester_three, Int.mul_ediv_cancel_left _ h]

/-! ## 4.  The Claim 21 bit-length bound for minors -/

/-- **A minor has ω·b + bitLen ω! bits.**  If every entry of `M` satisfies
`|M i j| < 2^b`, then every ω × ω minor does too, and
`bitLenInt (bMinor M r c) ≤ ω * b + bitLenInt ω!`.

Immediate from `bitLenInt_det_le` applied to the submatrix. -/
theorem bitLenInt_bMinor_le {N : ℕ} (M : Matrix (Fin N) (Fin N) ℤ) {ω : ℕ}
    (r c : Fin ω → Fin N) {b : ℕ} (hM : ∀ i j, |M i j| < (2 : ℤ) ^ b) :
    bitLenInt (bMinor M r c) ≤ ω * b + bitLenInt (ω.factorial) := by
  simpa [bMinor] using
    bitLenInt_det_le (M.submatrix r c) (fun i j => hM (r i) (c j))

/-- `Nat.size` is subadditive for powers: `(a ^ k).size ≤ k * a.size + 1`.
(The `+ 1` is needed at `k = 0`, where `a ^ 0 = 1` still costs one bit.) -/
theorem nat_size_pow_le (a k : ℕ) : (a ^ k).size ≤ k * a.size + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.pow_succ]
      calc (a ^ k * a).size ≤ (a ^ k).size + a.size := nat_size_mul_le _ _
        _ ≤ k * a.size + 1 + a.size := Nat.add_le_add_right ih _
        _ = (k + 1) * a.size + 1 := by ring

/-- **`bitLenInt n! ≤ n * bitLenInt n + 1`.**  From `n! ≤ n^n` and the power
bound above: this is the `log2(n!)` term of Claim 21, bounded by
`n * log2 n + 1`. -/
theorem bitLenInt_factorial_le (n : ℕ) : bitLenInt (n.factorial : ℤ) ≤ n * n.size + 1 := by
  rw [bitLenInt_natCast]
  calc (n.factorial).size ≤ (n ^ n).size := Nat.size_le_size (Nat.factorial_le_pow n)
    _ ≤ n * n.size + 1 := nat_size_pow_le n n

/-- Monotonicity of `bitLenInt` for factorials. -/
theorem bitLenInt_factorial_mono {m n : ℕ} (h : m ≤ n) :
    bitLenInt (m.factorial : ℤ) ≤ bitLenInt (n.factorial : ℤ) := by
  rw [bitLenInt_natCast, bitLenInt_natCast]
  exact Nat.size_le_size (Nat.factorial_le h)

/-- **Claim 21 for every intermediate entry.**  If `ω ≤ N` and every entry of the
N × N integer matrix `M` satisfies `|M i j| < 2^b`, then every ω × ω minor of
`M` — in particular every entry of the Bareiss tableau, which is such a minor —
has at most `N * b + bitLenInt N!` bits. -/
theorem bitLenInt_bMinor_le_factorial {N : ℕ} (M : Matrix (Fin N) (Fin N) ℤ) {ω : ℕ}
    (r c : Fin ω → Fin N) {b : ℕ} (hM : ∀ i j, |M i j| < (2 : ℤ) ^ b) (hω : ω ≤ N) :
    bitLenInt (bMinor M r c) ≤ N * b + bitLenInt (N.factorial) := by
  refine le_trans (bitLenInt_bMinor_le M r c hM) ?_
  have h1 : ω * b ≤ N * b := Nat.mul_le_mul_right b hω
  have h2 := bitLenInt_factorial_mono hω
  omega

/-- **The closed form `N·b + N·log2 N + 1`.**  Every intermediate entry of Bareiss
on an N × N integer system with `|M i j| < 2^b` has at most
`N * b + N * N.size + 1` bits. -/
theorem bitLenInt_bMinor_le_size {N : ℕ} (M : Matrix (Fin N) (Fin N) ℤ) {ω : ℕ}
    (r c : Fin ω → Fin N) {b : ℕ} (hM : ∀ i j, |M i j| < (2 : ℤ) ^ b) (hω : ω ≤ N) :
    bitLenInt (bMinor M r c) ≤ N * b + N * N.size + 1 := by
  refine le_trans (bitLenInt_bMinor_le_factorial M r c hM hω) ?_
  have h := bitLenInt_factorial_le N
  omega

end Q1Paper.PaperI
