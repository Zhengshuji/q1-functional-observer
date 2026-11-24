import Q1Paper.PaperI.RationalBasis

/-!
Q1Paper/PaperI/BitLenMatMul.lean

Scratch module: **submultiplicativity (and additivity) of `bitLenMat`**, the missing
composition lemma for the single-parameter bit bounds of Paper I.

Motivation.  `BitLen.lean` bounds the *entries* of the cleared matrix `A.num`
(`bitLenInt (A.num i j) ≤ A.den.size + bitLenRat (A i j)`, `bitLenInt_det_num_le_bitLenMat`,
…), and `InputLen.lean` compares `bitLenMat A` with `inputLen A`, but there is no way to
bound `bitLenMat (M * N)`: such a bound is what every chained estimate
(`L0 * (A * P)`, `fromRows (C * A) C`, …) needs.  This file supplies it.

Main results (all for rational matrices, no `sorry`, no `admit`, no new axioms):

* `bitLenMat_mul_le` : `bitLenMat (M * N) ≤ bitLenMat M + bitLenMat N + n.size + 1` for
  `M : Matrix (Fin m) (Fin n) ℚ`, `N : Matrix (Fin n) (Fin k) ℚ` (general form
  `bitLenMatAny_mul_le`, arbitrary finite inner index type).  Compare with the naive
  `bitLenMat M + bitLenMat N`: the extra `n.size + 1` is the `log` of the number of
  summands in an entry of the product, and it cannot be removed — for the `1 × 4` and
  `4 × 1` matrices of ones the product is the single entry `4`, whose bit length is `3`,
  while both factors have bit length `1` (so the naive bound `1 + 1` is false:
  `bitLenRat_one_add_one_lt_four`).  Nothing here needs `n ≤ 2 ^ n.size` beyond `+ 1`.

* `bitLenMatAny_fromRows_le` : `bitLenMat [A; B] ≤ bitLenMat A + bitLenMat B`.  The `max`
  form is **false**: `Matrix.den` is the `lcm` of the entry denominators, so stacking
  `[1/2]` and `[1/3]` gives common denominator `6` (bit length `3`) although both blocks
  have bit length `2` (see the discussion after the theorem).

* `bitLenMat_submatrix_le`, `bitLenMat_transpose_le` (an equality in substance), the
  negation `bitLenMat_neg`, the scalar bound `bitLenMat_smul_le`, the additive bound
  `bitLenMat_add_le` and the `map`-bound `bitLenMat_map_intCast(_le)`.

* `bitLenMat_chain_le`, `bitLenMat_chain_inputLen_le`, `bitLenMatAny_rowStacked_le`:
  the composed forms the two paper claims actually need.

The proofs all go through one interface, `bitLenMatAny_le_of_dominated`: to bound
`bitLenMat B` by `b` it suffices to have `B.den.size ≤ b` and, entrywise, an *integer*
`z` with `z.natAbs < 2 ^ b` and `(B.num i j).natAbs ≤ z.natAbs`.  The integer `z` is
produced from the parent matrix/matrices by clearing denominators —
`z = ∑ l, M.num i l * N.num l j` for a product, `z = A.num (r i) (c j)` for a submatrix,
`z = c.num * A.num i j` for a scalar multiple — and the dominance of `(B.num i j).natAbs`
by `z.natAbs` is the elementary fact that `B.num i j * c = z` for a positive integer `c`
(`natAbs_num_le_of_den_dvd`, `natAbs_num_le_mul_den_of_den_le`,
`rat_num_natAbs_le_of_den_dvd`).

Check with `lake env lean Q1Paper/PaperI/BitLenMatMul.lean`.
-/


open Matrix

namespace Q1Paper.PaperI

/-! ## 0.  `bitLenMat` for an arbitrary finite index type

`bitLenMat` is defined for `Fin`-shaped matrices only.  `Matrix.fromRows` produces the
index type `α ⊕ β`, so we need the same quantity for arbitrary finite index types; it is
*definitionally* the same function, so nothing is lost. -/

/-- Bit length of a rational matrix, for an arbitrary finite index type: the maximum of
the bit size of the common denominator and of the bit lengths of the cleared entries. -/
def bitLenMatAny {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℚ) : ℕ :=
  max A.den.size (Finset.univ.sup (fun p : m × n => bitLenInt (A.num p.1 p.2)))

/-- On `Fin`-shaped matrices `bitLenMatAny` *is* `bitLenMat` (definitionally). -/
theorem bitLenMatAny_eq_bitLenMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    bitLenMatAny A = bitLenMat A := rfl

theorem mat_den_size_le_bitLenMatAny {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) : A.den.size ≤ bitLenMatAny A :=
  le_max_left _ _

theorem mat_bitLenInt_num_le_bitLenMatAny {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) (i : m) (j : n) : bitLenInt (A.num i j) ≤ bitLenMatAny A :=
  le_trans
    (Finset.le_sup (f := fun p : m × n => bitLenInt (A.num p.1 p.2)) (Finset.mem_univ (i, j)))
    (le_max_right _ _)

/-- Every cleared entry is below `2 ^ bitLenMatAny A` in absolute value. -/
theorem mat_natAbs_num_lt_two_pow_bitLenMatAny {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) (i : m) (j : n) : (A.num i j).natAbs < 2 ^ bitLenMatAny A :=
  lt_of_lt_of_le (bitLenInt_natAbs_lt (A.num i j))
    (Nat.pow_le_pow_right (by decide : 0 < 2) (mat_bitLenInt_num_le_bitLenMatAny A i j))

/-- `n.size ≤ n`: a bit count can be absorbed into a polynomial budget. -/
theorem nat_size_le_self (n : ℕ) : n.size ≤ n :=
  Nat.size_le.mpr Nat.lt_two_pow_self

/-! ## 1.  Arithmetic helpers -/

/-- If `a * c = z` with `c > 0`, then `a.natAbs ≤ z.natAbs` (turns the exact clearing
identity `B.num i j * c = z` into the dominance needed by the master lemma). -/
theorem int_natAbs_le_of_mul_natCast {a z : ℤ} {c : ℕ} (hc : 0 < c) (h : a * (c : ℤ) = z) :
    a.natAbs ≤ z.natAbs := by
  have h2 : a.natAbs * c = z.natAbs := by
    have := congr_arg Int.natAbs h
    simpa [Int.natAbs_mul] using this
  calc a.natAbs = a.natAbs * 1 := (Nat.mul_one _).symm
    _ ≤ a.natAbs * c := Nat.mul_le_mul_left _ hc
    _ = z.natAbs := h2

/-- The denominator of a sum divides `D` as soon as both denominators do. -/
theorem rat_den_add_dvd {q₁ q₂ : ℚ} {D : ℕ} (h₁ : q₁.den ∣ D) (h₂ : q₂.den ∣ D) :
    (q₁ + q₂).den ∣ D :=
  (Rat.add_den_dvd_lcm q₁ q₂).trans (Nat.lcm_dvd h₁ h₂)

/-- The denominator of a finite sum divides `D` as soon as all summand denominators do. -/
theorem rat_den_sum_dvd {ι : Type*} (s : Finset ι) (f : ι → ℚ) {D : ℕ}
    (h : ∀ i ∈ s, (f i).den ∣ D) : (s.sum f).den ∣ D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact rat_den_add_dvd (h a (Finset.mem_insert_self a t))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **Clearing denominators.**  If `B i j = Z / D` with `Z` an integer and `D` a positive
integer divisible by `B.den`, then the cleared entry `B.num i j` is dominated by `Z`:
`(B.num i j).natAbs ≤ Z.natAbs`. -/
theorem mat_num_natAbs_le_of_den_dvd {m n : Type*} [Fintype m] [Fintype n]
    (B : Matrix m n ℚ) (i : m) (j : n) {D : ℕ} {Z : ℤ} (hD : 0 < D) (hdvd : B.den ∣ D)
    (hx : B i j = (Z : ℚ) / (D : ℚ)) : (B.num i j).natAbs ≤ Z.natAbs := by
  classical
  set c : ℕ := D / B.den with hc
  have hBpos : 0 < B.den := mat_den_pos B
  have hcpos : 0 < c := Nat.div_pos (Nat.le_of_dvd hD hdvd) hBpos
  have hdmul : B.den * c = D := by
    rw [hc, Nat.mul_comm]
    exact Nat.div_mul_cancel hdvd
  have hdc : (B.den : ℚ) * (c : ℚ) = (D : ℚ) := by
    have h : ((B.den * c : ℕ) : ℚ) = (D : ℚ) := by rw [hdmul]
    simpa using h
  have hDne : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hkey : ((B.num i j * (c : ℤ) : ℤ) : ℚ) = ((Z : ℤ) : ℚ) := by
    have h1 : ((B.num i j : ℤ) : ℚ) = (B.den : ℚ) * B i j := mat_num_eq_den_mul B i j
    push_cast
    calc (B.num i j : ℚ) * (c : ℚ) = ((B.den : ℚ) * B i j) * (c : ℚ) := by rw [h1]
      _ = ((B.den : ℚ) * (c : ℚ)) * B i j := by ring
      _ = (D : ℚ) * B i j := by rw [hdc]
      _ = (D : ℚ) * ((Z : ℚ) / (D : ℚ)) := by rw [hx]
      _ = (Z : ℚ) := by field_simp
  exact int_natAbs_le_of_mul_natCast hcpos (Int.cast_injective hkey)

/-- **Clearing denominators, entry-replacement form.**  If `B i j = A i' j'` and
`B.den ≤ A.den * D`, then `(B.num i j).natAbs ≤ (A.num i' j').natAbs * D`. -/
theorem natAbs_num_le_mul_den_of_den_le {m n m' n' : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n'] (B : Matrix m n ℚ) (A : Matrix m' n' ℚ) {D : ℕ}
    (hle : B.den ≤ A.den * D) (i : m) (j : n) (i' : m') (j' : n') (h : B i j = A i' j') :
    (B.num i j).natAbs ≤ (A.num i' j').natAbs * D := by
  have hA : 0 < A.den := mat_den_pos A
  have hkey : ((B.num i j : ℤ) : ℚ) * (A.den : ℚ) = ((A.num i' j' : ℤ) : ℚ) * (B.den : ℚ) := by
    rw [mat_num_eq_den_mul B i j, mat_num_eq_den_mul A i' j', h]
    ring
  have hkeyInt : B.num i j * (A.den : ℤ) = A.num i' j' * (B.den : ℤ) := by
    refine Int.cast_injective (α := ℚ) ?_
    push_cast
    exact hkey
  have hnat : (B.num i j).natAbs * A.den = (A.num i' j').natAbs * B.den := by
    have := congr_arg Int.natAbs hkeyInt
    simpa [Int.natAbs_mul] using this
  have h1 : (B.num i j).natAbs * A.den ≤ ((A.num i' j').natAbs * D) * A.den := by
    calc (B.num i j).natAbs * A.den = (A.num i' j').natAbs * B.den := hnat
      _ ≤ (A.num i' j').natAbs * (A.den * D) := Nat.mul_le_mul_left _ hle
      _ = ((A.num i' j').natAbs * D) * A.den := by ring
  exact Nat.le_of_mul_le_mul_right h1 hA

/-- If every summand of `s` is `< P`, then the sum is `< (s.card + 1) * P`
(no nonemptiness hypothesis: the empty sum is `0 < P`). -/
theorem finset_sum_lt_card_add_one_mul {ι : Type*} (s : Finset ι) (f : ι → ℕ) {P : ℕ}
    (hP : 0 < P) (h : ∀ i ∈ s, f i < P) : s.sum f < (s.card + 1) * P := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hP
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have h1 : f a < P := h a (Finset.mem_insert_self a t)
      have h2 : t.sum f < (t.card + 1) * P :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      calc f a + t.sum f < P + (t.card + 1) * P := Nat.add_lt_add h1 h2
        _ = (t.card + 1 + 1) * P := by ring

/-- **Master lemma.**  To bound `bitLenMatAny B` by `b` it suffices that the common
denominator has at most `b` bits and that every cleared entry is dominated (in
`natAbs`) by an integer of at most `b` bits. -/
theorem bitLenMatAny_le_of_dominated {m n : Type*} [Fintype m] [Fintype n]
    (B : Matrix m n ℚ) {b : ℕ} (hden : B.den.size ≤ b)
    (hnum : ∀ i j, ∃ z : ℤ, z.natAbs < 2 ^ b ∧ (B.num i j).natAbs ≤ z.natAbs) :
    bitLenMatAny B ≤ b := by
  refine max_le hden ?_
  refine Finset.sup_le (fun p _ => ?_)
  obtain ⟨i, j⟩ := p
  obtain ⟨z, hz, hle⟩ := hnum i j
  calc bitLenInt (B.num i j) = (B.num i j).natAbs.size := rfl
    _ ≤ z.natAbs.size := Nat.size_le_size hle
    _ = bitLenInt z := rfl
    _ ≤ b := bitLenInt_le_iff.mpr hz

/-! ## 2.  Submultiplicativity of `bitLenMat` -/

/-- **`bitLenMat` of a product** (general finite inner index type): the bit length of a
product of two rational matrices is at most the sum of the bit lengths plus the number of
bits of the inner dimension (plus one bookkeeping bit).

Indeed `(M * N).den ∣ M.den * N.den`, and `(M * N).num i j` is dominated by the integer
`∑ l, M.num i l * N.num l j`, which is smaller than
`(card β + 1) * 2 ^ (bitLenMatAny M + bitLenMatAny N)`. -/
theorem bitLenMatAny_mul_le {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (M : Matrix α β ℚ) (N : Matrix β γ ℚ) :
    bitLenMatAny (M * N) ≤ bitLenMatAny M + bitLenMatAny N + (Fintype.card β + 1).size := by
  classical
  have hDpos : 0 < M.den * N.den := Nat.mul_pos (mat_den_pos M) (mat_den_pos N)
  have hdvd : (M * N).den ∣ M.den * N.den := by
    rw [Matrix.den_dvd_iff]
    intro i j
    rw [Matrix.mul_apply]
    refine rat_den_sum_dvd _ _ (fun l _ => ?_)
    exact (Rat.mul_den_dvd (M i l) (N l j)).trans
      (Nat.mul_dvd_mul (mat_den_dvd M i l) (mat_den_dvd N l j))
  -- (1) the common denominator
  have hden : (M * N).den.size ≤ bitLenMatAny M + bitLenMatAny N + (Fintype.card β + 1).size := by
    have h1 : (M * N).den.size ≤ (M.den * N.den).size :=
      Nat.size_le_size (Nat.le_of_dvd hDpos hdvd)
    have h2 : (M.den * N.den).size ≤ M.den.size + N.den.size := nat_size_mul_le _ _
    have h3 : M.den.size + N.den.size ≤ bitLenMatAny M + bitLenMatAny N :=
      Nat.add_le_add (mat_den_size_le_bitLenMatAny M) (mat_den_size_le_bitLenMatAny N)
    omega
  refine bitLenMatAny_le_of_dominated _ hden (fun i j => ?_)
  -- (2) the cleared entries are dominated by `∑ l, M.num i l * N.num l j`
  refine ⟨∑ l : β, M.num i l * N.num l j, ?_, ?_⟩
  · -- magnitude of the dominating integer
    set P : ℕ := 2 ^ (bitLenMatAny M + bitLenMatAny N) with hPdef
    have hPpos : 0 < P := pow_pos (by decide : (0 : ℕ) < 2) _
    have hterm : ∀ l : β, (M.num i l * N.num l j).natAbs < P := by
      intro l
      rw [Int.natAbs_mul, hPdef]
      calc (M.num i l).natAbs * (N.num l j).natAbs
          < 2 ^ bitLenMatAny M * 2 ^ bitLenMatAny N :=
            Nat.mul_lt_mul_of_le_of_lt
              (le_of_lt (mat_natAbs_num_lt_two_pow_bitLenMatAny M i l))
              (mat_natAbs_num_lt_two_pow_bitLenMatAny N l j)
              (pow_pos (by decide : (0 : ℕ) < 2) _)
        _ = 2 ^ (bitLenMatAny M + bitLenMatAny N) := (Nat.pow_add _ _ _).symm
    have hsum : (∑ l : β, (M.num i l * N.num l j).natAbs) < (Fintype.card β + 1) * P := by
      have h := finset_sum_lt_card_add_one_mul (Finset.univ : Finset β)
        (fun l => (M.num i l * N.num l j).natAbs) hPpos (fun l _ => hterm l)
      rwa [Finset.card_univ] at h
    have hmul_le : (Fintype.card β + 1) * P ≤ 2 ^ ((Fintype.card β + 1).size) * P :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.lt_size_self (Fintype.card β + 1)))
    have hexp : (Fintype.card β + 1).size + (bitLenMatAny M + bitLenMatAny N)
        = bitLenMatAny M + bitLenMatAny N + (Fintype.card β + 1).size := by omega
    calc (∑ l : β, M.num i l * N.num l j).natAbs
        ≤ ∑ l : β, (M.num i l * N.num l j).natAbs := Int.natAbs_sum_le _ _
      _ < (Fintype.card β + 1) * P := hsum
      _ ≤ 2 ^ ((Fintype.card β + 1).size) * P := hmul_le
      _ = 2 ^ ((Fintype.card β + 1).size) * 2 ^ (bitLenMatAny M + bitLenMatAny N) := by
            rw [hPdef]
      _ = 2 ^ ((Fintype.card β + 1).size + (bitLenMatAny M + bitLenMatAny N)) :=
            (Nat.pow_add _ _ _).symm
      _ = 2 ^ (bitLenMatAny M + bitLenMatAny N + (Fintype.card β + 1).size) := by rw [hexp]
  · -- clearing the denominator of the `(i,j)` entry
    have hx : (M * N) i j
        = ((∑ l : β, M.num i l * N.num l j : ℤ) : ℚ) / ((M.den * N.den : ℕ) : ℚ) := by
      rw [Matrix.mul_apply]
      calc (∑ l : β, M i l * N l j : ℚ)
          = ∑ l : β, ((M.num i l : ℚ) / (M.den : ℚ)) * ((N.num l j : ℚ) / (N.den : ℚ)) := by
            refine Finset.sum_congr rfl (fun l _ => ?_)
            rw [← Matrix.num_div_den M i l, ← Matrix.num_div_den N l j]
        _ = ∑ l : β, (((M.num i l * N.num l j : ℤ) : ℚ)) / ((M.den * N.den : ℕ) : ℚ) := by
            refine Finset.sum_congr rfl (fun l _ => ?_)
            rw [div_mul_div_comm]
            push_cast
            ring
        _ = ((∑ l : β, M.num i l * N.num l j : ℤ) : ℚ) / ((M.den * N.den : ℕ) : ℚ) := by
            rw [← Finset.sum_div]
            push_cast
            ring
    exact mat_num_natAbs_le_of_den_dvd (M * N) i j hDpos hdvd hx

/-- **`bitLenMat` of a product** (the `Fin`-indexed form): with inner dimension `n`,
`bitLenMat (M * N) ≤ bitLenMat M + bitLenMat N + n.size + 1`.

Compare with the naive `bitLenMat M + bitLenMat N`: the bound is bigger only by
`n.size + 1 ≤ n + 1`, the `log` of the number of summands in an entry of the product, and
that term cannot be dropped (`bitLenRat_one_add_one_lt_four` and the discussion there). -/
theorem bitLenMat_mul_le {m n k : ℕ} (M : Matrix (Fin m) (Fin n) ℚ)
    (N : Matrix (Fin n) (Fin k) ℚ) :
    bitLenMat (M * N) ≤ bitLenMat M + bitLenMat N + n.size + 1 := by
  have h := bitLenMatAny_mul_le M N
  rw [Fintype.card_fin] at h
  have hcard : (n + 1).size ≤ n.size + 1 := by
    rw [Nat.size_le]
    calc n + 1 ≤ 2 ^ n.size := Nat.succ_le_of_lt (Nat.lt_size_self n)
      _ < 2 ^ (n.size + 1) := Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self _)
  have h' : bitLenMatAny (M * N) ≤ bitLenMatAny M + bitLenMatAny N + n.size + 1 := by omega
  simpa [bitLenMatAny_eq_bitLenMat] using h'

/-- The arithmetic core of the failure of the naive bound `bitLenMat M + bitLenMat N`:
the single number `4` needs `bitLenRat 4 = 3` bits, more than the two bits of
`bitLenRat 1 + bitLenRat 1`.  Reading this at matrix level: for the `1 × 4` and `4 × 1`
matrices of ones, `M * N = (4)`, `bitLenMat (M * N) = 3`, while `bitLenMat M =
bitLenMat N = 1`, so the naive bound `1 + 1` is false; the `n.size` (= `3` for `n = 4`)
term of `bitLenMat_mul_le` is exactly what accounts for it. -/
theorem bitLenRat_one_add_one_lt_four :
    bitLenRat (1 : ℚ) + bitLenRat (1 : ℚ) < bitLenRat (4 : ℚ) := by
  decide

/-! ## 3.  `bitLenMat` of `submatrix`, `transpose`, `fromRows`, `neg`, `smul`, `+`, `map` -/

/-- **Submatrix.**  Selecting rows and columns cannot increase the bit length. -/
theorem bitLenMatAny_submatrix_le {α β α' β' : Type*} [Fintype α] [Fintype β]
    [Fintype α'] [Fintype β'] (A : Matrix α β ℚ) (r : α' → α) (c : β' → β) :
    bitLenMatAny (A.submatrix r c) ≤ bitLenMatAny A := by
  have hdvd : (A.submatrix r c).den ∣ A.den := by
    rw [Matrix.den_dvd_iff]
    intro i j
    rw [Matrix.submatrix_apply]
    exact mat_den_dvd A (r i) (c j)
  have hle : (A.submatrix r c).den ≤ A.den := Nat.le_of_dvd (mat_den_pos A) hdvd
  have hden : (A.submatrix r c).den.size ≤ bitLenMatAny A :=
    (Nat.size_le_size hle).trans (mat_den_size_le_bitLenMatAny A)
  refine bitLenMatAny_le_of_dominated _ hden (fun i j => ?_)
  refine ⟨A.num (r i) (c j), mat_natAbs_num_lt_two_pow_bitLenMatAny A (r i) (c j), ?_⟩
  have h := natAbs_num_le_mul_den_of_den_le (D := 1) (A.submatrix r c) A
    (by simpa using hle) i j (r i) (c j) (Matrix.submatrix_apply A r c i j)
  simpa using h

/-- **Submatrix** (`Fin` form). -/
theorem bitLenMat_submatrix_le {m n m' k' : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (r : Fin m' → Fin m) (c : Fin k' → Fin n) :
    bitLenMat (A.submatrix r c) ≤ bitLenMat A := by
  have h := bitLenMatAny_submatrix_le A r c
  rwa [bitLenMatAny_eq_bitLenMat, bitLenMatAny_eq_bitLenMat] at h

/-- **Transpose.**  Transposition does not change the bit length at all. -/
theorem bitLenMatAny_transpose_le {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℚ) : bitLenMatAny Aᵀ ≤ bitLenMatAny A := by
  have hden : Aᵀ.den.size ≤ bitLenMatAny A := by
    rw [Matrix.den_transpose]
    exact mat_den_size_le_bitLenMatAny A
  refine bitLenMatAny_le_of_dominated _ hden (fun i j => ?_)
  refine ⟨A.num j i, mat_natAbs_num_lt_two_pow_bitLenMatAny A j i, ?_⟩
  rw [Matrix.num_transpose]
  exact le_of_eq (by simp)

/-- **Transpose** (`Fin` form). -/
theorem bitLenMat_transpose_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    bitLenMat Aᵀ ≤ bitLenMat A := by
  have h := bitLenMatAny_transpose_le A
  rwa [bitLenMatAny_eq_bitLenMat, bitLenMatAny_eq_bitLenMat] at h

/-- **`fromRows`.**  Stacking two blocks (sharing the columns) adds the bit lengths.

The `max` form is **false**, because `Matrix.den` is the `lcm` of the entry denominators:
`bitLenMat [1/2; 1/3] = 3` (common denominator `6`) while both `1 × 1` blocks have bit
length `2` (`den = 2`, resp. `den = 3`, and numerator `1`).  Numerically:
`bitLenRat (1/2) = 2 = bitLenRat (1/3)` but the two denominators have `lcm 6` of bit
length `3`.  Hence the sum, not the maximum, is the correct bound. -/
theorem bitLenMatAny_fromRows_le {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (A : Matrix α γ ℚ) (B : Matrix β γ ℚ) :
    bitLenMatAny (Matrix.fromRows A B) ≤ bitLenMatAny A + bitLenMatAny B := by
  classical
  have hDpos : 0 < A.den * B.den := Nat.mul_pos (mat_den_pos A) (mat_den_pos B)
  have hdvd : (Matrix.fromRows A B).den ∣ A.den * B.den := by
    rw [Matrix.den_dvd_iff]
    rintro (i | i) j
    · rw [Matrix.fromRows_apply_inl]
      exact (mat_den_dvd A i j).trans (Nat.dvd_mul_right _ _)
    · rw [Matrix.fromRows_apply_inr]
      exact (mat_den_dvd B i j).trans (Nat.dvd_mul_left _ _)
  have hle : (Matrix.fromRows A B).den ≤ A.den * B.den := Nat.le_of_dvd hDpos hdvd
  have hden : (Matrix.fromRows A B).den.size ≤ bitLenMatAny A + bitLenMatAny B := by
    have h2 : (A.den * B.den).size ≤ A.den.size + B.den.size := nat_size_mul_le _ _
    have h3 : A.den.size + B.den.size ≤ bitLenMatAny A + bitLenMatAny B :=
      Nat.add_le_add (mat_den_size_le_bitLenMatAny A) (mat_den_size_le_bitLenMatAny B)
    exact (Nat.size_le_size hle).trans (h2.trans h3)
  refine bitLenMatAny_le_of_dominated _ hden (fun i j => ?_)
  rcases i with i | i
  · have happ : (Matrix.fromRows A B) (Sum.inl i) j = A i j := Matrix.fromRows_apply_inl A B i j
    refine ⟨A.num i j * (B.den : ℤ), ?_, ?_⟩
    · rw [Int.natAbs_mul, Int.natAbs_natCast]
      have h1 := mat_natAbs_num_lt_two_pow_bitLenMatAny A i j
      have h2 : B.den < 2 ^ bitLenMatAny B :=
        lt_of_lt_of_le (Nat.lt_size_self B.den)
          (Nat.pow_le_pow_right (by decide : 0 < 2) (mat_den_size_le_bitLenMatAny B))
      calc (A.num i j).natAbs * B.den
          < 2 ^ bitLenMatAny A * 2 ^ bitLenMatAny B :=
            Nat.mul_lt_mul_of_le_of_lt (le_of_lt h1) h2
              (pow_pos (by decide : (0 : ℕ) < 2) _)
        _ = 2 ^ (bitLenMatAny A + bitLenMatAny B) := (Nat.pow_add _ _ _).symm
    · have := natAbs_num_le_mul_den_of_den_le (Matrix.fromRows A B) A hle (Sum.inl i) j i j happ
      simpa [Int.natAbs_mul] using this
  · have happ : (Matrix.fromRows A B) (Sum.inr i) j = B i j := Matrix.fromRows_apply_inr A B i j
    refine ⟨B.num i j * (A.den : ℤ), ?_, ?_⟩
    · rw [Int.natAbs_mul, Int.natAbs_natCast]
      have h1 := mat_natAbs_num_lt_two_pow_bitLenMatAny B i j
      have h2 : A.den < 2 ^ bitLenMatAny A :=
        lt_of_lt_of_le (Nat.lt_size_self A.den)
          (Nat.pow_le_pow_right (by decide : 0 < 2) (mat_den_size_le_bitLenMatAny A))
      calc (B.num i j).natAbs * A.den
          < 2 ^ bitLenMatAny B * 2 ^ bitLenMatAny A :=
            Nat.mul_lt_mul_of_le_of_lt (le_of_lt h1) h2
              (pow_pos (by decide : (0 : ℕ) < 2) _)
        _ = 2 ^ (bitLenMatAny B + bitLenMatAny A) := (Nat.pow_add _ _ _).symm
        _ = 2 ^ (bitLenMatAny A + bitLenMatAny B) := by rw [Nat.add_comm]
    · have hle' : (Matrix.fromRows A B).den ≤ B.den * A.den := by rw [Nat.mul_comm]; exact hle
      have := natAbs_num_le_mul_den_of_den_le (Matrix.fromRows A B) B hle' (Sum.inr i) j i j happ
      simpa [Int.natAbs_mul] using this

/-- **Negation is compatible with the bit length** (`|−z| = |z|`). -/
theorem bitLenMatAny_neg_le {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℚ) :
    bitLenMatAny (-A) ≤ bitLenMatAny A := by
  have hden : (-A).den.size ≤ bitLenMatAny A := by
    rw [Matrix.den_neg]
    exact mat_den_size_le_bitLenMatAny A
  refine bitLenMatAny_le_of_dominated _ hden (fun i j => ?_)
  refine ⟨-(A.num i j), ?_, ?_⟩
  · rw [Int.natAbs_neg]
    exact mat_natAbs_num_lt_two_pow_bitLenMatAny A i j
  · simp

/-- **Negation** preserves the bit length. -/
theorem bitLenMat_neg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    bitLenMat (-A) = bitLenMat A := by
  have h1 : bitLenMatAny (-A) ≤ bitLenMatAny A := bitLenMatAny_neg_le A
  have h2 : bitLenMatAny A ≤ bitLenMatAny (-A) := by
    have := bitLenMatAny_neg_le (-A)
    rwa [neg_neg] at this
  have h3 : bitLenMatAny (-A) = bitLenMatAny A := le_antisymm h1 h2
  simpa [bitLenMatAny_eq_bitLenMat] using h3

/-- **Scalar multiples**: `bitLenMat (c • A) ≤ bitLenMat A + bitLenRat c`. -/
theorem bitLenMatAny_smul_le {α β : Type*} [Fintype α] [Fintype β]
    (c : ℚ) (A : Matrix α β ℚ) :
    bitLenMatAny (c • A) ≤ bitLenMatAny A + bitLenRat c := by
  have hDpos : 0 < c.den * A.den := Nat.mul_pos (Rat.den_pos c) (mat_den_pos A)
  have hdvd : (c • A).den ∣ c.den * A.den := by
    rw [Matrix.den_dvd_iff]
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (Rat.mul_den_dvd c (A i j)).trans
      (Nat.mul_dvd_mul (dvd_refl c.den) (mat_den_dvd A i j))
  have hle : (c • A).den ≤ c.den * A.den := Nat.le_of_dvd hDpos hdvd
  have hden : (c • A).den.size ≤ bitLenMatAny A + bitLenRat c := by
    have h2 : (c.den * A.den).size ≤ c.den.size + A.den.size := nat_size_mul_le _ _
    have h3 : c.den.size + A.den.size ≤ bitLenRat c + bitLenMatAny A :=
      Nat.add_le_add (nat_size_den_le_bitLenRat c) (mat_den_size_le_bitLenMatAny A)
    calc (c • A).den.size ≤ (c.den * A.den).size := Nat.size_le_size hle
      _ ≤ c.den.size + A.den.size := h2
      _ ≤ bitLenRat c + bitLenMatAny A := h3
      _ = bitLenMatAny A + bitLenRat c := Nat.add_comm _ _
  refine bitLenMatAny_le_of_dominated _ hden (fun i j => ?_)
  have hx : (c • A) i j = ((c.num * A.num i j : ℤ) : ℚ) / ((c.den * A.den : ℕ) : ℚ) := by
    rw [Matrix.smul_apply, smul_eq_mul]
    conv_lhs => rw [← Rat.num_div_den c]
    conv_lhs => rw [← Matrix.num_div_den A i j]
    rw [div_mul_div_comm]
    push_cast
    ring
  refine ⟨c.num * A.num i j, ?_, mat_num_natAbs_le_of_den_dvd (c • A) i j hDpos hdvd hx⟩
  rw [Int.natAbs_mul]
  have h1 : (c.num).natAbs < 2 ^ bitLenRat c :=
    lt_of_lt_of_le (bitLenInt_natAbs_lt c.num)
      (Nat.pow_le_pow_right (by decide : 0 < 2) (bitLenInt_num_le_bitLenRat c))
  have h2 := mat_natAbs_num_lt_two_pow_bitLenMatAny A i j
  calc (c.num).natAbs * (A.num i j).natAbs
      < 2 ^ bitLenRat c * 2 ^ bitLenMatAny A :=
        Nat.mul_lt_mul_of_le_of_lt (le_of_lt h1) h2
          (pow_pos (by decide : (0 : ℕ) < 2) _)
    _ = 2 ^ (bitLenRat c + bitLenMatAny A) := (Nat.pow_add _ _ _).symm
    _ = 2 ^ (bitLenMatAny A + bitLenRat c) := by rw [Nat.add_comm]

/-- **Scalar multiples** (`Fin` form). -/
theorem bitLenMat_smul_le {m n : ℕ} (c : ℚ) (A : Matrix (Fin m) (Fin n) ℚ) :
    bitLenMat (c • A) ≤ bitLenMat A + bitLenRat c := by
  have h := bitLenMatAny_smul_le c A
  rwa [bitLenMatAny_eq_bitLenMat, bitLenMatAny_eq_bitLenMat] at h

/-- **Sums**: `bitLenMat (A + B) ≤ bitLenMat A + bitLenMat B + 1` (one carry bit). -/
theorem bitLenMatAny_add_le {α β : Type*} [Fintype α] [Fintype β]
    (A B : Matrix α β ℚ) :
    bitLenMatAny (A + B) ≤ bitLenMatAny A + bitLenMatAny B + 1 := by
  have hDpos : 0 < A.den * B.den := Nat.mul_pos (mat_den_pos A) (mat_den_pos B)
  have hdvd : (A + B).den ∣ A.den * B.den := by
    rw [Matrix.den_dvd_iff]
    intro i j
    rw [Matrix.add_apply]
    exact rat_den_add_dvd ((mat_den_dvd A i j).trans (Nat.dvd_mul_right _ _))
      ((mat_den_dvd B i j).trans (Nat.dvd_mul_left _ _))
  have hden : (A + B).den.size ≤ bitLenMatAny A + bitLenMatAny B + 1 := by
    have h1 : (A + B).den.size ≤ (A.den * B.den).size :=
      Nat.size_le_size (Nat.le_of_dvd hDpos hdvd)
    have h2 : (A.den * B.den).size ≤ A.den.size + B.den.size := nat_size_mul_le _ _
    have h3 : A.den.size + B.den.size ≤ bitLenMatAny A + bitLenMatAny B :=
      Nat.add_le_add (mat_den_size_le_bitLenMatAny A) (mat_den_size_le_bitLenMatAny B)
    omega
  refine bitLenMatAny_le_of_dominated _ hden (fun i j => ?_)
  have hx : (A + B) i j
      = ((A.num i j * (B.den : ℤ) + B.num i j * (A.den : ℤ) : ℤ) : ℚ)
        / ((A.den * B.den : ℕ) : ℚ) := by
    have hA : (A.den : ℚ) ≠ 0 := by exact_mod_cast (mat_den_pos A).ne'
    have hB : (B.den : ℚ) ≠ 0 := by exact_mod_cast (mat_den_pos B).ne'
    rw [Matrix.add_apply, ← Matrix.num_div_den A i j, ← Matrix.num_div_den B i j,
      div_add_div _ _ hA hB]
    push_cast
    ring
  refine ⟨A.num i j * (B.den : ℤ) + B.num i j * (A.den : ℤ), ?_,
    mat_num_natAbs_le_of_den_dvd (A + B) i j hDpos hdvd hx⟩
  have h1 : (A.num i j * (B.den : ℤ)).natAbs < 2 ^ (bitLenMatAny A + bitLenMatAny B) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    calc (A.num i j).natAbs * B.den
        < 2 ^ bitLenMatAny A * 2 ^ bitLenMatAny B :=
          Nat.mul_lt_mul_of_le_of_lt
            (le_of_lt (mat_natAbs_num_lt_two_pow_bitLenMatAny A i j))
            (lt_of_lt_of_le (Nat.lt_size_self B.den)
              (Nat.pow_le_pow_right (by decide : 0 < 2) (mat_den_size_le_bitLenMatAny B)))
            (pow_pos (by decide : (0 : ℕ) < 2) _)
      _ = 2 ^ (bitLenMatAny A + bitLenMatAny B) := (Nat.pow_add _ _ _).symm
  have h2 : (B.num i j * (A.den : ℤ)).natAbs < 2 ^ (bitLenMatAny A + bitLenMatAny B) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    calc (B.num i j).natAbs * A.den
        < 2 ^ bitLenMatAny B * 2 ^ bitLenMatAny A :=
          Nat.mul_lt_mul_of_le_of_lt
            (le_of_lt (mat_natAbs_num_lt_two_pow_bitLenMatAny B i j))
            (lt_of_lt_of_le (Nat.lt_size_self A.den)
              (Nat.pow_le_pow_right (by decide : 0 < 2) (mat_den_size_le_bitLenMatAny A)))
            (pow_pos (by decide : (0 : ℕ) < 2) _)
      _ = 2 ^ (bitLenMatAny B + bitLenMatAny A) := (Nat.pow_add _ _ _).symm
      _ = 2 ^ (bitLenMatAny A + bitLenMatAny B) := by rw [Nat.add_comm]
  calc (A.num i j * (B.den : ℤ) + B.num i j * (A.den : ℤ)).natAbs
      ≤ (A.num i j * (B.den : ℤ)).natAbs + (B.num i j * (A.den : ℤ)).natAbs :=
        Int.natAbs_add_le _ _
    _ < 2 ^ (bitLenMatAny A + bitLenMatAny B) + 2 ^ (bitLenMatAny A + bitLenMatAny B) :=
        Nat.add_lt_add h1 h2
    _ = 2 ^ (bitLenMatAny A + bitLenMatAny B + 1) := by
        rw [Nat.pow_succ]
        ring

/-- **Sums** (`Fin` form). -/
theorem bitLenMat_add_le {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) :
    bitLenMat (A + B) ≤ bitLenMat A + bitLenMat B + 1 := by
  have h := bitLenMatAny_add_le A B
  rw [bitLenMatAny_eq_bitLenMat, bitLenMatAny_eq_bitLenMat,
    bitLenMatAny_eq_bitLenMat] at h
  exact h

/-- **`map` along `ℤ → ℚ`.**  For an integer matrix the common denominator is `1` and the
cleared matrix is the matrix itself, so the bit length is the maximum of `1` and the entry
bit lengths. -/
theorem bitLenMat_map_intCast {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    bitLenMat (A.map (Int.cast : ℤ → ℚ))
      = max 1 (Finset.univ.sup (fun p : Fin m × Fin n => bitLenInt (A p.1 p.2))) := by
  rw [bitLenMat, Matrix.den_map_intCast, Matrix.num_map_intCast]
  simp

/-- **`map` along `ℤ → ℚ`**, entrywise form. -/
theorem bitLenMat_map_intCast_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) {b : ℕ}
    (hb : ∀ i j, bitLenInt (A i j) ≤ b) :
    bitLenMat (A.map (Int.cast : ℤ → ℚ)) ≤ max 1 b := by
  rw [bitLenMat_map_intCast]
  exact max_le (le_max_left _ _)
    ((Finset.sup_le (fun p _ => hb p.1 p.2)).trans (le_max_right _ _))

/-! ## 4.  The composed bounds the two paper claims need -/

/-- **The product chain `L0 * (A * P)`.**  Two applications of `bitLenMat_mul_le`; both
inner dimensions are `n`.  (`P` is `n × m` and `L0` is `r0 × n` so that `A * P` and
`L0 * (A * P)` are well typed; with `P : Matrix (Fin m) (Fin n)` the expression
`A * P` only typechecks when `m = n`.) -/
theorem bitLenMat_chain_le {m n r0 : ℕ} (P : Matrix (Fin n) (Fin m) ℚ)
    (A : Matrix (Fin n) (Fin n) ℚ) (L0 : Matrix (Fin r0) (Fin n) ℚ) :
    bitLenMat (L0 * (A * P)) ≤ bitLenMat L0 + bitLenMat A + bitLenMat P
      + 2 * (n.size + 1) := by
  have h1 : bitLenMat (A * P) ≤ bitLenMat A + bitLenMat P + n.size + 1 := bitLenMat_mul_le A P
  have h2 : bitLenMat (L0 * (A * P))
      ≤ bitLenMat L0 + bitLenMat (A * P) + n.size + 1 := bitLenMat_mul_le L0 (A * P)
  omega

/-- **The product chain, in terms of `inputLen`.**  This is the form in which the paper's
single-parameter bounds compose: the shapes are non-empty (`0 < n + m`, `0 < n`,
`0 < r0`), so `bitLenMat ≤ inputLen` for each factor. -/
theorem bitLenMat_chain_inputLen_le {m n r0 : ℕ} (P : Matrix (Fin n) (Fin m) ℚ)
    (A : Matrix (Fin n) (Fin n) ℚ) (L0 : Matrix (Fin r0) (Fin n) ℚ)
    (hnm : 0 < n + m) (hn : 0 < n) (hr0 : 0 < r0) :
    bitLenMat (L0 * (A * P))
      ≤ inputLen L0 + inputLen A + inputLen P + 2 * (n.size + 1) := by
  have h := bitLenMat_chain_le P A L0
  have hA : bitLenMat A ≤ inputLen A := bitLenMat_le_inputLen A (by omega)
  have hP : bitLenMat P ≤ inputLen P := bitLenMat_le_inputLen P hnm
  have hL : bitLenMat L0 ≤ inputLen L0 := bitLenMat_le_inputLen L0 (by omega)
  omega

/-- **The row-stacked chain `L0 * ([C * A; C] * P)`**: this is the matrix `row(L0 M)` of
the paper, with `M = fromRows (C * A) C`.  It combines `bitLenMatAny_fromRows_le` with two
applications of `bitLenMatAny_mul_le`; the row index of the stack is `Fin p ⊕ Fin p`, of
cardinality `p + p`, and `(p + p + 1).size ≤ p + p + 1`. -/
theorem bitLenMatAny_rowStacked_le {ρ : Type*} [Fintype ρ] {m n p : ℕ}
    (C : Matrix (Fin p) (Fin n) ℚ) (A : Matrix (Fin n) (Fin n) ℚ)
    (P : Matrix (Fin n) (Fin m) ℚ) (L0 : Matrix ρ (Fin p ⊕ Fin p) ℚ) :
    bitLenMatAny (L0 * (Matrix.fromRows (C * A) C * P))
      ≤ bitLenMatAny L0 + bitLenMatAny P + 2 * bitLenMat C + bitLenMat A
        + 2 * (n + 1) + (2 * p + 1) := by
  have hCA : bitLenMat (C * A) ≤ bitLenMat C + bitLenMat A + n.size + 1 := bitLenMat_mul_le C A
  have hFR : bitLenMatAny (Matrix.fromRows (C * A) C) ≤ bitLenMatAny (C * A) + bitLenMatAny C :=
    bitLenMatAny_fromRows_le (C * A) C
  rw [bitLenMatAny_eq_bitLenMat, bitLenMatAny_eq_bitLenMat] at hFR
  have hFR' : bitLenMatAny (Matrix.fromRows (C * A) C)
      ≤ bitLenMat C + bitLenMat A + n.size + 1 + bitLenMat C := by omega
  have h2 : bitLenMatAny (Matrix.fromRows (C * A) C * P)
      ≤ bitLenMatAny (Matrix.fromRows (C * A) C) + bitLenMatAny P
        + (Fintype.card (Fin n) + 1).size :=
    bitLenMatAny_mul_le (Matrix.fromRows (C * A) C) P
  rw [Fintype.card_fin] at h2
  have h3 : bitLenMatAny (L0 * (Matrix.fromRows (C * A) C * P))
      ≤ bitLenMatAny L0 + bitLenMatAny (Matrix.fromRows (C * A) C * P)
        + (Fintype.card (Fin p ⊕ Fin p) + 1).size :=
    bitLenMatAny_mul_le L0 (Matrix.fromRows (C * A) C * P)
  have hcard : Fintype.card (Fin p ⊕ Fin p) = p + p := by simp
  rw [hcard] at h3
  have hs2 : (n + 1).size ≤ n + 1 := nat_size_le_self (n + 1)
  have hs3 : n.size + 1 ≤ n + 1 := by
    have := nat_size_le_self n
    omega
  have hs4 : (p + p + 1).size ≤ 2 * p + 1 := by
    have := nat_size_le_self (p + p + 1)
    omega
  omega

end Q1Paper.PaperI

