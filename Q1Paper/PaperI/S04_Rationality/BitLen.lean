
import Mathlib

/-!
Q1Paper/PaperI/S04_Rationality/BitLen.lean

Bit-length foundation for Claim 13.

Contents:
* `bitLenInt` : scalar bit length of an integer, with the convention `bitLenInt 0 = 0`;
* magnitude bound `|z| < 2 ^ bitLenInt z`, a multiplicative subadditivity
  `bitLenInt (z₁ * z₂) ≤ bitLenInt z₁ + bitLenInt z₂`, and the additive bound
  `bitLenInt (z₁ + z₂) ≤ 1 + max (bitLenInt z₁) (bitLenInt z₂)`
  (the constant `1` is sharp, see `bitLenInt_add_sharp`);
* `bitLenRat` : input bit length of a rational, `max (bitLenInt q.num) q.den.size`,
  with positivity, the zero value, the magnitude bound `|q| < 2 ^ bitLenRat q`, and
  multiplicative growth `bitLenRat (q₁ * q₂) ≤ bitLenRat q₁ + bitLenRat q₂`;
* for a rational matrix `A`, the exact consequence of `Matrix.num_div_den`,
  the entry bound `|A.num i j| = A.den * |A i j|` for the cleared matrix, and the
  bit-length estimate `bitLenInt (A.num i j) ≤ A.den.size + bitLenRat (A i j)`;
* `bitLenMat` : bit length of a rational matrix, bounding every entry of `A.num`.

Self-contained: a single `import Mathlib`, no `sorry`, no new axioms.  Check with
`lake env lean Q1Paper/PaperI/BitLen.lean`.
-/


open Matrix

namespace Q1Paper.PaperI

/-! ## 1.  Bit length of an integer -/

/-- Scalar bit length of an integer: the number of binary digits of `|z|`, i.e.
`(Int.natAbs z).size`.

**Convention.** `bitLenInt 0 = 0` (the empty binary expansion); for `z ≠ 0`,
`bitLenInt z` is the unique `b ≥ 1` with `2 ^ (b - 1) ≤ |z| < 2 ^ b`. -/
def bitLenInt (z : ℤ) : ℕ := z.natAbs.size

@[simp] theorem bitLenInt_zero : bitLenInt 0 = 0 := by simp [bitLenInt]

theorem bitLenInt_eq_zero {z : ℤ} : bitLenInt z = 0 ↔ z = 0 := by
  rw [bitLenInt, Nat.size_eq_zero, Int.natAbs_eq_zero]

theorem bitLenInt_pos {z : ℤ} (hz : z ≠ 0) : 0 < bitLenInt z := by
  rcases Nat.eq_zero_or_pos (bitLenInt z) with h | h
  · exact absurd (bitLenInt_eq_zero.mp h) hz
  · exact h

/-- Characterisation of the integer bit length: `bitLenInt z ≤ n ↔ |z| < 2 ^ n`. -/
theorem bitLenInt_le_iff {z : ℤ} {n : ℕ} : bitLenInt z ≤ n ↔ z.natAbs < 2 ^ n :=
  Nat.size_le

theorem bitLenInt_natAbs_lt (z : ℤ) : z.natAbs < 2 ^ bitLenInt z :=
  Nat.lt_size_self z.natAbs

/-- The defining magnitude bound: `|z| < 2 ^ bitLenInt z`. -/
theorem bitLenInt_abs_lt (z : ℤ) : |z| < (2 : ℤ) ^ bitLenInt z := by
  calc |z| = ((z.natAbs : ℕ) : ℤ) := (Int.natCast_natAbs z).symm
    _ < ((2 ^ z.natAbs.size : ℕ) : ℤ) := by exact_mod_cast bitLenInt_natAbs_lt z
    _ = (2 : ℤ) ^ z.natAbs.size := by push_cast; ring

theorem bitLenInt_neg (z : ℤ) : bitLenInt (-z) = bitLenInt z := by
  simp only [bitLenInt, Int.natAbs_neg]

/-- Auxiliary: `Nat.size` is subadditive for multiplication. -/
theorem nat_size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  rw [Nat.size_le]
  calc a * b < 2 ^ a.size * 2 ^ b.size :=
        Nat.mul_lt_mul_of_le_of_lt (le_of_lt (Nat.lt_size_self a)) (Nat.lt_size_self b)
          (by positivity)
    _ = 2 ^ (a.size + b.size) := (Nat.pow_add 2 a.size b.size).symm

/-- Auxiliary: `Nat.size` is subadditive for addition, with one extra bit. -/
theorem nat_size_add_le (a b : ℕ) : (a + b).size ≤ 1 + max a.size b.size := by
  rw [Nat.size_le]
  have ha : a < 2 ^ max a.size b.size :=
    lt_of_lt_of_le (Nat.lt_size_self a)
      (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_left a.size b.size))
  have hb : b < 2 ^ max a.size b.size :=
    lt_of_lt_of_le (Nat.lt_size_self b)
      (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right a.size b.size))
  calc a + b < 2 ^ max a.size b.size + 2 ^ max a.size b.size := Nat.add_lt_add ha hb
    _ = 2 ^ (1 + max a.size b.size) := by rw [Nat.pow_add, Nat.pow_one]; ring

/-- `Nat.size` is monotone with respect to divisibility. -/
theorem nat_size_le_size_of_dvd {a b : ℕ} (hb : 0 < b) (h : a ∣ b) : a.size ≤ b.size :=
  Nat.size_le_size (Nat.le_of_dvd hb h)

/-- Multiplicative subadditivity of the integer bit length. -/
theorem bitLenInt_mul (z₁ z₂ : ℤ) :
    bitLenInt (z₁ * z₂) ≤ bitLenInt z₁ + bitLenInt z₂ := by
  rw [bitLenInt, Int.natAbs_mul]
  exact nat_size_mul_le _ _

/-- Additive bound for the integer bit length: one extra bit suffices. -/
theorem bitLenInt_add (z₁ z₂ : ℤ) :
    bitLenInt (z₁ + z₂) ≤ 1 + max (bitLenInt z₁) (bitLenInt z₂) := by
  have h := Int.natAbs_add_le z₁ z₂
  calc bitLenInt (z₁ + z₂) = ((z₁ + z₂).natAbs).size := rfl
    _ ≤ (z₁.natAbs + z₂.natAbs).size := Nat.size_le_size h
    _ ≤ 1 + max z₁.natAbs.size z₂.natAbs.size := nat_size_add_le _ _
    _ = 1 + max (bitLenInt z₁) (bitLenInt z₂) := rfl

theorem bitLenInt_sub (z₁ z₂ : ℤ) :
    bitLenInt (z₁ - z₂) ≤ 1 + max (bitLenInt z₁) (bitLenInt z₂) := by
  simpa [sub_eq_add_neg, bitLenInt_neg] using bitLenInt_add z₁ (-z₂)

/-- The constant `1` in `bitLenInt_add` cannot be lowered: `7 + 7 = 14` needs
`1 + max 3 3 = 4` bits, while `3` bits only reach `7`. -/
theorem bitLenInt_add_sharp :
    bitLenInt ((2 : ℤ) ^ 3 - 1 + ((2 : ℤ) ^ 3 - 1)) =
      1 + max (bitLenInt ((2 : ℤ) ^ 3 - 1)) (bitLenInt ((2 : ℤ) ^ 3 - 1)) := by
  decide

/-! ## 2.  Bit length of a rational -/

/-- Input bit length of a rational `q`: the maximum of the bit length of the
numerator and the bit size of the denominator.

**Convention.** `bitLenRat 0 = 1` (the denominator `1` contributes one bit). -/
def bitLenRat (q : ℚ) : ℕ := max (bitLenInt q.num) q.den.size

theorem bitLenInt_num_le_bitLenRat (q : ℚ) : bitLenInt q.num ≤ bitLenRat q :=
  le_max_left _ _

theorem nat_size_den_le_bitLenRat (q : ℚ) : q.den.size ≤ bitLenRat q :=
  le_max_right _ _

/-- The rational bit length is always positive (`q.den ≠ 0`). -/
theorem bitLenRat_pos (q : ℚ) : 0 < bitLenRat q :=
  lt_of_lt_of_le (Nat.size_pos.mpr q.den_pos) (nat_size_den_le_bitLenRat q)

theorem bitLenRat_ne_zero (q : ℚ) : bitLenRat q ≠ 0 := (bitLenRat_pos q).ne'

theorem bitLenRat_zero : bitLenRat 0 = 1 := by decide

/-- Bridge between the integer absolute value and its `natAbs`, over `ℚ`. -/
theorem int_natAbs_cast_abs (z : ℤ) : ((z.natAbs : ℕ) : ℚ) = |(z : ℚ)| := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]

/-- Magnitude bound for the rational bit length: `|q| < 2 ^ bitLenRat q`. -/
theorem bitLenRat_abs_lt (q : ℚ) : |q| < (2 : ℚ) ^ bitLenRat q := by
  -- numerator part
  have hnum : |(q.num : ℚ)| < (2 : ℚ) ^ bitLenRat q := by
    have hcast : |(q.num : ℚ)| = ((q.num.natAbs : ℕ) : ℚ) :=
      (int_natAbs_cast_abs q.num).symm
    rw [hcast]
    have h1 : ((q.num.natAbs : ℕ) : ℚ) < (2 : ℚ) ^ bitLenInt q.num := by
      have h : q.num.natAbs < 2 ^ (q.num.natAbs).size := Nat.lt_size_self _
      have h' : ((q.num.natAbs : ℕ) : ℚ) < ((2 ^ (q.num.natAbs).size : ℕ) : ℚ) := by
        exact_mod_cast h
      simpa [bitLenInt, Nat.cast_pow] using h'
    refine lt_of_lt_of_le h1 ?_
    have hmono : 2 ^ bitLenInt q.num ≤ 2 ^ bitLenRat q :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (bitLenInt_num_le_bitLenRat q)
    calc (2 : ℚ) ^ bitLenInt q.num = ((2 ^ bitLenInt q.num : ℕ) : ℚ) := by push_cast; ring
      _ ≤ ((2 ^ bitLenRat q : ℕ) : ℚ) := by exact_mod_cast hmono
      _ = (2 : ℚ) ^ bitLenRat q := by push_cast; ring
  -- combine with `q * q.den = q.num`
  have hden : (1 : ℚ) ≤ (q.den : ℚ) := by
    have h : (1 : ℕ) ≤ q.den := q.den_pos
    exact_mod_cast h
  have hmul : q * (q.den : ℚ) = (q.num : ℚ) := Rat.mul_den_eq_num q
  have habs : |(q.num : ℚ)| = |q| * (q.den : ℚ) := by
    calc |(q.num : ℚ)| = |q * (q.den : ℚ)| := by rw [hmul]
      _ = |q| * |(q.den : ℚ)| := abs_mul q _
      _ = |q| * (q.den : ℚ) := by
            rw [abs_of_nonneg (Nat.cast_nonneg (α := ℚ) q.den)]
  have hle : |q| ≤ |q| * (q.den : ℚ) := by
    have h := mul_le_mul_of_nonneg_left hden (abs_nonneg q)
    simpa using h
  linarith [habs, hnum, hle]

/-- A reduced numerator of a product is `q₁.num * q₂.num` up to a positive integer
factor: reduction can only cancel common factors against the denominator. -/
theorem rat_mul_num_eq_mul (q₁ q₂ : ℚ) :
    ∃ T : ℕ, 0 < T ∧ (q₁ * q₂).num * (T : ℤ) = q₁.num * q₂.num := by
  obtain ⟨T, hT⟩ := Rat.mul_den_dvd q₁ q₂
  have hTpos : 0 < T := by
    rcases Nat.eq_zero_or_pos T with h | h
    · rw [h, Nat.mul_zero] at hT
      exact absurd hT (Nat.ne_of_gt (Nat.mul_pos q₁.den_pos q₂.den_pos))
    · exact h
  -- the "cleared" identity for a product, over `ℚ` and then over `ℤ`
  have hcast : (((q₁ * q₂).num * ((q₁.den * q₂.den : ℕ) : ℤ) : ℤ) : ℚ)
      = (((q₁.num * q₂.num) * ((q₁ * q₂).den : ℤ) : ℤ) : ℚ) := by
    push_cast
    rw [← Rat.mul_den_eq_num (q₁ * q₂), ← Rat.mul_den_eq_num q₁, ← Rat.mul_den_eq_num q₂]
    ring
  have hclear : (q₁ * q₂).num * ((q₁.den * q₂.den : ℕ) : ℤ)
      = (q₁.num * q₂.num) * ((q₁ * q₂).den : ℤ) :=
    Int.cast_injective hcast
  -- replace the denominator product by `(q₁ * q₂).den * T`
  have hDT : ((q₁.den * q₂.den : ℕ) : ℤ) = ((q₁ * q₂).den : ℤ) * (T : ℤ) := by
    rw [hT]; push_cast; ring
  have hX : ((q₁ * q₂).num * (T : ℤ)) * ((q₁ * q₂).den : ℤ)
      = (q₁.num * q₂.num) * ((q₁ * q₂).den : ℤ) := by
    have h := hclear
    rw [hDT] at h
    calc ((q₁ * q₂).num * (T : ℤ)) * ((q₁ * q₂).den : ℤ)
        = (q₁ * q₂).num * (((q₁ * q₂).den : ℤ) * (T : ℤ)) := by ring
      _ = (q₁.num * q₂.num) * ((q₁ * q₂).den : ℤ) := h
  exact ⟨T, hTpos, mul_right_cancel₀ (by exact_mod_cast (q₁ * q₂).den_ne_zero) hX⟩

/-- The numerator of a product divides the product of the numerators. -/
theorem rat_mul_num_dvd (q₁ q₂ : ℚ) : (q₁ * q₂).num ∣ q₁.num * q₂.num := by
  obtain ⟨T, -, hT⟩ := rat_mul_num_eq_mul q₁ q₂
  exact ⟨(T : ℤ), hT.symm⟩

/-- Absolute-value form of the divisibility, directly usable for bit lengths. -/
theorem rat_mul_num_natAbs_le (q₁ q₂ : ℚ) :
    (q₁ * q₂).num.natAbs ≤ (q₁.num * q₂.num).natAbs := by
  obtain ⟨T, hTpos, hT⟩ := rat_mul_num_eq_mul q₁ q₂
  have hnat : (q₁ * q₂).num.natAbs * T = (q₁.num * q₂.num).natAbs := by
    have h := congr_arg Int.natAbs hT
    rw [Int.natAbs_mul] at h
    simpa using h
  calc (q₁ * q₂).num.natAbs = (q₁ * q₂).num.natAbs * 1 := (Nat.mul_one _).symm
    _ ≤ (q₁ * q₂).num.natAbs * T := Nat.mul_le_mul_left _ hTpos
    _ = (q₁.num * q₂.num).natAbs := hnat

/-- Multiplicative growth of the rational bit length: additivity up to no loss. -/
theorem bitLenRat_mul (q₁ q₂ : ℚ) :
    bitLenRat (q₁ * q₂) ≤ bitLenRat q₁ + bitLenRat q₂ := by
  show max (bitLenInt (q₁ * q₂).num) (q₁ * q₂).den.size ≤ bitLenRat q₁ + bitLenRat q₂
  refine max_le ?_ ?_
  · calc bitLenInt ((q₁ * q₂).num) = ((q₁ * q₂).num.natAbs).size := rfl
      _ ≤ ((q₁.num * q₂.num).natAbs).size := Nat.size_le_size (rat_mul_num_natAbs_le q₁ q₂)
      _ = bitLenInt (q₁.num * q₂.num) := rfl
      _ ≤ bitLenInt q₁.num + bitLenInt q₂.num := bitLenInt_mul q₁.num q₂.num
      _ ≤ bitLenRat q₁ + bitLenRat q₂ :=
          Nat.add_le_add (bitLenInt_num_le_bitLenRat q₁) (bitLenInt_num_le_bitLenRat q₂)
  · calc (q₁ * q₂).den.size ≤ (q₁.den * q₂.den).size :=
          nat_size_le_size_of_dvd (Nat.mul_pos q₁.den_pos q₂.den_pos) (Rat.mul_den_dvd q₁ q₂)
      _ ≤ q₁.den.size + q₂.den.size := nat_size_mul_le q₁.den q₂.den
      _ ≤ bitLenRat q₁ + bitLenRat q₂ :=
          Nat.add_le_add (nat_size_den_le_bitLenRat q₁) (nat_size_den_le_bitLenRat q₂)

/-! ## 3.  Entry bounds for the cleared matrix `A.num` -/

section MatrixBounds

variable {m n : Type*} [Fintype m] [Fintype n]

theorem mat_den_pos (A : Matrix m n ℚ) : 0 < A.den :=
  Nat.pos_of_ne_zero (Matrix.den_ne_zero A)

/-- Every entry denominator divides the matrix denominator. -/
theorem mat_den_dvd (A : Matrix m n ℚ) (i : m) (j : n) : (A i j).den ∣ A.den :=
  Matrix.den_dvd_iff.mp (dvd_refl A.den) i j

/-- The matrix denominator dominates every entry denominator in bit size. -/
theorem mat_den_size_entry_le (A : Matrix m n ℚ) (i : m) (j : n) :
    (A i j).den.size ≤ A.den.size :=
  nat_size_le_size_of_dvd (mat_den_pos A) (mat_den_dvd A i j)

/-- Exact form of `Matrix.num_div_den`: `A.num i j = A.den * A i j` in `ℚ`. -/
theorem mat_num_eq_den_mul (A : Matrix m n ℚ) (i : m) (j : n) :
    (A.num i j : ℚ) = (A.den : ℚ) * A i j := by
  have hden : (A.den : ℚ) ≠ 0 := by exact_mod_cast Matrix.den_ne_zero A
  calc (A.num i j : ℚ) = ((A.num i j : ℚ) / (A.den : ℚ)) * (A.den : ℚ) :=
        (div_mul_cancel₀ _ hden).symm
    _ = A i j * (A.den : ℚ) := by rw [Matrix.num_div_den A i j]
    _ = (A.den : ℚ) * A i j := mul_comm _ _

/-- Exact entry bound for the cleared matrix: `|A.num i j| = A.den * |A i j|`. -/
theorem mat_abs_num_eq (A : Matrix m n ℚ) (i : m) (j : n) :
    |(A.num i j : ℚ)| = (A.den : ℚ) * |A i j| := by
  rw [mat_num_eq_den_mul A i j, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg (α := ℚ) A.den)]

/-- The inequality form of the entry bound. -/
theorem mat_abs_num_le (A : Matrix m n ℚ) (i : m) (j : n) :
    |(A.num i j : ℚ)| ≤ (A.den : ℚ) * |A i j| :=
  (mat_abs_num_eq A i j).le

/-- Exact integer identity behind `Matrix.num_div_den`, in cleared (division-free)
form: `A.num i j * (A i j).den = A.den * (A i j).num`. -/
theorem mat_num_mul_den_eq (A : Matrix m n ℚ) (i : m) (j : n) :
    A.num i j * ((A i j).den : ℤ) = (A.den : ℤ) * (A i j).num := by
  have hcast : (((A.num i j * ((A i j).den : ℤ) : ℤ)) : ℚ) =
      ((((A.den : ℤ) * (A i j).num : ℤ)) : ℚ) := by
    push_cast
    rw [mat_num_eq_den_mul A i j]
    rw [← Rat.mul_den_eq_num (A i j)]
    ring
  exact Int.cast_injective hcast

/-- Divisibility form of the same identity:
`A.num i j = (A.den / (A i j).den) * (A i j).num`. -/
theorem mat_num_eq_div_den_mul_num (A : Matrix m n ℚ) (i : m) (j : n) :
    A.num i j = (A.den / (A i j).den : ℕ) * (A i j).num := by
  have hdvd : (A i j).den ∣ A.den := mat_den_dvd A i j
  have he : ((A i j).den : ℤ) ≠ 0 := by exact_mod_cast Rat.den_nz (A i j)
  have hdecomp : (A.den : ℤ) = ((A.den / (A i j).den : ℕ) : ℤ) * ((A i j).den : ℤ) := by
    have h : (A.den / (A i j).den : ℕ) * (A i j).den = A.den := Nat.div_mul_cancel hdvd
    exact_mod_cast h.symm
  have h' : A.num i j * ((A i j).den : ℤ) =
      (((A.den / (A i j).den : ℕ) : ℤ) * (A i j).num) * ((A i j).den : ℤ) := by
    rw [mat_num_mul_den_eq A i j, hdecomp]
    ring
  exact mul_right_cancel₀ he h'

theorem mat_den_le_two_pow (A : Matrix m n ℚ) : A.den ≤ 2 ^ A.den.size :=
  le_of_lt (Nat.lt_size_self A.den)

/-- The cleared matrix is integral: its denominator is `1`. -/
theorem mat_den_numMap (A : Matrix m n ℚ) :
    (A.num.map (fun z : ℤ => (z : ℚ))).den = 1 :=
  Matrix.den_map_intCast A.num

/-- Bit-length entry bound for the cleared matrix:
`bitLenInt (A.num i j) ≤ A.den.size + bitLenRat (A i j)`. -/
theorem mat_bitLenInt_num_le (A : Matrix m n ℚ) (i : m) (j : n) :
    bitLenInt (A.num i j) ≤ A.den.size + bitLenRat (A i j) := by
  rw [bitLenInt, Nat.size_le]
  have hcast : ((A.num i j).natAbs : ℚ) = |(A.num i j : ℚ)| := int_natAbs_cast_abs _
  have hlt : |(A.num i j : ℚ)| < (2 : ℚ) ^ (A.den.size + bitLenRat (A i j)) := by
    rw [mat_abs_num_eq]
    calc (A.den : ℚ) * |A i j| < (A.den : ℚ) * (2 : ℚ) ^ bitLenRat (A i j) :=
          mul_lt_mul_of_pos_left (bitLenRat_abs_lt (A i j)) (by exact_mod_cast mat_den_pos A)
      _ ≤ (2 : ℚ) ^ A.den.size * (2 : ℚ) ^ bitLenRat (A i j) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast mat_den_le_two_pow A) (by positivity)
      _ = (2 : ℚ) ^ (A.den.size + bitLenRat (A i j)) := (pow_add _ _ _).symm
  have hbridge : ((A.num i j).natAbs : ℚ) <
      ((2 ^ (A.den.size + bitLenRat (A i j)) : ℕ) : ℚ) := by
    rw [hcast]
    push_cast
    exact hlt
  exact Nat.cast_lt.mp hbridge

end MatrixBounds

/-! ## 4.  Bit length of a rational matrix -/

/-- Bit length of a rational matrix: the maximum of the bit size of the common
denominator and the bit lengths of the entries of the integer numerator. -/
def bitLenMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : ℕ :=
  max A.den.size (Finset.univ.sup (fun p : Fin m × Fin n => bitLenInt (A.num p.1 p.2)))

theorem mat_den_size_le_bitLenMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    A.den.size ≤ bitLenMat A :=
  le_max_left _ _

theorem mat_bitLenInt_num_le_bitLenMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (i : Fin m) (j : Fin n) : bitLenInt (A.num i j) ≤ bitLenMat A := by
  refine le_trans ?_ (le_max_right (A.den.size) _)
  exact Finset.le_sup (s := Finset.univ)
    (f := fun p : Fin m × Fin n => bitLenInt (A.num p.1 p.2)) (Finset.mem_univ (i, j))

/-- Every entry of the cleared matrix is bounded by `2 ^ bitLenMat A`. -/
theorem mat_abs_num_lt_two_pow_bitLenMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (i : Fin m) (j : Fin n) : |A.num i j| < (2 : ℤ) ^ bitLenMat A := by
  refine lt_of_lt_of_le (bitLenInt_abs_lt (A.num i j)) ?_
  have h : 2 ^ bitLenInt (A.num i j) ≤ 2 ^ bitLenMat A :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (mat_bitLenInt_num_le_bitLenMat A i j)
  calc (2 : ℤ) ^ bitLenInt (A.num i j) = ((2 ^ bitLenInt (A.num i j) : ℕ) : ℤ) := by
        push_cast; ring
    _ ≤ ((2 ^ bitLenMat A : ℕ) : ℤ) := by exact_mod_cast h
    _ = (2 : ℤ) ^ bitLenMat A := by push_cast; ring

/-- Combined statement: every entry of `A.num` is bounded in absolute value by
`2 ^ bitLenMat A`, and `A.den` has bit size at most `bitLenMat A`. -/
theorem mat_num_entries_bounded {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    (∀ i j, |A.num i j| < (2 : ℤ) ^ bitLenMat A) ∧ A.den.size ≤ bitLenMat A :=
  ⟨fun i j => mat_abs_num_lt_two_pow_bitLenMat A i j, mat_den_size_le_bitLenMat A⟩

end Q1Paper.PaperI
